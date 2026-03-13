// Lean compiler output
// Module: Lean.Elab.BuiltinDo.For
// Imports: public import Lean.Elab.BuiltinDo.Basic meta import Lean.Parser.Do import Init.Control.Do import Lean.Meta.ProdN
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
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Pi_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_mkMonadicType___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_continueWithUnit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSimpleThunk(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Meta_mkProdMkN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_mkPureApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray2___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDoSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_enterLoopBody___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_bindMutVarsFromTuple(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Meta_getLocalDeclFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Elab_Term_addTermInfo_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSome(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_mkBindApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkInstMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_mkPUnit___redArg(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Elab_Do_checkMutVarsForShadowing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_getReturnCont___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_Elab_Do_doElemElabAttribute;
static const lean_string_object l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__0 = (const lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__1 = (const lean_object*)&l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Std.toStream"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__3_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toStream"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__6_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(165, 78, 6, 120, 105, 250, 102, 183)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ToStream"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__8_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(131, 221, 81, 225, 58, 10, 156, 107)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(10, 224, 141, 229, 184, 244, 208, 180)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__10_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__11 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__11_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__12 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__12_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__14 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__14_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "__s"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__16 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__16_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(222, 33, 185, 180, 14, 135, 99, 223)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__18 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__18_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doLet"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__19 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__19_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "let"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__20 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__20_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mut"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__21 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__21_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__22 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__22_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letIdDecl"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "letId"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__24 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__24_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__26 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__26_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__27 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__27_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doMatch"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "matchDiscr"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Std.Stream.next\?"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__32;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Stream"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "next\?"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__34 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__34_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__35_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(131, 33, 225, 197, 4, 77, 215, 237)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__35_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(223, 69, 181, 194, 149, 37, 29, 54)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__35 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__35_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__35_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__37 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__37_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42_value),LEAN_SCALAR_PTR_LITERAL(73, 239, 30, 105, 8, 60, 178, 241)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__45 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__45_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__46_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42_value),LEAN_SCALAR_PTR_LITERAL(149, 114, 34, 228, 75, 195, 143, 131)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__46 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__46_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__46_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__48 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__48_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doBreak"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "break"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__51 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__51_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "some"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__52 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__52_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__52_value),LEAN_SCALAR_PTR_LITERAL(37, 202, 7, 33, 103, 74, 114, 212)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__55_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__52_value),LEAN_SCALAR_PTR_LITERAL(89, 148, 40, 55, 221, 242, 231, 67)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__55 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__55_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__55_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__57 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__57_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "tuple"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__58 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__58_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__59 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__59_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__60 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__60_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__61 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__61_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__61_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__62 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__62_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__63 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__63_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__64_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__64;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "s'"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__68 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__68_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__68_value),LEAN_SCALAR_PTR_LITERAL(203, 110, 194, 112, 150, 40, 11, 92)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__71 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__71_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doReassign"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__72 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__72_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "letIdDeclNoBinders"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__73 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__73_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doNested"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__74 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__74_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "The proof annotation here has not been implemented yet."};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doForDecl"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__3_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(149, 147, 251, 147, 43, 72, 7, 132)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doFor"};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__0 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 12, 178, 2, 144, 97, 71, 235)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__1 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "in"};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__2 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__74_value),LEAN_SCALAR_PTR_LITERAL(220, 154, 41, 109, 103, 76, 110, 63)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__3 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__27_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__4 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__5_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__5_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__5_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__5 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__5_value;
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "for"};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__6 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__6_value;
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__7 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__7_value;
static const lean_array_object l_Lean_Elab_Do_expandDoFor___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__8 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__8_value;
static const lean_array_object l_Lean_Elab_Do_expandDoFor___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__9 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__10_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__10_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__10_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__10 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__11_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__11_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__11_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(29, 50, 175, 23, 122, 111, 148, 60)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__11 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(99, 51, 127, 238, 206, 239, 57, 130)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__12 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__13 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__14 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__14_value;
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__15 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__15_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__16 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "expandDoFor"};
static const lean_object* l_Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 157, 21, 52, 135, 185, 36, 254)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__2___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unit"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__2___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__2___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__2___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(87, 186, 243, 194, 96, 12, 218, 7)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__2___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__2___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoFor___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoFor___lam__2___closed__3;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = " but the info said there is no early return"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__2___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__2___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoFor___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoFor___lam__2___closed__5;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Early returning "};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__2___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__2___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoFor___lam__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoFor___lam__2___closed__7;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "<not-available>"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__2___closed__8 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__2___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__2___closed__8_value)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__2___closed__9 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__2___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoFor___lam__2___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoFor___lam__2___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "done"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "yield"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__5___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__5___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ForInStep"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__8___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__8___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__8___closed__0_value),LEAN_SCALAR_PTR_LITERAL(153, 23, 255, 201, 194, 179, 65, 111)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__8___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__8___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "r"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__0_value),LEAN_SCALAR_PTR_LITERAL(201, 206, 29, 183, 206, 15, 98, 41)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(168, 60, 211, 188, 58, 220, 100, 184)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__2_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__10___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Break"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__10___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "runK"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__4_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__10___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "match_1"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___closed__5 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__10___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__3_value),LEAN_SCALAR_PTR_LITERAL(25, 204, 143, 3, 84, 67, 92, 151)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__10___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 178, 64, 100, 79, 118, 122, 28)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__10___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__5_value),LEAN_SCALAR_PTR_LITERAL(199, 194, 234, 57, 172, 104, 157, 179)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__6_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__10___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prod"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___closed__7 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__7_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__10___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fst"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___closed__8 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__10___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__7_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__10___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__8_value),LEAN_SCALAR_PTR_LITERAL(170, 44, 236, 58, 247, 164, 254, 114)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___closed__9 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__10(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__11(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Membership"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__12___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__12___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mem"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__12___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__12___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__12___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__12___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 217, 109, 94, 255, 55, 82, 109)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__12___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__12___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__12___closed__1_value),LEAN_SCALAR_PTR_LITERAL(224, 90, 126, 237, 128, 148, 153, 69)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__12___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__12___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__1;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__5_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__6_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__7___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ForIn"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 152, 230, 155, 97, 233, 45, 158)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "forIn"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 152, 230, 155, 97, 233, 45, 158)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__2_value),LEAN_SCALAR_PTR_LITERAL(9, 12, 142, 239, 44, 138, 10, 93)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__12___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 217, 109, 94, 255, 55, 82, 109)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__4_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "d"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__5 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 234, 148, 175, 115, 149, 2, 231)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__6_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ForIn'"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__7 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__7_value),LEAN_SCALAR_PTR_LITERAL(75, 251, 229, 162, 252, 35, 196, 120)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__8 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__8_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "forIn'"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__9 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__7_value),LEAN_SCALAR_PTR_LITERAL(75, 251, 229, 162, 252, 35, 196, 120)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__10_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__9_value),LEAN_SCALAR_PTR_LITERAL(10, 254, 232, 131, 195, 189, 138, 93)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__10 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__10_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Type mismatch. `for` loops have result type "};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__11 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__11_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoFor___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoFor___closed__12;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = ", but the rest of the `do` sequence expected "};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__13 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__13_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoFor___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoFor___closed__14;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__15 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__15_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoFor___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoFor___closed__16;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "α"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__17 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__17_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__17_value),LEAN_SCALAR_PTR_LITERAL(102, 24, 27, 80, 217, 159, 184, 13)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__18 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__18_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "ρ"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__19 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__19_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__19_value),LEAN_SCALAR_PTR_LITERAL(148, 87, 172, 24, 54, 35, 28, 246)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__20 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__20_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "__r"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__21 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__21_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__21_value),LEAN_SCALAR_PTR_LITERAL(38, 26, 183, 93, 43, 136, 227, 87)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__22 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__22_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "elabDoFor"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(41, 135, 12, 29, 130, 81, 226, 183)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1(lean_object* v___y_4_, lean_object* v___y_5_){
_start:
{
lean_object* v_macroScope_6_; lean_object* v_traceMsgs_7_; lean_object* v_expandedMacroDecls_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_21_; 
v_macroScope_6_ = lean_ctor_get(v___y_5_, 0);
v_traceMsgs_7_ = lean_ctor_get(v___y_5_, 1);
v_expandedMacroDecls_8_ = lean_ctor_get(v___y_5_, 2);
v_isSharedCheck_21_ = !lean_is_exclusive(v___y_5_);
if (v_isSharedCheck_21_ == 0)
{
v___x_10_ = v___y_5_;
v_isShared_11_ = v_isSharedCheck_21_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_expandedMacroDecls_8_);
lean_inc(v_traceMsgs_7_);
lean_inc(v_macroScope_6_);
lean_dec(v___y_5_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_21_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
lean_object* v_quotContext_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_17_; 
v_quotContext_12_ = lean_ctor_get(v___y_4_, 1);
lean_inc(v_quotContext_12_);
lean_dec_ref(v___y_4_);
v___x_13_ = ((lean_object*)(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__1));
v___x_14_ = lean_unsigned_to_nat(1u);
v___x_15_ = lean_nat_add(v_macroScope_6_, v___x_14_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 0, v___x_15_);
v___x_17_ = v___x_10_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v___x_15_);
lean_ctor_set(v_reuseFailAlloc_20_, 1, v_traceMsgs_7_);
lean_ctor_set(v_reuseFailAlloc_20_, 2, v_expandedMacroDecls_8_);
v___x_17_ = v_reuseFailAlloc_20_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = l_Lean_addMacroScope(v_quotContext_12_, v___x_13_, v_macroScope_6_);
v___x_19_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
lean_ctor_set(v___x_19_, 1, v___x_17_);
return v___x_19_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(lean_object* v_ref_22_, uint8_t v_canonical_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v___x_26_; lean_object* v_a_27_; lean_object* v_a_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_36_; 
v___x_26_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1(v___y_24_, v___y_25_);
v_a_27_ = lean_ctor_get(v___x_26_, 0);
v_a_28_ = lean_ctor_get(v___x_26_, 1);
v_isSharedCheck_36_ = !lean_is_exclusive(v___x_26_);
if (v_isSharedCheck_36_ == 0)
{
v___x_30_ = v___x_26_;
v_isShared_31_ = v_isSharedCheck_36_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_a_28_);
lean_inc(v_a_27_);
lean_dec(v___x_26_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_36_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v___x_32_; lean_object* v___x_34_; 
v___x_32_ = l_Lean_mkIdentFrom(v_ref_22_, v_a_27_, v_canonical_23_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 0, v___x_32_);
v___x_34_ = v___x_30_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v___x_32_);
lean_ctor_set(v_reuseFailAlloc_35_, 1, v_a_28_);
v___x_34_ = v_reuseFailAlloc_35_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
return v___x_34_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1___boxed(lean_object* v_ref_37_, lean_object* v_canonical_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
uint8_t v_canonical_boxed_41_; lean_object* v_res_42_; 
v_canonical_boxed_41_ = lean_unbox(v_canonical_38_);
v_res_42_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v_ref_37_, v_canonical_boxed_41_, v___y_39_, v___y_40_);
lean_dec(v_ref_37_);
return v_res_42_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__3));
v___x_48_ = l_String_toRawSubstring_x27(v___x_47_);
return v___x_48_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25(void){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Array_mkArray0(lean_box(0));
return v___x_80_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__32(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31));
v___x_88_ = l_String_toRawSubstring_x27(v___x_87_);
return v___x_88_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_107_ = l_String_toRawSubstring_x27(v___x_106_);
return v___x_107_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__52));
v___x_125_ = l_String_toRawSubstring_x27(v___x_124_);
return v___x_125_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__64(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__63));
v___x_145_ = l_String_toRawSubstring_x27(v___x_144_);
return v___x_145_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__68));
v___x_151_ = l_String_toRawSubstring_x27(v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(lean_object* v___x_160_, lean_object* v___x_161_, lean_object* v___x_162_, uint8_t v___x_163_, lean_object* v___x_164_, lean_object* v___x_165_, lean_object* v___x_166_, lean_object* v___f_167_, lean_object* v_fst_168_, lean_object* v___x_169_, lean_object* v_snd_170_, lean_object* v_x_171_, lean_object* v_h_x3f_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___y_178_; 
v___x_175_ = l_Lean_Syntax_getArg(v___x_160_, v___x_161_);
v___x_176_ = l_Lean_Syntax_getArg(v___x_160_, v___x_162_);
if (lean_obj_tag(v_h_x3f_172_) == 1)
{
lean_object* v_val_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v_val_393_ = lean_ctor_get(v_h_x3f_172_, 0);
v___x_394_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
lean_inc_ref(v___y_173_);
v___x_395_ = l_Lean_Macro_throwErrorAt___redArg(v_val_393_, v___x_394_, v___y_173_, v___y_174_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v_a_396_; 
v_a_396_ = lean_ctor_get(v___x_395_, 1);
lean_inc(v_a_396_);
lean_dec_ref(v___x_395_);
v___y_178_ = v_a_396_;
goto v___jp_177_;
}
else
{
lean_object* v_a_397_; lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_405_; 
lean_dec(v___x_176_);
lean_dec(v___x_175_);
lean_dec_ref(v___y_173_);
lean_dec(v_snd_170_);
lean_dec_ref(v___x_169_);
lean_dec(v_fst_168_);
lean_dec_ref(v___f_167_);
lean_dec_ref(v___x_166_);
lean_dec_ref(v___x_165_);
lean_dec_ref(v___x_164_);
v_a_397_ = lean_ctor_get(v___x_395_, 0);
v_a_398_ = lean_ctor_get(v___x_395_, 1);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_405_ == 0)
{
v___x_400_ = v___x_395_;
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_inc(v_a_397_);
lean_dec(v___x_395_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_397_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_a_398_);
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
else
{
v___y_178_ = v___y_174_;
goto v___jp_177_;
}
v___jp_177_:
{
lean_object* v_quotContext_179_; lean_object* v_currMacroScope_180_; lean_object* v_ref_181_; lean_object* v_ref_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v_macroScope_204_; lean_object* v_traceMsgs_205_; lean_object* v_expandedMacroDecls_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_392_; 
v_quotContext_179_ = lean_ctor_get(v___y_173_, 1);
lean_inc(v_quotContext_179_);
v_currMacroScope_180_ = lean_ctor_get(v___y_173_, 2);
lean_inc(v_currMacroScope_180_);
v_ref_181_ = lean_ctor_get(v___y_173_, 5);
lean_inc(v_ref_181_);
v_ref_182_ = l_Lean_replaceRef(v___x_176_, v_ref_181_);
v___x_183_ = l_Lean_SourceInfo_fromRef(v_ref_182_, v___x_163_);
lean_dec(v_ref_182_);
v___x_184_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__0));
lean_inc_ref(v___x_166_);
lean_inc_ref(v___x_165_);
lean_inc_ref(v___x_164_);
v___x_185_ = l_Lean_Name_mkStr4(v___x_164_, v___x_165_, v___x_166_, v___x_184_);
v___x_186_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__1));
lean_inc_ref(v___x_166_);
lean_inc_ref(v___x_165_);
lean_inc_ref(v___x_164_);
v___x_187_ = l_Lean_Name_mkStr4(v___x_164_, v___x_165_, v___x_166_, v___x_186_);
v___x_188_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__2));
lean_inc(v___x_183_);
v___x_189_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_183_);
lean_ctor_set(v___x_189_, 1, v___x_188_);
v___x_190_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4);
v___x_191_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7));
lean_inc(v_currMacroScope_180_);
lean_inc(v_quotContext_179_);
v___x_192_ = l_Lean_addMacroScope(v_quotContext_179_, v___x_191_, v_currMacroScope_180_);
v___x_193_ = lean_box(0);
v___x_194_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__11));
lean_inc(v___x_183_);
v___x_195_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_195_, 0, v___x_183_);
lean_ctor_set(v___x_195_, 1, v___x_190_);
lean_ctor_set(v___x_195_, 2, v___x_192_);
lean_ctor_set(v___x_195_, 3, v___x_194_);
lean_inc(v___x_187_);
lean_inc(v___x_183_);
v___x_196_ = l_Lean_Syntax_node2(v___x_183_, v___x_187_, v___x_189_, v___x_195_);
v___x_197_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_198_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__14));
lean_inc_ref(v___x_166_);
lean_inc_ref(v___x_165_);
lean_inc_ref(v___x_164_);
v___x_199_ = l_Lean_Name_mkStr4(v___x_164_, v___x_165_, v___x_166_, v___x_198_);
v___x_200_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15));
lean_inc(v___x_183_);
v___x_201_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_183_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
lean_inc(v___x_199_);
lean_inc(v___x_183_);
v___x_202_ = l_Lean_Syntax_node1(v___x_183_, v___x_199_, v___x_201_);
lean_inc(v___x_176_);
lean_inc_n(v___x_202_, 2);
lean_inc(v___x_183_);
v___x_203_ = l_Lean_Syntax_node4(v___x_183_, v___x_197_, v___x_202_, v___x_202_, v___x_202_, v___x_176_);
v_macroScope_204_ = lean_ctor_get(v___y_178_, 0);
v_traceMsgs_205_ = lean_ctor_get(v___y_178_, 1);
v_expandedMacroDecls_206_ = lean_ctor_get(v___y_178_, 2);
v_isSharedCheck_392_ = !lean_is_exclusive(v___y_178_);
if (v_isSharedCheck_392_ == 0)
{
v___x_208_ = v___y_178_;
v_isShared_209_ = v_isSharedCheck_392_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_expandedMacroDecls_206_);
lean_inc(v_traceMsgs_205_);
lean_inc(v_macroScope_204_);
lean_dec(v___y_178_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_392_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_210_; lean_object* v___x_212_; 
v___x_210_ = lean_nat_add(v_macroScope_204_, v___x_161_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 0, v___x_210_);
v___x_212_ = v___x_208_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_210_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v_traceMsgs_205_);
lean_ctor_set(v_reuseFailAlloc_391_, 2, v_expandedMacroDecls_206_);
v___x_212_ = v_reuseFailAlloc_391_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_213_; 
lean_inc_ref(v___f_167_);
lean_inc_ref(v___y_173_);
lean_inc(v_ref_181_);
v___x_213_ = lean_apply_3(v___f_167_, v_ref_181_, v___y_173_, v___x_212_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; lean_object* v_a_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_a_214_);
v_a_215_ = lean_ctor_get(v___x_213_, 1);
lean_inc(v_a_215_);
lean_dec_ref(v___x_213_);
lean_inc(v___x_185_);
v___x_216_ = l_Lean_Syntax_node2(v___x_183_, v___x_185_, v___x_196_, v___x_203_);
v___x_217_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17));
lean_inc(v_quotContext_179_);
v___x_218_ = l_Lean_addMacroScope(v_quotContext_179_, v___x_217_, v_macroScope_204_);
v___x_219_ = l_Lean_mkIdentFrom(v___x_176_, v___x_218_, v___x_163_);
lean_dec(v___x_176_);
v___x_220_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__18));
lean_inc_ref(v___x_166_);
lean_inc_ref(v___x_165_);
lean_inc_ref(v___x_164_);
v___x_221_ = l_Lean_Name_mkStr4(v___x_164_, v___x_165_, v___x_166_, v___x_220_);
v___x_222_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__19));
lean_inc_ref(v___x_166_);
lean_inc_ref(v___x_165_);
lean_inc_ref(v___x_164_);
v___x_223_ = l_Lean_Name_mkStr4(v___x_164_, v___x_165_, v___x_166_, v___x_222_);
v___x_224_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__20));
lean_inc(v_a_214_);
v___x_225_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_225_, 0, v_a_214_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
v___x_226_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__21));
lean_inc(v_a_214_);
v___x_227_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_227_, 0, v_a_214_);
lean_ctor_set(v___x_227_, 1, v___x_226_);
lean_inc(v_a_214_);
v___x_228_ = l_Lean_Syntax_node1(v_a_214_, v___x_197_, v___x_227_);
v___x_229_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__22));
lean_inc_ref(v___x_166_);
lean_inc_ref(v___x_165_);
lean_inc_ref(v___x_164_);
v___x_230_ = l_Lean_Name_mkStr4(v___x_164_, v___x_165_, v___x_166_, v___x_229_);
v___x_231_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23));
lean_inc_ref(v___x_166_);
lean_inc_ref(v___x_165_);
lean_inc_ref(v___x_164_);
v___x_232_ = l_Lean_Name_mkStr4(v___x_164_, v___x_165_, v___x_166_, v___x_231_);
v___x_233_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__24));
lean_inc_ref(v___x_166_);
lean_inc_ref(v___x_165_);
lean_inc_ref(v___x_164_);
v___x_234_ = l_Lean_Name_mkStr4(v___x_164_, v___x_165_, v___x_166_, v___x_233_);
lean_inc(v___x_219_);
lean_inc(v___x_234_);
lean_inc(v_a_214_);
v___x_235_ = l_Lean_Syntax_node1(v_a_214_, v___x_234_, v___x_219_);
v___x_236_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25);
lean_inc(v_a_214_);
v___x_237_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_237_, 0, v_a_214_);
lean_ctor_set(v___x_237_, 1, v___x_197_);
lean_ctor_set(v___x_237_, 2, v___x_236_);
v___x_238_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__26));
lean_inc(v_a_214_);
v___x_239_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_239_, 0, v_a_214_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
lean_inc_ref_n(v___x_237_, 2);
lean_inc(v_a_214_);
v___x_240_ = l_Lean_Syntax_node5(v_a_214_, v___x_232_, v___x_235_, v___x_237_, v___x_237_, v___x_239_, v___x_216_);
v___x_241_ = lean_apply_3(v___f_167_, v_ref_181_, v___y_173_, v_a_215_);
if (lean_obj_tag(v___x_241_) == 0)
{
lean_object* v_a_242_; lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_372_; 
v_a_242_ = lean_ctor_get(v___x_241_, 0);
v_a_243_ = lean_ctor_get(v___x_241_, 1);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_372_ == 0)
{
v___x_245_ = v___x_241_;
v_isShared_246_ = v_isSharedCheck_372_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_inc(v_a_242_);
lean_dec(v___x_241_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_372_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_370_; 
lean_inc(v_a_214_);
v___x_247_ = l_Lean_Syntax_node1(v_a_214_, v___x_230_, v___x_240_);
lean_inc(v_a_214_);
v___x_248_ = l_Lean_Syntax_node3(v_a_214_, v___x_223_, v___x_225_, v___x_228_, v___x_247_);
lean_inc(v___x_221_);
v___x_249_ = l_Lean_Syntax_node2(v_a_214_, v___x_221_, v___x_248_, v___x_237_);
v___x_250_ = lean_array_push(v_fst_168_, v___x_249_);
v___x_251_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__27));
lean_inc_ref(v___x_166_);
lean_inc_ref(v___x_165_);
lean_inc_ref(v___x_164_);
v___x_252_ = l_Lean_Name_mkStr4(v___x_164_, v___x_165_, v___x_166_, v___x_251_);
v___x_253_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28));
lean_inc_ref(v___x_166_);
lean_inc_ref(v___x_165_);
lean_inc_ref(v___x_164_);
v___x_254_ = l_Lean_Name_mkStr4(v___x_164_, v___x_165_, v___x_166_, v___x_253_);
v___x_255_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29));
lean_inc(v_a_242_);
v___x_256_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_256_, 0, v_a_242_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
lean_inc(v_a_242_);
v___x_257_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_257_, 0, v_a_242_);
lean_ctor_set(v___x_257_, 1, v___x_197_);
lean_ctor_set(v___x_257_, 2, v___x_236_);
v___x_258_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_ref(v___x_166_);
lean_inc_ref(v___x_165_);
lean_inc_ref(v___x_164_);
v___x_259_ = l_Lean_Name_mkStr4(v___x_164_, v___x_165_, v___x_166_, v___x_258_);
lean_inc(v_a_242_);
v___x_260_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_260_, 0, v_a_242_);
lean_ctor_set(v___x_260_, 1, v___x_188_);
v___x_261_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__32, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__32_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__32);
v___x_262_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__35));
lean_inc(v_currMacroScope_180_);
lean_inc(v_quotContext_179_);
v___x_263_ = l_Lean_addMacroScope(v_quotContext_179_, v___x_262_, v_currMacroScope_180_);
v___x_264_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__37));
lean_inc(v_a_242_);
v___x_265_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_265_, 0, v_a_242_);
lean_ctor_set(v___x_265_, 1, v___x_261_);
lean_ctor_set(v___x_265_, 2, v___x_263_);
lean_ctor_set(v___x_265_, 3, v___x_264_);
lean_inc(v_a_242_);
v___x_266_ = l_Lean_Syntax_node2(v_a_242_, v___x_187_, v___x_260_, v___x_265_);
lean_inc(v_a_242_);
v___x_267_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_267_, 0, v_a_242_);
lean_ctor_set(v___x_267_, 1, v___x_200_);
lean_inc(v_a_242_);
v___x_268_ = l_Lean_Syntax_node1(v_a_242_, v___x_199_, v___x_267_);
lean_inc(v___x_219_);
lean_inc_n(v___x_268_, 2);
lean_inc(v_a_242_);
v___x_269_ = l_Lean_Syntax_node4(v_a_242_, v___x_197_, v___x_268_, v___x_268_, v___x_268_, v___x_219_);
lean_inc(v___x_185_);
lean_inc(v_a_242_);
v___x_270_ = l_Lean_Syntax_node2(v_a_242_, v___x_185_, v___x_266_, v___x_269_);
lean_inc_ref(v___x_257_);
lean_inc(v_a_242_);
v___x_271_ = l_Lean_Syntax_node2(v_a_242_, v___x_259_, v___x_257_, v___x_270_);
lean_inc(v_a_242_);
v___x_272_ = l_Lean_Syntax_node1(v_a_242_, v___x_197_, v___x_271_);
v___x_273_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38));
lean_inc(v_a_242_);
v___x_274_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_274_, 0, v_a_242_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
v___x_275_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
lean_inc_ref(v___x_166_);
lean_inc_ref(v___x_165_);
lean_inc_ref(v___x_164_);
v___x_276_ = l_Lean_Name_mkStr4(v___x_164_, v___x_165_, v___x_166_, v___x_275_);
v___x_277_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40));
lean_inc_ref(v___x_166_);
lean_inc_ref(v___x_165_);
lean_inc_ref(v___x_164_);
v___x_278_ = l_Lean_Name_mkStr4(v___x_164_, v___x_165_, v___x_166_, v___x_277_);
v___x_279_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41));
lean_inc(v_a_242_);
v___x_280_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_280_, 0, v_a_242_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43);
v___x_282_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44));
lean_inc(v_currMacroScope_180_);
lean_inc(v_quotContext_179_);
v___x_283_ = l_Lean_addMacroScope(v_quotContext_179_, v___x_282_, v_currMacroScope_180_);
v___x_284_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__48));
lean_inc(v_a_242_);
v___x_285_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_285_, 0, v_a_242_);
lean_ctor_set(v___x_285_, 1, v___x_281_);
lean_ctor_set(v___x_285_, 2, v___x_283_);
lean_ctor_set(v___x_285_, 3, v___x_284_);
lean_inc(v_a_242_);
v___x_286_ = l_Lean_Syntax_node1(v_a_242_, v___x_197_, v___x_285_);
lean_inc(v_a_242_);
v___x_287_ = l_Lean_Syntax_node1(v_a_242_, v___x_197_, v___x_286_);
v___x_288_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49));
lean_inc(v_a_242_);
v___x_289_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_289_, 0, v_a_242_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
v___x_290_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
lean_inc_ref(v___x_166_);
lean_inc_ref(v___x_165_);
lean_inc_ref(v___x_164_);
v___x_291_ = l_Lean_Name_mkStr4(v___x_164_, v___x_165_, v___x_166_, v___x_290_);
v___x_292_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__51));
lean_inc(v_a_242_);
v___x_293_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_293_, 0, v_a_242_);
lean_ctor_set(v___x_293_, 1, v___x_292_);
lean_inc(v_a_242_);
v___x_294_ = l_Lean_Syntax_node1(v_a_242_, v___x_291_, v___x_293_);
lean_inc_ref(v___x_257_);
lean_inc(v___x_221_);
lean_inc(v_a_242_);
v___x_295_ = l_Lean_Syntax_node2(v_a_242_, v___x_221_, v___x_294_, v___x_257_);
lean_inc(v_a_242_);
v___x_296_ = l_Lean_Syntax_node1(v_a_242_, v___x_197_, v___x_295_);
lean_inc(v___x_252_);
lean_inc(v_a_242_);
v___x_297_ = l_Lean_Syntax_node1(v_a_242_, v___x_252_, v___x_296_);
lean_inc_ref(v___x_289_);
lean_inc_ref(v___x_280_);
lean_inc(v___x_278_);
lean_inc(v_a_242_);
v___x_298_ = l_Lean_Syntax_node4(v_a_242_, v___x_278_, v___x_280_, v___x_287_, v___x_289_, v___x_297_);
v___x_299_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53);
v___x_300_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54));
lean_inc(v_currMacroScope_180_);
lean_inc(v_quotContext_179_);
v___x_301_ = l_Lean_addMacroScope(v_quotContext_179_, v___x_300_, v_currMacroScope_180_);
v___x_302_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__57));
lean_inc(v_a_242_);
v___x_303_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_303_, 0, v_a_242_);
lean_ctor_set(v___x_303_, 1, v___x_299_);
lean_ctor_set(v___x_303_, 2, v___x_301_);
lean_ctor_set(v___x_303_, 3, v___x_302_);
v___x_304_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__58));
lean_inc_ref(v___x_166_);
lean_inc_ref(v___x_165_);
lean_inc_ref(v___x_164_);
v___x_305_ = l_Lean_Name_mkStr4(v___x_164_, v___x_165_, v___x_166_, v___x_304_);
v___x_306_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__59));
lean_inc_ref(v___x_166_);
lean_inc_ref(v___x_165_);
lean_inc_ref(v___x_164_);
v___x_307_ = l_Lean_Name_mkStr4(v___x_164_, v___x_165_, v___x_166_, v___x_306_);
v___x_308_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__60));
lean_inc(v_a_242_);
v___x_309_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_309_, 0, v_a_242_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
v___x_310_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__62));
v___x_311_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__64, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__64_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__64);
v___x_312_ = lean_box(0);
lean_inc(v_currMacroScope_180_);
lean_inc(v_quotContext_179_);
v___x_313_ = l_Lean_addMacroScope(v_quotContext_179_, v___x_312_, v_currMacroScope_180_);
v___x_314_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65));
v___x_315_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66));
lean_inc_ref(v___x_164_);
v___x_316_ = l_Lean_Name_mkStr3(v___x_164_, v___x_314_, v___x_315_);
v___x_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
v___x_318_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67));
lean_inc_ref(v___x_164_);
v___x_319_ = l_Lean_Name_mkStr2(v___x_164_, v___x_318_);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_inc_ref(v___x_166_);
lean_inc_ref(v___x_165_);
lean_inc_ref(v___x_164_);
v___x_321_ = l_Lean_Name_mkStr3(v___x_164_, v___x_165_, v___x_166_);
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
v___x_323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v___x_193_);
v___x_324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_320_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
v___x_325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_317_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
lean_inc(v_a_242_);
v___x_326_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_326_, 0, v_a_242_);
lean_ctor_set(v___x_326_, 1, v___x_311_);
lean_ctor_set(v___x_326_, 2, v___x_313_);
lean_ctor_set(v___x_326_, 3, v___x_325_);
lean_inc(v_a_242_);
v___x_327_ = l_Lean_Syntax_node1(v_a_242_, v___x_310_, v___x_326_);
lean_inc(v_a_242_);
v___x_328_ = l_Lean_Syntax_node2(v_a_242_, v___x_307_, v___x_309_, v___x_327_);
lean_inc(v_a_242_);
v___x_329_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_329_, 0, v_a_242_);
lean_ctor_set(v___x_329_, 1, v___x_169_);
v___x_330_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69);
v___x_331_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70));
v___x_332_ = l_Lean_addMacroScope(v_quotContext_179_, v___x_331_, v_currMacroScope_180_);
lean_inc(v_a_242_);
v___x_333_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_333_, 0, v_a_242_);
lean_ctor_set(v___x_333_, 1, v___x_330_);
lean_ctor_set(v___x_333_, 2, v___x_332_);
lean_ctor_set(v___x_333_, 3, v___x_193_);
lean_inc_ref(v___x_333_);
lean_inc(v_a_242_);
v___x_334_ = l_Lean_Syntax_node1(v_a_242_, v___x_197_, v___x_333_);
lean_inc(v_a_242_);
v___x_335_ = l_Lean_Syntax_node3(v_a_242_, v___x_197_, v___x_175_, v___x_329_, v___x_334_);
v___x_336_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__71));
lean_inc(v_a_242_);
v___x_337_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_337_, 0, v_a_242_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
lean_inc(v_a_242_);
v___x_338_ = l_Lean_Syntax_node3(v_a_242_, v___x_305_, v___x_328_, v___x_335_, v___x_337_);
lean_inc(v_a_242_);
v___x_339_ = l_Lean_Syntax_node1(v_a_242_, v___x_197_, v___x_338_);
lean_inc(v_a_242_);
v___x_340_ = l_Lean_Syntax_node2(v_a_242_, v___x_185_, v___x_303_, v___x_339_);
lean_inc(v_a_242_);
v___x_341_ = l_Lean_Syntax_node1(v_a_242_, v___x_197_, v___x_340_);
lean_inc(v_a_242_);
v___x_342_ = l_Lean_Syntax_node1(v_a_242_, v___x_197_, v___x_341_);
v___x_343_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__72));
lean_inc_ref(v___x_166_);
lean_inc_ref(v___x_165_);
lean_inc_ref(v___x_164_);
v___x_344_ = l_Lean_Name_mkStr4(v___x_164_, v___x_165_, v___x_166_, v___x_343_);
v___x_345_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__73));
lean_inc_ref(v___x_166_);
lean_inc_ref(v___x_165_);
lean_inc_ref(v___x_164_);
v___x_346_ = l_Lean_Name_mkStr4(v___x_164_, v___x_165_, v___x_166_, v___x_345_);
lean_inc(v_a_242_);
v___x_347_ = l_Lean_Syntax_node1(v_a_242_, v___x_234_, v___x_219_);
lean_inc(v_a_242_);
v___x_348_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_348_, 0, v_a_242_);
lean_ctor_set(v___x_348_, 1, v___x_238_);
lean_inc_ref_n(v___x_257_, 2);
lean_inc(v_a_242_);
v___x_349_ = l_Lean_Syntax_node5(v_a_242_, v___x_346_, v___x_347_, v___x_257_, v___x_257_, v___x_348_, v___x_333_);
lean_inc(v_a_242_);
v___x_350_ = l_Lean_Syntax_node1(v_a_242_, v___x_344_, v___x_349_);
lean_inc_ref(v___x_257_);
lean_inc(v___x_221_);
lean_inc(v_a_242_);
v___x_351_ = l_Lean_Syntax_node2(v_a_242_, v___x_221_, v___x_350_, v___x_257_);
v___x_352_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__74));
v___x_353_ = l_Lean_Name_mkStr4(v___x_164_, v___x_165_, v___x_166_, v___x_352_);
v___x_354_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75));
lean_inc(v_a_242_);
v___x_355_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_355_, 0, v_a_242_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
lean_inc(v_a_242_);
v___x_356_ = l_Lean_Syntax_node2(v_a_242_, v___x_353_, v___x_355_, v_snd_170_);
lean_inc_ref(v___x_257_);
lean_inc(v___x_221_);
lean_inc(v_a_242_);
v___x_357_ = l_Lean_Syntax_node2(v_a_242_, v___x_221_, v___x_356_, v___x_257_);
lean_inc(v_a_242_);
v___x_358_ = l_Lean_Syntax_node2(v_a_242_, v___x_197_, v___x_351_, v___x_357_);
lean_inc(v___x_252_);
lean_inc(v_a_242_);
v___x_359_ = l_Lean_Syntax_node1(v_a_242_, v___x_252_, v___x_358_);
lean_inc(v_a_242_);
v___x_360_ = l_Lean_Syntax_node4(v_a_242_, v___x_278_, v___x_280_, v___x_342_, v___x_289_, v___x_359_);
lean_inc(v_a_242_);
v___x_361_ = l_Lean_Syntax_node2(v_a_242_, v___x_197_, v___x_298_, v___x_360_);
lean_inc(v_a_242_);
v___x_362_ = l_Lean_Syntax_node1(v_a_242_, v___x_276_, v___x_361_);
lean_inc_ref_n(v___x_257_, 3);
lean_inc(v_a_242_);
v___x_363_ = l_Lean_Syntax_node7(v_a_242_, v___x_254_, v___x_256_, v___x_257_, v___x_257_, v___x_257_, v___x_272_, v___x_274_, v___x_362_);
lean_inc(v_a_242_);
v___x_364_ = l_Lean_Syntax_node2(v_a_242_, v___x_221_, v___x_363_, v___x_257_);
lean_inc(v_a_242_);
v___x_365_ = l_Lean_Syntax_node1(v_a_242_, v___x_197_, v___x_364_);
v___x_366_ = l_Lean_Syntax_node1(v_a_242_, v___x_252_, v___x_365_);
v___x_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_250_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
v___x_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_368_);
v___x_370_ = v___x_245_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_368_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_a_243_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
else
{
lean_object* v_a_373_; lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_dec(v___x_240_);
lean_dec_ref(v___x_237_);
lean_dec(v___x_234_);
lean_dec(v___x_230_);
lean_dec(v___x_228_);
lean_dec_ref(v___x_225_);
lean_dec(v___x_223_);
lean_dec(v___x_221_);
lean_dec(v___x_219_);
lean_dec(v_a_214_);
lean_dec(v___x_199_);
lean_dec(v___x_187_);
lean_dec(v___x_185_);
lean_dec(v_currMacroScope_180_);
lean_dec(v_quotContext_179_);
lean_dec(v___x_175_);
lean_dec(v_snd_170_);
lean_dec_ref(v___x_169_);
lean_dec(v_fst_168_);
lean_dec_ref(v___x_166_);
lean_dec_ref(v___x_165_);
lean_dec_ref(v___x_164_);
v_a_373_ = lean_ctor_get(v___x_241_, 0);
v_a_374_ = lean_ctor_get(v___x_241_, 1);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_241_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_inc(v_a_373_);
lean_dec(v___x_241_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_373_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
else
{
lean_object* v_a_382_; lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
lean_dec(v_macroScope_204_);
lean_dec(v___x_203_);
lean_dec(v___x_199_);
lean_dec(v___x_196_);
lean_dec(v___x_187_);
lean_dec(v___x_185_);
lean_dec(v___x_183_);
lean_dec(v_ref_181_);
lean_dec(v_currMacroScope_180_);
lean_dec(v_quotContext_179_);
lean_dec(v___x_176_);
lean_dec(v___x_175_);
lean_dec_ref(v___y_173_);
lean_dec(v_snd_170_);
lean_dec_ref(v___x_169_);
lean_dec(v_fst_168_);
lean_dec_ref(v___f_167_);
lean_dec_ref(v___x_166_);
lean_dec_ref(v___x_165_);
lean_dec_ref(v___x_164_);
v_a_382_ = lean_ctor_get(v___x_213_, 0);
v_a_383_ = lean_ctor_get(v___x_213_, 1);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_213_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_inc(v_a_382_);
lean_dec(v___x_213_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_382_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v_a_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___boxed(lean_object* v___x_406_, lean_object* v___x_407_, lean_object* v___x_408_, lean_object* v___x_409_, lean_object* v___x_410_, lean_object* v___x_411_, lean_object* v___x_412_, lean_object* v___f_413_, lean_object* v_fst_414_, lean_object* v___x_415_, lean_object* v_snd_416_, lean_object* v_x_417_, lean_object* v_h_x3f_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
uint8_t v___x_145183__boxed_421_; lean_object* v_res_422_; 
v___x_145183__boxed_421_ = lean_unbox(v___x_409_);
v_res_422_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(v___x_406_, v___x_407_, v___x_408_, v___x_145183__boxed_421_, v___x_410_, v___x_411_, v___x_412_, v___f_413_, v_fst_414_, v___x_415_, v_snd_416_, v_x_417_, v_h_x3f_418_, v___y_419_, v___y_420_);
lean_dec(v_h_x3f_418_);
lean_dec(v___x_408_);
lean_dec(v___x_407_);
lean_dec(v___x_406_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0(uint8_t v___x_423_, lean_object* v_____do__lift_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = l_Lean_SourceInfo_fromRef(v_____do__lift_424_, v___x_423_);
v___x_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v___y_426_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0___boxed(lean_object* v___x_429_, lean_object* v_____do__lift_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
uint8_t v___x_145782__boxed_433_; lean_object* v_res_434_; 
v___x_145782__boxed_433_ = lean_unbox(v___x_429_);
v_res_434_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0(v___x_145782__boxed_433_, v_____do__lift_430_, v___y_431_, v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v_____do__lift_430_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(uint8_t v___x_445_, lean_object* v_a_446_, lean_object* v_b_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v_array_450_; lean_object* v_start_451_; lean_object* v_stop_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_546_; 
v_array_450_ = lean_ctor_get(v_a_446_, 0);
v_start_451_ = lean_ctor_get(v_a_446_, 1);
v_stop_452_ = lean_ctor_get(v_a_446_, 2);
v_isSharedCheck_546_ = !lean_is_exclusive(v_a_446_);
if (v_isSharedCheck_546_ == 0)
{
v___x_454_ = v_a_446_;
v_isShared_455_ = v_isSharedCheck_546_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_stop_452_);
lean_inc(v_start_451_);
lean_inc(v_array_450_);
lean_dec(v_a_446_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_546_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
uint8_t v___x_456_; 
v___x_456_ = lean_nat_dec_lt(v_start_451_, v_stop_452_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; 
lean_del_object(v___x_454_);
lean_dec(v_stop_452_);
lean_dec(v_start_451_);
lean_dec_ref(v_array_450_);
lean_dec_ref(v___y_448_);
v___x_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_457_, 0, v_b_447_);
lean_ctor_set(v___x_457_, 1, v___y_449_);
return v___x_457_;
}
else
{
lean_object* v_fst_458_; lean_object* v_snd_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_545_; 
v_fst_458_ = lean_ctor_get(v_b_447_, 0);
v_snd_459_ = lean_ctor_get(v_b_447_, 1);
v_isSharedCheck_545_ = !lean_is_exclusive(v_b_447_);
if (v_isSharedCheck_545_ == 0)
{
v___x_461_ = v_b_447_;
v_isShared_462_ = v_isSharedCheck_545_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_snd_459_);
lean_inc(v_fst_458_);
lean_dec(v_b_447_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_545_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_470_; 
v___x_463_ = lean_unsigned_to_nat(1u);
v___x_464_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0));
v___x_465_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1));
v___x_466_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2));
v___x_467_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
v___x_468_ = lean_nat_add(v_start_451_, v___x_463_);
lean_inc_ref(v_array_450_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 1, v___x_468_);
v___x_470_ = v___x_454_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_array_450_);
lean_ctor_set(v_reuseFailAlloc_544_, 1, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_544_, 2, v_stop_452_);
v___x_470_ = v_reuseFailAlloc_544_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
lean_object* v___y_472_; lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_496_ = lean_array_fget(v_array_450_, v_start_451_);
lean_dec(v_start_451_);
lean_dec_ref(v_array_450_);
lean_inc(v___x_496_);
v___x_497_ = l_Lean_Syntax_isOfKind(v___x_496_, v___x_467_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; 
lean_dec(v___x_496_);
v___x_498_ = l_Lean_Macro_throwUnsupported___redArg(v___y_449_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_501_; 
v_a_499_ = lean_ctor_get(v___x_498_, 1);
lean_inc(v_a_499_);
lean_dec_ref(v___x_498_);
if (v_isShared_462_ == 0)
{
v___x_501_ = v___x_461_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_fst_458_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v_snd_459_);
v___x_501_ = v_reuseFailAlloc_503_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
v_a_446_ = v___x_470_;
v_b_447_ = v___x_501_;
v___y_449_ = v_a_499_;
goto _start;
}
}
else
{
lean_object* v_a_504_; lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
lean_dec_ref(v___x_470_);
lean_del_object(v___x_461_);
lean_dec(v_snd_459_);
lean_dec(v_fst_458_);
lean_dec_ref(v___y_448_);
v_a_504_ = lean_ctor_get(v___x_498_, 0);
v_a_505_ = lean_ctor_get(v___x_498_, 1);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v___x_498_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_inc(v_a_504_);
lean_dec(v___x_498_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_504_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_a_505_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
else
{
lean_object* v___x_513_; lean_object* v___f_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_513_ = lean_box(v___x_445_);
v___f_514_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_514_, 0, v___x_513_);
v___x_515_ = lean_unsigned_to_nat(3u);
v___x_516_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__5));
v___x_517_ = lean_unsigned_to_nat(0u);
v___x_518_ = l_Lean_Syntax_getArg(v___x_496_, v___x_517_);
v___x_519_ = l_Lean_Syntax_isNone(v___x_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_520_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_518_);
v___x_521_ = l_Lean_Syntax_matchesNull(v___x_518_, v___x_520_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; 
lean_dec(v___x_518_);
lean_dec_ref(v___f_514_);
lean_dec(v___x_496_);
v___x_522_ = l_Lean_Macro_throwUnsupported___redArg(v___y_449_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v___x_525_; 
v_a_523_ = lean_ctor_get(v___x_522_, 1);
lean_inc(v_a_523_);
lean_dec_ref(v___x_522_);
if (v_isShared_462_ == 0)
{
v___x_525_ = v___x_461_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_fst_458_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_snd_459_);
v___x_525_ = v_reuseFailAlloc_527_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
v_a_446_ = v___x_470_;
v_b_447_ = v___x_525_;
v___y_449_ = v_a_523_;
goto _start;
}
}
else
{
lean_object* v_a_528_; lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
lean_dec_ref(v___x_470_);
lean_del_object(v___x_461_);
lean_dec(v_snd_459_);
lean_dec(v_fst_458_);
lean_dec_ref(v___y_448_);
v_a_528_ = lean_ctor_get(v___x_522_, 0);
v_a_529_ = lean_ctor_get(v___x_522_, 1);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___x_522_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_inc(v_a_528_);
lean_dec(v___x_522_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_528_);
lean_ctor_set(v_reuseFailAlloc_535_, 1, v_a_529_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
else
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
lean_del_object(v___x_461_);
v___x_537_ = l_Lean_Syntax_getArg(v___x_518_, v___x_517_);
lean_dec(v___x_518_);
v___x_538_ = lean_box(0);
v___x_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_539_, 0, v___x_537_);
lean_inc_ref(v___y_448_);
v___x_540_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(v___x_496_, v___x_463_, v___x_515_, v___x_445_, v___x_464_, v___x_465_, v___x_466_, v___f_514_, v_fst_458_, v___x_516_, v_snd_459_, v___x_538_, v___x_539_, v___y_448_, v___y_449_);
lean_dec_ref(v___x_539_);
lean_dec(v___x_496_);
v___y_472_ = v___x_540_;
goto v___jp_471_;
}
}
else
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
lean_dec(v___x_518_);
lean_del_object(v___x_461_);
v___x_541_ = lean_box(0);
v___x_542_ = lean_box(0);
lean_inc_ref(v___y_448_);
v___x_543_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(v___x_496_, v___x_463_, v___x_515_, v___x_445_, v___x_464_, v___x_465_, v___x_466_, v___f_514_, v_fst_458_, v___x_516_, v_snd_459_, v___x_541_, v___x_542_, v___y_448_, v___y_449_);
lean_dec(v___x_496_);
v___y_472_ = v___x_543_;
goto v___jp_471_;
}
}
v___jp_471_:
{
if (lean_obj_tag(v___y_472_) == 0)
{
lean_object* v_a_473_; 
v_a_473_ = lean_ctor_get(v___y_472_, 0);
lean_inc(v_a_473_);
if (lean_obj_tag(v_a_473_) == 0)
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_482_; 
lean_dec_ref(v___x_470_);
lean_dec_ref(v___y_448_);
v_a_474_ = lean_ctor_get(v___y_472_, 1);
v_isSharedCheck_482_ = !lean_is_exclusive(v___y_472_);
if (v_isSharedCheck_482_ == 0)
{
lean_object* v_unused_483_; 
v_unused_483_ = lean_ctor_get(v___y_472_, 0);
lean_dec(v_unused_483_);
v___x_476_ = v___y_472_;
v_isShared_477_ = v_isSharedCheck_482_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___y_472_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_482_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v_a_478_; lean_object* v___x_480_; 
v_a_478_ = lean_ctor_get(v_a_473_, 0);
lean_inc(v_a_478_);
lean_dec_ref(v_a_473_);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v_a_478_);
v___x_480_ = v___x_476_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_478_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_a_474_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
else
{
lean_object* v_a_484_; lean_object* v_a_485_; 
v_a_484_ = lean_ctor_get(v___y_472_, 1);
lean_inc(v_a_484_);
lean_dec_ref(v___y_472_);
v_a_485_ = lean_ctor_get(v_a_473_, 0);
lean_inc(v_a_485_);
lean_dec_ref(v_a_473_);
v_a_446_ = v___x_470_;
v_b_447_ = v_a_485_;
v___y_449_ = v_a_484_;
goto _start;
}
}
else
{
lean_object* v_a_487_; lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_dec_ref(v___x_470_);
lean_dec_ref(v___y_448_);
v_a_487_ = lean_ctor_get(v___y_472_, 0);
v_a_488_ = lean_ctor_get(v___y_472_, 1);
v_isSharedCheck_495_ = !lean_is_exclusive(v___y_472_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___y_472_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_inc(v_a_487_);
lean_dec(v___y_472_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_487_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___boxed(lean_object* v___x_547_, lean_object* v_a_548_, lean_object* v_b_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
uint8_t v___x_145818__boxed_552_; lean_object* v_res_553_; 
v___x_145818__boxed_552_ = lean_unbox(v___x_547_);
v_res_553_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_145818__boxed_552_, v_a_548_, v_b_549_, v___y_550_, v___y_551_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor(lean_object* v_stx_610_, lean_object* v_a_611_, lean_object* v_a_612_){
_start:
{
lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_613_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
lean_inc(v_stx_610_);
v___x_614_ = l_Lean_Syntax_isOfKind(v_stx_610_, v___x_613_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; 
lean_dec_ref(v_a_611_);
lean_dec(v_stx_610_);
v___x_615_ = l_Lean_Macro_throwUnsupported___redArg(v_a_612_);
return v___x_615_;
}
else
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_616_ = lean_unsigned_to_nat(0u);
v___x_617_ = lean_unsigned_to_nat(1u);
v___x_618_ = l_Lean_Syntax_getArg(v_stx_610_, v___x_617_);
lean_inc(v___x_618_);
v___x_619_ = l_Lean_Syntax_matchesNull(v___x_618_, v___x_617_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v_decls_652_; lean_object* v_decls_653_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v_x_658_; lean_object* v_body_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_620_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
v_decls_652_ = l_Lean_Syntax_getArgs(v___x_618_);
lean_dec(v___x_618_);
v_decls_653_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_652_);
lean_dec_ref(v_decls_652_);
v___x_697_ = lean_box(0);
v___x_698_ = lean_array_get(v___x_697_, v_decls_653_, v___x_616_);
lean_inc(v___x_698_);
v___x_699_ = l_Lean_Syntax_isOfKind(v___x_698_, v___x_620_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; 
lean_dec(v___x_698_);
lean_dec_ref(v_decls_653_);
lean_dec_ref(v_a_611_);
lean_dec(v_stx_610_);
v___x_700_ = l_Lean_Macro_throwUnsupported___redArg(v_a_612_);
return v___x_700_;
}
else
{
lean_object* v___x_701_; lean_object* v_body_702_; lean_object* v_h_x3f_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_701_ = lean_unsigned_to_nat(3u);
v_body_702_ = l_Lean_Syntax_getArg(v_stx_610_, v___x_701_);
lean_dec(v_stx_610_);
v___x_767_ = l_Lean_Syntax_getArg(v___x_698_, v___x_616_);
v___x_768_ = l_Lean_Syntax_isNone(v___x_767_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_769_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_767_);
v___x_770_ = l_Lean_Syntax_matchesNull(v___x_767_, v___x_769_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; 
lean_dec(v___x_767_);
lean_dec(v_body_702_);
lean_dec(v___x_698_);
lean_dec_ref(v_decls_653_);
lean_dec_ref(v_a_611_);
v___x_771_ = l_Lean_Macro_throwUnsupported___redArg(v_a_612_);
return v___x_771_;
}
else
{
lean_object* v_h_x3f_772_; lean_object* v___x_773_; 
v_h_x3f_772_ = l_Lean_Syntax_getArg(v___x_767_, v___x_616_);
lean_dec(v___x_767_);
v___x_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_773_, 0, v_h_x3f_772_);
v_h_x3f_704_ = v___x_773_;
v___y_705_ = v_a_611_;
v___y_706_ = v_a_612_;
goto v___jp_703_;
}
}
else
{
lean_object* v___x_774_; 
lean_dec(v___x_767_);
v___x_774_ = lean_box(0);
v_h_x3f_704_ = v___x_774_;
v___y_705_ = v_a_611_;
v___y_706_ = v_a_612_;
goto v___jp_703_;
}
v___jp_703_:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v_doElems_709_; uint8_t v___x_710_; 
v___x_707_ = l_Lean_Syntax_getArg(v___x_698_, v___x_617_);
v___x_708_ = l_Lean_Syntax_getArg(v___x_698_, v___x_701_);
lean_dec(v___x_698_);
v_doElems_709_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_710_ = l_Lean_Syntax_isIdent(v___x_707_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_711_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_707_);
v___x_712_ = l_Lean_Syntax_isOfKind(v___x_707_, v___x_711_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; 
lean_inc_ref(v___y_705_);
v___x_713_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_707_, v___x_712_, v___y_705_, v___y_706_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v_a_715_; lean_object* v_ref_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_a_714_);
v_a_715_ = lean_ctor_get(v___x_713_, 1);
lean_inc(v_a_715_);
lean_dec_ref(v___x_713_);
v_ref_716_ = lean_ctor_get(v___y_705_, 5);
v___x_717_ = l_Lean_SourceInfo_fromRef(v_ref_716_, v___x_712_);
v___x_718_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_719_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_720_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_721_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_722_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29));
lean_inc(v___x_717_);
v___x_723_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_717_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
v___x_724_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25);
lean_inc(v___x_717_);
v___x_725_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_725_, 0, v___x_717_);
lean_ctor_set(v___x_725_, 1, v___x_719_);
lean_ctor_set(v___x_725_, 2, v___x_724_);
v___x_726_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc(v_a_714_);
lean_inc_ref(v___x_725_);
lean_inc(v___x_717_);
v___x_727_ = l_Lean_Syntax_node2(v___x_717_, v___x_726_, v___x_725_, v_a_714_);
lean_inc(v___x_717_);
v___x_728_ = l_Lean_Syntax_node1(v___x_717_, v___x_719_, v___x_727_);
v___x_729_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38));
lean_inc(v___x_717_);
v___x_730_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_717_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_732_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_733_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41));
lean_inc(v___x_717_);
v___x_734_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_717_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
lean_inc(v___x_717_);
v___x_735_ = l_Lean_Syntax_node1(v___x_717_, v___x_719_, v___x_707_);
lean_inc(v___x_717_);
v___x_736_ = l_Lean_Syntax_node1(v___x_717_, v___x_719_, v___x_735_);
v___x_737_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49));
lean_inc(v___x_717_);
v___x_738_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_717_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
lean_inc(v___x_717_);
v___x_739_ = l_Lean_Syntax_node4(v___x_717_, v___x_732_, v___x_734_, v___x_736_, v___x_738_, v_body_702_);
lean_inc(v___x_717_);
v___x_740_ = l_Lean_Syntax_node1(v___x_717_, v___x_719_, v___x_739_);
lean_inc(v___x_717_);
v___x_741_ = l_Lean_Syntax_node1(v___x_717_, v___x_731_, v___x_740_);
lean_inc_ref_n(v___x_725_, 3);
lean_inc(v___x_717_);
v___x_742_ = l_Lean_Syntax_node7(v___x_717_, v___x_721_, v___x_723_, v___x_725_, v___x_725_, v___x_725_, v___x_728_, v___x_730_, v___x_741_);
lean_inc(v___x_717_);
v___x_743_ = l_Lean_Syntax_node2(v___x_717_, v___x_720_, v___x_742_, v___x_725_);
lean_inc(v___x_717_);
v___x_744_ = l_Lean_Syntax_node1(v___x_717_, v___x_719_, v___x_743_);
v___x_745_ = l_Lean_Syntax_node1(v___x_717_, v___x_718_, v___x_744_);
v___y_655_ = v___x_708_;
v___y_656_ = v_doElems_709_;
v___y_657_ = v_h_x3f_704_;
v_x_658_ = v_a_714_;
v_body_659_ = v___x_745_;
v___y_660_ = v___y_705_;
v___y_661_ = v_a_715_;
goto v___jp_654_;
}
else
{
lean_object* v_a_746_; lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
lean_dec(v___x_708_);
lean_dec(v___x_707_);
lean_dec_ref(v___y_705_);
lean_dec(v_h_x3f_704_);
lean_dec(v_body_702_);
lean_dec_ref(v_decls_653_);
v_a_746_ = lean_ctor_get(v___x_713_, 0);
v_a_747_ = lean_ctor_get(v___x_713_, 1);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_713_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_inc(v_a_746_);
lean_dec(v___x_713_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_746_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
else
{
lean_object* v___x_755_; 
lean_inc_ref(v___y_705_);
v___x_755_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_707_, v___x_710_, v___y_705_, v___y_706_);
lean_dec(v___x_707_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; lean_object* v_a_757_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_756_);
v_a_757_ = lean_ctor_get(v___x_755_, 1);
lean_inc(v_a_757_);
lean_dec_ref(v___x_755_);
v___y_655_ = v___x_708_;
v___y_656_ = v_doElems_709_;
v___y_657_ = v_h_x3f_704_;
v_x_658_ = v_a_756_;
v_body_659_ = v_body_702_;
v___y_660_ = v___y_705_;
v___y_661_ = v_a_757_;
goto v___jp_654_;
}
else
{
lean_object* v_a_758_; lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_dec(v___x_708_);
lean_dec_ref(v___y_705_);
lean_dec(v_h_x3f_704_);
lean_dec(v_body_702_);
lean_dec_ref(v_decls_653_);
v_a_758_ = lean_ctor_get(v___x_755_, 0);
v_a_759_ = lean_ctor_get(v___x_755_, 1);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_755_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_inc(v_a_758_);
lean_dec(v___x_755_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_758_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
}
else
{
v___y_655_ = v___x_708_;
v___y_656_ = v_doElems_709_;
v___y_657_ = v_h_x3f_704_;
v_x_658_ = v___x_707_;
v_body_659_ = v_body_702_;
v___y_660_ = v___y_705_;
v___y_661_ = v___y_706_;
goto v___jp_654_;
}
}
}
v___jp_621_:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
lean_inc_ref(v___y_623_);
v___x_633_ = l_Array_append___redArg(v___y_623_, v___y_632_);
lean_dec_ref(v___y_632_);
lean_inc(v___y_631_);
lean_inc(v___y_622_);
v___x_634_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_634_, 0, v___y_622_);
lean_ctor_set(v___x_634_, 1, v___y_631_);
lean_ctor_set(v___x_634_, 2, v___x_633_);
v___x_635_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
lean_inc(v___y_622_);
v___x_636_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_636_, 0, v___y_622_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
lean_inc(v___y_622_);
v___x_637_ = l_Lean_Syntax_node4(v___y_622_, v___x_620_, v___x_634_, v___y_630_, v___x_636_, v___y_625_);
lean_inc(v___y_631_);
lean_inc(v___y_622_);
v___x_638_ = l_Lean_Syntax_node1(v___y_622_, v___y_631_, v___x_637_);
v___x_639_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75));
lean_inc(v___y_622_);
v___x_640_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_640_, 0, v___y_622_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
lean_inc_ref(v___x_640_);
lean_inc(v___y_622_);
v___x_641_ = l_Lean_Syntax_node4(v___y_622_, v___x_613_, v___y_624_, v___x_638_, v___x_640_, v___y_629_);
lean_inc_ref(v___y_623_);
lean_inc(v___y_631_);
lean_inc(v___y_622_);
v___x_642_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_642_, 0, v___y_622_);
lean_ctor_set(v___x_642_, 1, v___y_631_);
lean_ctor_set(v___x_642_, 2, v___y_623_);
lean_inc(v___y_622_);
v___x_643_ = l_Lean_Syntax_node2(v___y_622_, v___y_626_, v___x_641_, v___x_642_);
v___x_644_ = lean_array_push(v___y_628_, v___x_643_);
v___x_645_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_646_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_647_ = l_Array_append___redArg(v___y_623_, v___x_644_);
lean_dec_ref(v___x_644_);
lean_inc(v___y_622_);
v___x_648_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_648_, 0, v___y_622_);
lean_ctor_set(v___x_648_, 1, v___y_631_);
lean_ctor_set(v___x_648_, 2, v___x_647_);
lean_inc(v___y_622_);
v___x_649_ = l_Lean_Syntax_node1(v___y_622_, v___x_646_, v___x_648_);
v___x_650_ = l_Lean_Syntax_node2(v___y_622_, v___x_645_, v___x_640_, v___x_649_);
v___x_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
lean_ctor_set(v___x_651_, 1, v___y_627_);
return v___x_651_;
}
v___jp_654_:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_662_ = lean_array_get_size(v_decls_653_);
v___x_663_ = l_Array_toSubarray___redArg(v_decls_653_, v___x_617_, v___x_662_);
v___x_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_664_, 0, v___y_656_);
lean_ctor_set(v___x_664_, 1, v_body_659_);
lean_inc_ref(v___y_660_);
v___x_665_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_619_, v___x_663_, v___x_664_, v___y_660_, v___y_661_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; lean_object* v_a_667_; lean_object* v_fst_668_; lean_object* v_snd_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_687_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_a_666_);
v_a_667_ = lean_ctor_get(v___x_665_, 1);
lean_inc(v_a_667_);
lean_dec_ref(v___x_665_);
v_fst_668_ = lean_ctor_get(v_a_666_, 0);
v_snd_669_ = lean_ctor_get(v_a_666_, 1);
v_isSharedCheck_687_ = !lean_is_exclusive(v_a_666_);
if (v_isSharedCheck_687_ == 0)
{
v___x_671_ = v_a_666_;
v_isShared_672_ = v_isSharedCheck_687_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_snd_669_);
lean_inc(v_fst_668_);
lean_dec(v_a_666_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_687_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v_ref_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_678_; 
v_ref_673_ = lean_ctor_get(v___y_660_, 5);
lean_inc(v_ref_673_);
lean_dec_ref(v___y_660_);
v___x_674_ = l_Lean_SourceInfo_fromRef(v_ref_673_, v___x_619_);
lean_dec(v_ref_673_);
v___x_675_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_676_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
lean_inc(v___x_674_);
if (v_isShared_672_ == 0)
{
lean_ctor_set_tag(v___x_671_, 2);
lean_ctor_set(v___x_671_, 1, v___x_676_);
lean_ctor_set(v___x_671_, 0, v___x_674_);
v___x_678_ = v___x_671_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v___x_674_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v___x_676_);
v___x_678_ = v_reuseFailAlloc_686_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_680_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25);
if (lean_obj_tag(v___y_657_) == 1)
{
lean_object* v_val_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v_val_681_ = lean_ctor_get(v___y_657_, 0);
lean_inc(v_val_681_);
lean_dec_ref(v___y_657_);
v___x_682_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
lean_inc(v___x_674_);
v___x_683_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_674_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v___x_684_ = l_Array_mkArray2___redArg(v_val_681_, v___x_683_);
v___y_622_ = v___x_674_;
v___y_623_ = v___x_680_;
v___y_624_ = v___x_678_;
v___y_625_ = v___y_655_;
v___y_626_ = v___x_675_;
v___y_627_ = v_a_667_;
v___y_628_ = v_fst_668_;
v___y_629_ = v_snd_669_;
v___y_630_ = v_x_658_;
v___y_631_ = v___x_679_;
v___y_632_ = v___x_684_;
goto v___jp_621_;
}
else
{
lean_object* v___x_685_; 
lean_dec(v___y_657_);
v___x_685_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
v___y_622_ = v___x_674_;
v___y_623_ = v___x_680_;
v___y_624_ = v___x_678_;
v___y_625_ = v___y_655_;
v___y_626_ = v___x_675_;
v___y_627_ = v_a_667_;
v___y_628_ = v_fst_668_;
v___y_629_ = v_snd_669_;
v___y_630_ = v_x_658_;
v___y_631_ = v___x_679_;
v___y_632_ = v___x_685_;
goto v___jp_621_;
}
}
}
}
else
{
lean_object* v_a_688_; lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec_ref(v___y_660_);
lean_dec(v_x_658_);
lean_dec(v___y_657_);
lean_dec(v___y_655_);
v_a_688_ = lean_ctor_get(v___x_665_, 0);
v_a_689_ = lean_ctor_get(v___x_665_, 1);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_665_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_inc(v_a_688_);
lean_dec(v___x_665_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_688_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
}
else
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_840_; uint8_t v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v_x_845_; lean_object* v_body_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; uint8_t v___y_888_; lean_object* v___y_889_; lean_object* v_h_x3f_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; uint8_t v___x_1007_; 
v___x_775_ = l_Lean_Syntax_getArg(v___x_618_, v___x_616_);
v___x_776_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
lean_inc(v___x_775_);
v___x_1007_ = l_Lean_Syntax_isOfKind(v___x_775_, v___x_776_);
if (v___x_1007_ == 0)
{
lean_object* v_decls_1008_; lean_object* v_decls_1009_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v_x_1014_; lean_object* v_body_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___x_1053_; lean_object* v___x_1054_; uint8_t v___x_1055_; 
lean_dec(v___x_775_);
v_decls_1008_ = l_Lean_Syntax_getArgs(v___x_618_);
lean_dec(v___x_618_);
v_decls_1009_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_1008_);
lean_dec_ref(v_decls_1008_);
v___x_1053_ = lean_box(0);
v___x_1054_ = lean_array_get(v___x_1053_, v_decls_1009_, v___x_616_);
lean_inc(v___x_1054_);
v___x_1055_ = l_Lean_Syntax_isOfKind(v___x_1054_, v___x_776_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1056_; 
lean_dec(v___x_1054_);
lean_dec_ref(v_decls_1009_);
lean_dec_ref(v_a_611_);
lean_dec(v_stx_610_);
v___x_1056_ = l_Lean_Macro_throwUnsupported___redArg(v_a_612_);
return v___x_1056_;
}
else
{
lean_object* v___x_1057_; lean_object* v_body_1058_; lean_object* v_h_x3f_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
v___x_1057_ = lean_unsigned_to_nat(3u);
v_body_1058_ = l_Lean_Syntax_getArg(v_stx_610_, v___x_1057_);
lean_dec(v_stx_610_);
v___x_1123_ = l_Lean_Syntax_getArg(v___x_1054_, v___x_616_);
v___x_1124_ = l_Lean_Syntax_isNone(v___x_1123_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; uint8_t v___x_1126_; 
v___x_1125_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1123_);
v___x_1126_ = l_Lean_Syntax_matchesNull(v___x_1123_, v___x_1125_);
if (v___x_1126_ == 0)
{
lean_object* v___x_1127_; 
lean_dec(v___x_1123_);
lean_dec(v_body_1058_);
lean_dec(v___x_1054_);
lean_dec_ref(v_decls_1009_);
lean_dec_ref(v_a_611_);
v___x_1127_ = l_Lean_Macro_throwUnsupported___redArg(v_a_612_);
return v___x_1127_;
}
else
{
lean_object* v_h_x3f_1128_; lean_object* v___x_1129_; 
v_h_x3f_1128_ = l_Lean_Syntax_getArg(v___x_1123_, v___x_616_);
lean_dec(v___x_1123_);
v___x_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1129_, 0, v_h_x3f_1128_);
v_h_x3f_1060_ = v___x_1129_;
v___y_1061_ = v_a_611_;
v___y_1062_ = v_a_612_;
goto v___jp_1059_;
}
}
else
{
lean_object* v___x_1130_; 
lean_dec(v___x_1123_);
v___x_1130_ = lean_box(0);
v_h_x3f_1060_ = v___x_1130_;
v___y_1061_ = v_a_611_;
v___y_1062_ = v_a_612_;
goto v___jp_1059_;
}
v___jp_1059_:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v_doElems_1065_; uint8_t v___x_1066_; 
v___x_1063_ = l_Lean_Syntax_getArg(v___x_1054_, v___x_617_);
v___x_1064_ = l_Lean_Syntax_getArg(v___x_1054_, v___x_1057_);
lean_dec(v___x_1054_);
v_doElems_1065_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_1066_ = l_Lean_Syntax_isIdent(v___x_1063_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1067_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_1063_);
v___x_1068_ = l_Lean_Syntax_isOfKind(v___x_1063_, v___x_1067_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; 
lean_inc_ref(v___y_1061_);
v___x_1069_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1063_, v___x_1068_, v___y_1061_, v___y_1062_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v_a_1071_; lean_object* v_ref_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_a_1070_);
v_a_1071_ = lean_ctor_get(v___x_1069_, 1);
lean_inc(v_a_1071_);
lean_dec_ref(v___x_1069_);
v_ref_1072_ = lean_ctor_get(v___y_1061_, 5);
v___x_1073_ = l_Lean_SourceInfo_fromRef(v_ref_1072_, v___x_1068_);
v___x_1074_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_1075_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1076_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_1077_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_1078_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29));
lean_inc(v___x_1073_);
v___x_1079_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1073_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25);
lean_inc(v___x_1073_);
v___x_1081_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1073_);
lean_ctor_set(v___x_1081_, 1, v___x_1075_);
lean_ctor_set(v___x_1081_, 2, v___x_1080_);
v___x_1082_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc(v_a_1070_);
lean_inc_ref(v___x_1081_);
lean_inc(v___x_1073_);
v___x_1083_ = l_Lean_Syntax_node2(v___x_1073_, v___x_1082_, v___x_1081_, v_a_1070_);
lean_inc(v___x_1073_);
v___x_1084_ = l_Lean_Syntax_node1(v___x_1073_, v___x_1075_, v___x_1083_);
v___x_1085_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38));
lean_inc(v___x_1073_);
v___x_1086_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1073_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_1088_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_1089_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41));
lean_inc(v___x_1073_);
v___x_1090_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1073_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
lean_inc(v___x_1073_);
v___x_1091_ = l_Lean_Syntax_node1(v___x_1073_, v___x_1075_, v___x_1063_);
lean_inc(v___x_1073_);
v___x_1092_ = l_Lean_Syntax_node1(v___x_1073_, v___x_1075_, v___x_1091_);
v___x_1093_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49));
lean_inc(v___x_1073_);
v___x_1094_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1073_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
lean_inc(v___x_1073_);
v___x_1095_ = l_Lean_Syntax_node4(v___x_1073_, v___x_1088_, v___x_1090_, v___x_1092_, v___x_1094_, v_body_1058_);
lean_inc(v___x_1073_);
v___x_1096_ = l_Lean_Syntax_node1(v___x_1073_, v___x_1075_, v___x_1095_);
lean_inc(v___x_1073_);
v___x_1097_ = l_Lean_Syntax_node1(v___x_1073_, v___x_1087_, v___x_1096_);
lean_inc_ref_n(v___x_1081_, 3);
lean_inc(v___x_1073_);
v___x_1098_ = l_Lean_Syntax_node7(v___x_1073_, v___x_1077_, v___x_1079_, v___x_1081_, v___x_1081_, v___x_1081_, v___x_1084_, v___x_1086_, v___x_1097_);
lean_inc(v___x_1073_);
v___x_1099_ = l_Lean_Syntax_node2(v___x_1073_, v___x_1076_, v___x_1098_, v___x_1081_);
lean_inc(v___x_1073_);
v___x_1100_ = l_Lean_Syntax_node1(v___x_1073_, v___x_1075_, v___x_1099_);
v___x_1101_ = l_Lean_Syntax_node1(v___x_1073_, v___x_1074_, v___x_1100_);
v___y_1011_ = v___x_1064_;
v___y_1012_ = v_h_x3f_1060_;
v___y_1013_ = v_doElems_1065_;
v_x_1014_ = v_a_1070_;
v_body_1015_ = v___x_1101_;
v___y_1016_ = v___y_1061_;
v___y_1017_ = v_a_1071_;
goto v___jp_1010_;
}
else
{
lean_object* v_a_1102_; lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
lean_dec(v___x_1064_);
lean_dec(v___x_1063_);
lean_dec_ref(v___y_1061_);
lean_dec(v_h_x3f_1060_);
lean_dec(v_body_1058_);
lean_dec_ref(v_decls_1009_);
v_a_1102_ = lean_ctor_get(v___x_1069_, 0);
v_a_1103_ = lean_ctor_get(v___x_1069_, 1);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1069_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_inc(v_a_1102_);
lean_dec(v___x_1069_);
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
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1102_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v_a_1103_);
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
lean_object* v___x_1111_; 
lean_inc_ref(v___y_1061_);
v___x_1111_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1063_, v___x_1066_, v___y_1061_, v___y_1062_);
lean_dec(v___x_1063_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v_a_1112_; lean_object* v_a_1113_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_a_1112_);
v_a_1113_ = lean_ctor_get(v___x_1111_, 1);
lean_inc(v_a_1113_);
lean_dec_ref(v___x_1111_);
v___y_1011_ = v___x_1064_;
v___y_1012_ = v_h_x3f_1060_;
v___y_1013_ = v_doElems_1065_;
v_x_1014_ = v_a_1112_;
v_body_1015_ = v_body_1058_;
v___y_1016_ = v___y_1061_;
v___y_1017_ = v_a_1113_;
goto v___jp_1010_;
}
else
{
lean_object* v_a_1114_; lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
lean_dec(v___x_1064_);
lean_dec_ref(v___y_1061_);
lean_dec(v_h_x3f_1060_);
lean_dec(v_body_1058_);
lean_dec_ref(v_decls_1009_);
v_a_1114_ = lean_ctor_get(v___x_1111_, 0);
v_a_1115_ = lean_ctor_get(v___x_1111_, 1);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1111_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_inc(v_a_1114_);
lean_dec(v___x_1111_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1114_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_a_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
}
else
{
v___y_1011_ = v___x_1064_;
v___y_1012_ = v_h_x3f_1060_;
v___y_1013_ = v_doElems_1065_;
v_x_1014_ = v___x_1063_;
v_body_1015_ = v_body_1058_;
v___y_1016_ = v___y_1061_;
v___y_1017_ = v___y_1062_;
goto v___jp_1010_;
}
}
}
v___jp_1010_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1018_ = lean_array_get_size(v_decls_1009_);
v___x_1019_ = l_Array_toSubarray___redArg(v_decls_1009_, v___x_617_, v___x_1018_);
v___x_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___y_1013_);
lean_ctor_set(v___x_1020_, 1, v_body_1015_);
lean_inc_ref(v___y_1016_);
v___x_1021_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_1007_, v___x_1019_, v___x_1020_, v___y_1016_, v___y_1017_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v_a_1023_; lean_object* v_fst_1024_; lean_object* v_snd_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1043_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
v_a_1023_ = lean_ctor_get(v___x_1021_, 1);
lean_inc(v_a_1023_);
lean_dec_ref(v___x_1021_);
v_fst_1024_ = lean_ctor_get(v_a_1022_, 0);
v_snd_1025_ = lean_ctor_get(v_a_1022_, 1);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_a_1022_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1027_ = v_a_1022_;
v_isShared_1028_ = v_isSharedCheck_1043_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_snd_1025_);
lean_inc(v_fst_1024_);
lean_dec(v_a_1022_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1043_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v_ref_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1034_; 
v_ref_1029_ = lean_ctor_get(v___y_1016_, 5);
lean_inc(v_ref_1029_);
lean_dec_ref(v___y_1016_);
v___x_1030_ = l_Lean_SourceInfo_fromRef(v_ref_1029_, v___x_1007_);
lean_dec(v_ref_1029_);
v___x_1031_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_1032_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
lean_inc(v___x_1030_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set_tag(v___x_1027_, 2);
lean_ctor_set(v___x_1027_, 1, v___x_1032_);
lean_ctor_set(v___x_1027_, 0, v___x_1030_);
v___x_1034_ = v___x_1027_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v___x_1032_);
v___x_1034_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1036_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25);
if (lean_obj_tag(v___y_1012_) == 1)
{
lean_object* v_val_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v_val_1037_ = lean_ctor_get(v___y_1012_, 0);
lean_inc(v_val_1037_);
lean_dec_ref(v___y_1012_);
v___x_1038_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
lean_inc(v___x_1030_);
v___x_1039_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1030_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = l_Array_mkArray2___redArg(v_val_1037_, v___x_1039_);
v___y_977_ = v___x_1035_;
v___y_978_ = v___x_1030_;
v___y_979_ = v_fst_1024_;
v___y_980_ = v_x_1014_;
v___y_981_ = v___y_1011_;
v___y_982_ = v___x_1036_;
v___y_983_ = v_a_1023_;
v___y_984_ = v___x_1031_;
v___y_985_ = v___x_1034_;
v___y_986_ = v_snd_1025_;
v___y_987_ = v___x_1040_;
goto v___jp_976_;
}
else
{
lean_object* v___x_1041_; 
lean_dec(v___y_1012_);
v___x_1041_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
v___y_977_ = v___x_1035_;
v___y_978_ = v___x_1030_;
v___y_979_ = v_fst_1024_;
v___y_980_ = v_x_1014_;
v___y_981_ = v___y_1011_;
v___y_982_ = v___x_1036_;
v___y_983_ = v_a_1023_;
v___y_984_ = v___x_1031_;
v___y_985_ = v___x_1034_;
v___y_986_ = v_snd_1025_;
v___y_987_ = v___x_1041_;
goto v___jp_976_;
}
}
}
}
else
{
lean_object* v_a_1044_; lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
lean_dec_ref(v___y_1016_);
lean_dec(v_x_1014_);
lean_dec(v___y_1012_);
lean_dec(v___y_1011_);
v_a_1044_ = lean_ctor_get(v___x_1021_, 0);
v_a_1045_ = lean_ctor_get(v___x_1021_, 1);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_1021_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_inc(v_a_1044_);
lean_dec(v___x_1021_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1044_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
}
else
{
lean_object* v___x_1131_; uint8_t v___x_1132_; 
v___x_1131_ = l_Lean_Syntax_getArg(v___x_775_, v___x_616_);
v___x_1132_ = l_Lean_Syntax_isNone(v___x_1131_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; uint8_t v___x_1134_; 
v___x_1133_ = lean_unsigned_to_nat(2u);
v___x_1134_ = l_Lean_Syntax_matchesNull(v___x_1131_, v___x_1133_);
if (v___x_1134_ == 0)
{
lean_object* v_decls_1135_; lean_object* v_decls_1136_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v_x_1141_; lean_object* v_body_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___x_1180_; lean_object* v___x_1181_; uint8_t v___x_1182_; 
lean_dec(v___x_775_);
v_decls_1135_ = l_Lean_Syntax_getArgs(v___x_618_);
lean_dec(v___x_618_);
v_decls_1136_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_1135_);
lean_dec_ref(v_decls_1135_);
v___x_1180_ = lean_box(0);
v___x_1181_ = lean_array_get(v___x_1180_, v_decls_1136_, v___x_616_);
lean_inc(v___x_1181_);
v___x_1182_ = l_Lean_Syntax_isOfKind(v___x_1181_, v___x_776_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; 
lean_dec(v___x_1181_);
lean_dec_ref(v_decls_1136_);
lean_dec_ref(v_a_611_);
lean_dec(v_stx_610_);
v___x_1183_ = l_Lean_Macro_throwUnsupported___redArg(v_a_612_);
return v___x_1183_;
}
else
{
lean_object* v___x_1184_; lean_object* v_body_1185_; lean_object* v_h_x3f_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v___x_1184_ = lean_unsigned_to_nat(3u);
v_body_1185_ = l_Lean_Syntax_getArg(v_stx_610_, v___x_1184_);
lean_dec(v_stx_610_);
v___x_1250_ = l_Lean_Syntax_getArg(v___x_1181_, v___x_616_);
v___x_1251_ = l_Lean_Syntax_isNone(v___x_1250_);
if (v___x_1251_ == 0)
{
uint8_t v___x_1252_; 
lean_inc(v___x_1250_);
v___x_1252_ = l_Lean_Syntax_matchesNull(v___x_1250_, v___x_1133_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; 
lean_dec(v___x_1250_);
lean_dec(v_body_1185_);
lean_dec(v___x_1181_);
lean_dec_ref(v_decls_1136_);
lean_dec_ref(v_a_611_);
v___x_1253_ = l_Lean_Macro_throwUnsupported___redArg(v_a_612_);
return v___x_1253_;
}
else
{
lean_object* v_h_x3f_1254_; lean_object* v___x_1255_; 
v_h_x3f_1254_ = l_Lean_Syntax_getArg(v___x_1250_, v___x_616_);
lean_dec(v___x_1250_);
v___x_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1255_, 0, v_h_x3f_1254_);
v_h_x3f_1187_ = v___x_1255_;
v___y_1188_ = v_a_611_;
v___y_1189_ = v_a_612_;
goto v___jp_1186_;
}
}
else
{
lean_object* v___x_1256_; 
lean_dec(v___x_1250_);
v___x_1256_ = lean_box(0);
v_h_x3f_1187_ = v___x_1256_;
v___y_1188_ = v_a_611_;
v___y_1189_ = v_a_612_;
goto v___jp_1186_;
}
v___jp_1186_:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v_doElems_1192_; uint8_t v___x_1193_; 
v___x_1190_ = l_Lean_Syntax_getArg(v___x_1181_, v___x_617_);
v___x_1191_ = l_Lean_Syntax_getArg(v___x_1181_, v___x_1184_);
lean_dec(v___x_1181_);
v_doElems_1192_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_1193_ = l_Lean_Syntax_isIdent(v___x_1190_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; uint8_t v___x_1195_; 
v___x_1194_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_1190_);
v___x_1195_ = l_Lean_Syntax_isOfKind(v___x_1190_, v___x_1194_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1196_; 
lean_inc_ref(v___y_1188_);
v___x_1196_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1190_, v___x_1195_, v___y_1188_, v___y_1189_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v_a_1197_; lean_object* v_a_1198_; lean_object* v_ref_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_a_1197_);
v_a_1198_ = lean_ctor_get(v___x_1196_, 1);
lean_inc(v_a_1198_);
lean_dec_ref(v___x_1196_);
v_ref_1199_ = lean_ctor_get(v___y_1188_, 5);
v___x_1200_ = l_Lean_SourceInfo_fromRef(v_ref_1199_, v___x_1195_);
v___x_1201_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_1202_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1203_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_1204_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_1205_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29));
lean_inc(v___x_1200_);
v___x_1206_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1200_);
lean_ctor_set(v___x_1206_, 1, v___x_1205_);
v___x_1207_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25);
lean_inc(v___x_1200_);
v___x_1208_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1200_);
lean_ctor_set(v___x_1208_, 1, v___x_1202_);
lean_ctor_set(v___x_1208_, 2, v___x_1207_);
v___x_1209_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc(v_a_1197_);
lean_inc_ref(v___x_1208_);
lean_inc(v___x_1200_);
v___x_1210_ = l_Lean_Syntax_node2(v___x_1200_, v___x_1209_, v___x_1208_, v_a_1197_);
lean_inc(v___x_1200_);
v___x_1211_ = l_Lean_Syntax_node1(v___x_1200_, v___x_1202_, v___x_1210_);
v___x_1212_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38));
lean_inc(v___x_1200_);
v___x_1213_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1200_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
v___x_1214_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_1215_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_1216_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41));
lean_inc(v___x_1200_);
v___x_1217_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1200_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
lean_inc(v___x_1200_);
v___x_1218_ = l_Lean_Syntax_node1(v___x_1200_, v___x_1202_, v___x_1190_);
lean_inc(v___x_1200_);
v___x_1219_ = l_Lean_Syntax_node1(v___x_1200_, v___x_1202_, v___x_1218_);
v___x_1220_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49));
lean_inc(v___x_1200_);
v___x_1221_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1200_);
lean_ctor_set(v___x_1221_, 1, v___x_1220_);
lean_inc(v___x_1200_);
v___x_1222_ = l_Lean_Syntax_node4(v___x_1200_, v___x_1215_, v___x_1217_, v___x_1219_, v___x_1221_, v_body_1185_);
lean_inc(v___x_1200_);
v___x_1223_ = l_Lean_Syntax_node1(v___x_1200_, v___x_1202_, v___x_1222_);
lean_inc(v___x_1200_);
v___x_1224_ = l_Lean_Syntax_node1(v___x_1200_, v___x_1214_, v___x_1223_);
lean_inc_ref_n(v___x_1208_, 3);
lean_inc(v___x_1200_);
v___x_1225_ = l_Lean_Syntax_node7(v___x_1200_, v___x_1204_, v___x_1206_, v___x_1208_, v___x_1208_, v___x_1208_, v___x_1211_, v___x_1213_, v___x_1224_);
lean_inc(v___x_1200_);
v___x_1226_ = l_Lean_Syntax_node2(v___x_1200_, v___x_1203_, v___x_1225_, v___x_1208_);
lean_inc(v___x_1200_);
v___x_1227_ = l_Lean_Syntax_node1(v___x_1200_, v___x_1202_, v___x_1226_);
v___x_1228_ = l_Lean_Syntax_node1(v___x_1200_, v___x_1201_, v___x_1227_);
v___y_1138_ = v_doElems_1192_;
v___y_1139_ = v___x_1191_;
v___y_1140_ = v_h_x3f_1187_;
v_x_1141_ = v_a_1197_;
v_body_1142_ = v___x_1228_;
v___y_1143_ = v___y_1188_;
v___y_1144_ = v_a_1198_;
goto v___jp_1137_;
}
else
{
lean_object* v_a_1229_; lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1237_; 
lean_dec(v___x_1191_);
lean_dec(v___x_1190_);
lean_dec_ref(v___y_1188_);
lean_dec(v_h_x3f_1187_);
lean_dec(v_body_1185_);
lean_dec_ref(v_decls_1136_);
v_a_1229_ = lean_ctor_get(v___x_1196_, 0);
v_a_1230_ = lean_ctor_get(v___x_1196_, 1);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1232_ = v___x_1196_;
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_inc(v_a_1229_);
lean_dec(v___x_1196_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1229_);
lean_ctor_set(v_reuseFailAlloc_1236_, 1, v_a_1230_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
else
{
lean_object* v___x_1238_; 
lean_inc_ref(v___y_1188_);
v___x_1238_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1190_, v___x_1193_, v___y_1188_, v___y_1189_);
lean_dec(v___x_1190_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v_a_1240_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
v_a_1240_ = lean_ctor_get(v___x_1238_, 1);
lean_inc(v_a_1240_);
lean_dec_ref(v___x_1238_);
v___y_1138_ = v_doElems_1192_;
v___y_1139_ = v___x_1191_;
v___y_1140_ = v_h_x3f_1187_;
v_x_1141_ = v_a_1239_;
v_body_1142_ = v_body_1185_;
v___y_1143_ = v___y_1188_;
v___y_1144_ = v_a_1240_;
goto v___jp_1137_;
}
else
{
lean_object* v_a_1241_; lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
lean_dec(v___x_1191_);
lean_dec_ref(v___y_1188_);
lean_dec(v_h_x3f_1187_);
lean_dec(v_body_1185_);
lean_dec_ref(v_decls_1136_);
v_a_1241_ = lean_ctor_get(v___x_1238_, 0);
v_a_1242_ = lean_ctor_get(v___x_1238_, 1);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1244_ = v___x_1238_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_inc(v_a_1241_);
lean_dec(v___x_1238_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1241_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v_a_1242_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
}
else
{
v___y_1138_ = v_doElems_1192_;
v___y_1139_ = v___x_1191_;
v___y_1140_ = v_h_x3f_1187_;
v_x_1141_ = v___x_1190_;
v_body_1142_ = v_body_1185_;
v___y_1143_ = v___y_1188_;
v___y_1144_ = v___y_1189_;
goto v___jp_1137_;
}
}
}
v___jp_1137_:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1145_ = lean_array_get_size(v_decls_1136_);
v___x_1146_ = l_Array_toSubarray___redArg(v_decls_1136_, v___x_617_, v___x_1145_);
v___x_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___y_1138_);
lean_ctor_set(v___x_1147_, 1, v_body_1142_);
lean_inc_ref(v___y_1143_);
v___x_1148_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_1134_, v___x_1146_, v___x_1147_, v___y_1143_, v___y_1144_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; lean_object* v_a_1150_; lean_object* v_fst_1151_; lean_object* v_snd_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1170_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
lean_inc(v_a_1149_);
v_a_1150_ = lean_ctor_get(v___x_1148_, 1);
lean_inc(v_a_1150_);
lean_dec_ref(v___x_1148_);
v_fst_1151_ = lean_ctor_get(v_a_1149_, 0);
v_snd_1152_ = lean_ctor_get(v_a_1149_, 1);
v_isSharedCheck_1170_ = !lean_is_exclusive(v_a_1149_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1154_ = v_a_1149_;
v_isShared_1155_ = v_isSharedCheck_1170_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_snd_1152_);
lean_inc(v_fst_1151_);
lean_dec(v_a_1149_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1170_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v_ref_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1161_; 
v_ref_1156_ = lean_ctor_get(v___y_1143_, 5);
lean_inc(v_ref_1156_);
lean_dec_ref(v___y_1143_);
v___x_1157_ = l_Lean_SourceInfo_fromRef(v_ref_1156_, v___x_1134_);
lean_dec(v_ref_1156_);
v___x_1158_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_1159_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
lean_inc(v___x_1157_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set_tag(v___x_1154_, 2);
lean_ctor_set(v___x_1154_, 1, v___x_1159_);
lean_ctor_set(v___x_1154_, 0, v___x_1157_);
v___x_1161_ = v___x_1154_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1157_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1163_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25);
if (lean_obj_tag(v___y_1140_) == 1)
{
lean_object* v_val_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v_val_1164_ = lean_ctor_get(v___y_1140_, 0);
lean_inc(v_val_1164_);
lean_dec_ref(v___y_1140_);
v___x_1165_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
lean_inc(v___x_1157_);
v___x_1166_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1157_);
lean_ctor_set(v___x_1166_, 1, v___x_1165_);
v___x_1167_ = l_Array_mkArray2___redArg(v_val_1164_, v___x_1166_);
v___y_778_ = v___x_1162_;
v___y_779_ = v___x_1163_;
v___y_780_ = v___x_1158_;
v___y_781_ = v_fst_1151_;
v___y_782_ = v___x_1161_;
v___y_783_ = v___y_1139_;
v___y_784_ = v___x_1157_;
v___y_785_ = v_a_1150_;
v___y_786_ = v_snd_1152_;
v___y_787_ = v_x_1141_;
v___y_788_ = v___x_1167_;
goto v___jp_777_;
}
else
{
lean_object* v___x_1168_; 
lean_dec(v___y_1140_);
v___x_1168_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
v___y_778_ = v___x_1162_;
v___y_779_ = v___x_1163_;
v___y_780_ = v___x_1158_;
v___y_781_ = v_fst_1151_;
v___y_782_ = v___x_1161_;
v___y_783_ = v___y_1139_;
v___y_784_ = v___x_1157_;
v___y_785_ = v_a_1150_;
v___y_786_ = v_snd_1152_;
v___y_787_ = v_x_1141_;
v___y_788_ = v___x_1168_;
goto v___jp_777_;
}
}
}
}
else
{
lean_object* v_a_1171_; lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
lean_dec_ref(v___y_1143_);
lean_dec(v_x_1141_);
lean_dec(v___y_1140_);
lean_dec(v___y_1139_);
v_a_1171_ = lean_ctor_get(v___x_1148_, 0);
v_a_1172_ = lean_ctor_get(v___x_1148_, 1);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_1148_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_inc(v_a_1171_);
lean_dec(v___x_1148_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1171_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v_a_1172_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
}
else
{
v___y_954_ = v_a_611_;
v___y_955_ = v_a_612_;
goto v___jp_953_;
}
}
else
{
lean_dec(v___x_1131_);
v___y_954_ = v_a_611_;
v___y_955_ = v_a_612_;
goto v___jp_953_;
}
}
v___jp_777_:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
lean_inc_ref(v___y_779_);
v___x_789_ = l_Array_append___redArg(v___y_779_, v___y_788_);
lean_dec_ref(v___y_788_);
lean_inc(v___y_778_);
lean_inc(v___y_784_);
v___x_790_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_790_, 0, v___y_784_);
lean_ctor_set(v___x_790_, 1, v___y_778_);
lean_ctor_set(v___x_790_, 2, v___x_789_);
v___x_791_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
lean_inc(v___y_784_);
v___x_792_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_792_, 0, v___y_784_);
lean_ctor_set(v___x_792_, 1, v___x_791_);
lean_inc(v___y_784_);
v___x_793_ = l_Lean_Syntax_node4(v___y_784_, v___x_776_, v___x_790_, v___y_787_, v___x_792_, v___y_783_);
lean_inc(v___y_778_);
lean_inc(v___y_784_);
v___x_794_ = l_Lean_Syntax_node1(v___y_784_, v___y_778_, v___x_793_);
v___x_795_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75));
lean_inc(v___y_784_);
v___x_796_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_796_, 0, v___y_784_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
lean_inc_ref(v___x_796_);
lean_inc(v___y_784_);
v___x_797_ = l_Lean_Syntax_node4(v___y_784_, v___x_613_, v___y_782_, v___x_794_, v___x_796_, v___y_786_);
lean_inc_ref(v___y_779_);
lean_inc(v___y_778_);
lean_inc(v___y_784_);
v___x_798_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_798_, 0, v___y_784_);
lean_ctor_set(v___x_798_, 1, v___y_778_);
lean_ctor_set(v___x_798_, 2, v___y_779_);
lean_inc(v___y_784_);
v___x_799_ = l_Lean_Syntax_node2(v___y_784_, v___y_780_, v___x_797_, v___x_798_);
v___x_800_ = lean_array_push(v___y_781_, v___x_799_);
v___x_801_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_802_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_803_ = l_Array_append___redArg(v___y_779_, v___x_800_);
lean_dec_ref(v___x_800_);
lean_inc(v___y_784_);
v___x_804_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_804_, 0, v___y_784_);
lean_ctor_set(v___x_804_, 1, v___y_778_);
lean_ctor_set(v___x_804_, 2, v___x_803_);
lean_inc(v___y_784_);
v___x_805_ = l_Lean_Syntax_node1(v___y_784_, v___x_802_, v___x_804_);
v___x_806_ = l_Lean_Syntax_node2(v___y_784_, v___x_801_, v___x_796_, v___x_805_);
v___x_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
lean_ctor_set(v___x_807_, 1, v___y_785_);
return v___x_807_;
}
v___jp_808_:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
lean_inc_ref(v___y_816_);
v___x_820_ = l_Array_append___redArg(v___y_816_, v___y_819_);
lean_dec_ref(v___y_819_);
lean_inc(v___y_810_);
lean_inc(v___y_809_);
v___x_821_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_821_, 0, v___y_809_);
lean_ctor_set(v___x_821_, 1, v___y_810_);
lean_ctor_set(v___x_821_, 2, v___x_820_);
v___x_822_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
lean_inc(v___y_809_);
v___x_823_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_823_, 0, v___y_809_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
lean_inc(v___y_809_);
v___x_824_ = l_Lean_Syntax_node4(v___y_809_, v___x_776_, v___x_821_, v___y_817_, v___x_823_, v___y_814_);
lean_inc(v___y_810_);
lean_inc(v___y_809_);
v___x_825_ = l_Lean_Syntax_node1(v___y_809_, v___y_810_, v___x_824_);
v___x_826_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75));
lean_inc(v___y_809_);
v___x_827_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_827_, 0, v___y_809_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
lean_inc_ref(v___x_827_);
lean_inc(v___y_809_);
v___x_828_ = l_Lean_Syntax_node4(v___y_809_, v___x_613_, v___y_818_, v___x_825_, v___x_827_, v___y_813_);
lean_inc_ref(v___y_816_);
lean_inc(v___y_810_);
lean_inc(v___y_809_);
v___x_829_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_829_, 0, v___y_809_);
lean_ctor_set(v___x_829_, 1, v___y_810_);
lean_ctor_set(v___x_829_, 2, v___y_816_);
lean_inc(v___y_809_);
v___x_830_ = l_Lean_Syntax_node2(v___y_809_, v___y_815_, v___x_828_, v___x_829_);
v___x_831_ = lean_array_push(v___y_812_, v___x_830_);
v___x_832_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_833_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_834_ = l_Array_append___redArg(v___y_816_, v___x_831_);
lean_dec_ref(v___x_831_);
lean_inc(v___y_809_);
v___x_835_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_835_, 0, v___y_809_);
lean_ctor_set(v___x_835_, 1, v___y_810_);
lean_ctor_set(v___x_835_, 2, v___x_834_);
lean_inc(v___y_809_);
v___x_836_ = l_Lean_Syntax_node1(v___y_809_, v___x_833_, v___x_835_);
v___x_837_ = l_Lean_Syntax_node2(v___y_809_, v___x_832_, v___x_827_, v___x_836_);
v___x_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
lean_ctor_set(v___x_838_, 1, v___y_811_);
return v___x_838_;
}
v___jp_839_:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_849_ = lean_array_get_size(v___y_844_);
v___x_850_ = l_Array_toSubarray___redArg(v___y_844_, v___x_617_, v___x_849_);
v___x_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_851_, 0, v___y_842_);
lean_ctor_set(v___x_851_, 1, v_body_846_);
lean_inc_ref(v___y_847_);
v___x_852_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___y_841_, v___x_850_, v___x_851_, v___y_847_, v___y_848_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v_a_854_; lean_object* v_fst_855_; lean_object* v_snd_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_874_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
v_a_854_ = lean_ctor_get(v___x_852_, 1);
lean_inc(v_a_854_);
lean_dec_ref(v___x_852_);
v_fst_855_ = lean_ctor_get(v_a_853_, 0);
v_snd_856_ = lean_ctor_get(v_a_853_, 1);
v_isSharedCheck_874_ = !lean_is_exclusive(v_a_853_);
if (v_isSharedCheck_874_ == 0)
{
v___x_858_ = v_a_853_;
v_isShared_859_ = v_isSharedCheck_874_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_snd_856_);
lean_inc(v_fst_855_);
lean_dec(v_a_853_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_874_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v_ref_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_865_; 
v_ref_860_ = lean_ctor_get(v___y_847_, 5);
lean_inc(v_ref_860_);
lean_dec_ref(v___y_847_);
v___x_861_ = l_Lean_SourceInfo_fromRef(v_ref_860_, v___y_841_);
lean_dec(v_ref_860_);
v___x_862_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_863_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
lean_inc(v___x_861_);
if (v_isShared_859_ == 0)
{
lean_ctor_set_tag(v___x_858_, 2);
lean_ctor_set(v___x_858_, 1, v___x_863_);
lean_ctor_set(v___x_858_, 0, v___x_861_);
v___x_865_ = v___x_858_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_861_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v___x_863_);
v___x_865_ = v_reuseFailAlloc_873_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_867_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25);
if (lean_obj_tag(v___y_843_) == 1)
{
lean_object* v_val_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v_val_868_ = lean_ctor_get(v___y_843_, 0);
lean_inc(v_val_868_);
lean_dec_ref(v___y_843_);
v___x_869_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
lean_inc(v___x_861_);
v___x_870_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_861_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = l_Array_mkArray2___redArg(v_val_868_, v___x_870_);
v___y_809_ = v___x_861_;
v___y_810_ = v___x_866_;
v___y_811_ = v_a_854_;
v___y_812_ = v_fst_855_;
v___y_813_ = v_snd_856_;
v___y_814_ = v___y_840_;
v___y_815_ = v___x_862_;
v___y_816_ = v___x_867_;
v___y_817_ = v_x_845_;
v___y_818_ = v___x_865_;
v___y_819_ = v___x_871_;
goto v___jp_808_;
}
else
{
lean_object* v___x_872_; 
lean_dec(v___y_843_);
v___x_872_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
v___y_809_ = v___x_861_;
v___y_810_ = v___x_866_;
v___y_811_ = v_a_854_;
v___y_812_ = v_fst_855_;
v___y_813_ = v_snd_856_;
v___y_814_ = v___y_840_;
v___y_815_ = v___x_862_;
v___y_816_ = v___x_867_;
v___y_817_ = v_x_845_;
v___y_818_ = v___x_865_;
v___y_819_ = v___x_872_;
goto v___jp_808_;
}
}
}
}
else
{
lean_object* v_a_875_; lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_dec_ref(v___y_847_);
lean_dec(v_x_845_);
lean_dec(v___y_843_);
lean_dec(v___y_840_);
v_a_875_ = lean_ctor_get(v___x_852_, 0);
v_a_876_ = lean_ctor_get(v___x_852_, 1);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_852_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_inc(v_a_875_);
lean_dec(v___x_852_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_875_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
v___jp_884_:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v_doElems_895_; uint8_t v___x_896_; 
v___x_893_ = l_Lean_Syntax_getArg(v___y_885_, v___x_617_);
v___x_894_ = l_Lean_Syntax_getArg(v___y_885_, v___y_887_);
lean_dec(v___y_885_);
v_doElems_895_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_896_ = l_Lean_Syntax_isIdent(v___x_893_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; uint8_t v___x_898_; 
v___x_897_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_893_);
v___x_898_ = l_Lean_Syntax_isOfKind(v___x_893_, v___x_897_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; 
lean_inc_ref(v___y_891_);
v___x_899_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_893_, v___y_888_, v___y_891_, v___y_892_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v_a_901_; lean_object* v_ref_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
v_a_901_ = lean_ctor_get(v___x_899_, 1);
lean_inc(v_a_901_);
lean_dec_ref(v___x_899_);
v_ref_902_ = lean_ctor_get(v___y_891_, 5);
v___x_903_ = l_Lean_SourceInfo_fromRef(v_ref_902_, v___y_888_);
v___x_904_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_905_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_906_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_907_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_908_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29));
lean_inc(v___x_903_);
v___x_909_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_903_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25);
lean_inc(v___x_903_);
v___x_911_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_911_, 0, v___x_903_);
lean_ctor_set(v___x_911_, 1, v___x_905_);
lean_ctor_set(v___x_911_, 2, v___x_910_);
v___x_912_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc(v_a_900_);
lean_inc_ref(v___x_911_);
lean_inc(v___x_903_);
v___x_913_ = l_Lean_Syntax_node2(v___x_903_, v___x_912_, v___x_911_, v_a_900_);
lean_inc(v___x_903_);
v___x_914_ = l_Lean_Syntax_node1(v___x_903_, v___x_905_, v___x_913_);
v___x_915_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38));
lean_inc(v___x_903_);
v___x_916_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_903_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_918_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_919_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41));
lean_inc(v___x_903_);
v___x_920_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_903_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
lean_inc(v___x_903_);
v___x_921_ = l_Lean_Syntax_node1(v___x_903_, v___x_905_, v___x_893_);
lean_inc(v___x_903_);
v___x_922_ = l_Lean_Syntax_node1(v___x_903_, v___x_905_, v___x_921_);
v___x_923_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49));
lean_inc(v___x_903_);
v___x_924_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_903_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
lean_inc(v___x_903_);
v___x_925_ = l_Lean_Syntax_node4(v___x_903_, v___x_918_, v___x_920_, v___x_922_, v___x_924_, v___y_886_);
lean_inc(v___x_903_);
v___x_926_ = l_Lean_Syntax_node1(v___x_903_, v___x_905_, v___x_925_);
lean_inc(v___x_903_);
v___x_927_ = l_Lean_Syntax_node1(v___x_903_, v___x_917_, v___x_926_);
lean_inc_ref_n(v___x_911_, 3);
lean_inc(v___x_903_);
v___x_928_ = l_Lean_Syntax_node7(v___x_903_, v___x_907_, v___x_909_, v___x_911_, v___x_911_, v___x_911_, v___x_914_, v___x_916_, v___x_927_);
lean_inc(v___x_903_);
v___x_929_ = l_Lean_Syntax_node2(v___x_903_, v___x_906_, v___x_928_, v___x_911_);
lean_inc(v___x_903_);
v___x_930_ = l_Lean_Syntax_node1(v___x_903_, v___x_905_, v___x_929_);
v___x_931_ = l_Lean_Syntax_node1(v___x_903_, v___x_904_, v___x_930_);
v___y_840_ = v___x_894_;
v___y_841_ = v___y_888_;
v___y_842_ = v_doElems_895_;
v___y_843_ = v_h_x3f_890_;
v___y_844_ = v___y_889_;
v_x_845_ = v_a_900_;
v_body_846_ = v___x_931_;
v___y_847_ = v___y_891_;
v___y_848_ = v_a_901_;
goto v___jp_839_;
}
else
{
lean_object* v_a_932_; lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
lean_dec(v___x_894_);
lean_dec(v___x_893_);
lean_dec_ref(v___y_891_);
lean_dec(v_h_x3f_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_886_);
v_a_932_ = lean_ctor_get(v___x_899_, 0);
v_a_933_ = lean_ctor_get(v___x_899_, 1);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_940_ == 0)
{
v___x_935_ = v___x_899_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_inc(v_a_932_);
lean_dec(v___x_899_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_932_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v_a_933_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
else
{
lean_object* v___x_941_; 
lean_inc_ref(v___y_891_);
v___x_941_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_893_, v___y_888_, v___y_891_, v___y_892_);
lean_dec(v___x_893_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; lean_object* v_a_943_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_a_942_);
v_a_943_ = lean_ctor_get(v___x_941_, 1);
lean_inc(v_a_943_);
lean_dec_ref(v___x_941_);
v___y_840_ = v___x_894_;
v___y_841_ = v___y_888_;
v___y_842_ = v_doElems_895_;
v___y_843_ = v_h_x3f_890_;
v___y_844_ = v___y_889_;
v_x_845_ = v_a_942_;
v_body_846_ = v___y_886_;
v___y_847_ = v___y_891_;
v___y_848_ = v_a_943_;
goto v___jp_839_;
}
else
{
lean_object* v_a_944_; lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
lean_dec(v___x_894_);
lean_dec_ref(v___y_891_);
lean_dec(v_h_x3f_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_886_);
v_a_944_ = lean_ctor_get(v___x_941_, 0);
v_a_945_ = lean_ctor_get(v___x_941_, 1);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_941_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_inc(v_a_944_);
lean_dec(v___x_941_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_944_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_a_945_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
}
else
{
v___y_840_ = v___x_894_;
v___y_841_ = v___y_888_;
v___y_842_ = v_doElems_895_;
v___y_843_ = v_h_x3f_890_;
v___y_844_ = v___y_889_;
v_x_845_ = v___x_893_;
v_body_846_ = v___y_886_;
v___y_847_ = v___y_891_;
v___y_848_ = v___y_892_;
goto v___jp_839_;
}
}
v___jp_953_:
{
lean_object* v___x_956_; lean_object* v___x_957_; uint8_t v___x_958_; 
v___x_956_ = l_Lean_Syntax_getArg(v___x_775_, v___x_617_);
lean_dec(v___x_775_);
v___x_957_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__16));
v___x_958_ = l_Lean_Syntax_isOfKind(v___x_956_, v___x_957_);
if (v___x_958_ == 0)
{
lean_object* v_decls_959_; lean_object* v_decls_960_; lean_object* v___x_961_; lean_object* v___x_962_; uint8_t v___x_963_; 
v_decls_959_ = l_Lean_Syntax_getArgs(v___x_618_);
lean_dec(v___x_618_);
v_decls_960_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_959_);
lean_dec_ref(v_decls_959_);
v___x_961_ = lean_box(0);
v___x_962_ = lean_array_get(v___x_961_, v_decls_960_, v___x_616_);
lean_inc(v___x_962_);
v___x_963_ = l_Lean_Syntax_isOfKind(v___x_962_, v___x_776_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; 
lean_dec(v___x_962_);
lean_dec_ref(v_decls_960_);
lean_dec_ref(v___y_954_);
lean_dec(v_stx_610_);
v___x_964_ = l_Lean_Macro_throwUnsupported___redArg(v___y_955_);
return v___x_964_;
}
else
{
lean_object* v___x_965_; lean_object* v_body_966_; lean_object* v___x_967_; uint8_t v___x_968_; 
v___x_965_ = lean_unsigned_to_nat(3u);
v_body_966_ = l_Lean_Syntax_getArg(v_stx_610_, v___x_965_);
lean_dec(v_stx_610_);
v___x_967_ = l_Lean_Syntax_getArg(v___x_962_, v___x_616_);
v___x_968_ = l_Lean_Syntax_isNone(v___x_967_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; uint8_t v___x_970_; 
v___x_969_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_967_);
v___x_970_ = l_Lean_Syntax_matchesNull(v___x_967_, v___x_969_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; 
lean_dec(v___x_967_);
lean_dec(v_body_966_);
lean_dec(v___x_962_);
lean_dec_ref(v_decls_960_);
lean_dec_ref(v___y_954_);
v___x_971_ = l_Lean_Macro_throwUnsupported___redArg(v___y_955_);
return v___x_971_;
}
else
{
lean_object* v_h_x3f_972_; lean_object* v___x_973_; 
v_h_x3f_972_ = l_Lean_Syntax_getArg(v___x_967_, v___x_616_);
lean_dec(v___x_967_);
v___x_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_973_, 0, v_h_x3f_972_);
v___y_885_ = v___x_962_;
v___y_886_ = v_body_966_;
v___y_887_ = v___x_965_;
v___y_888_ = v___x_958_;
v___y_889_ = v_decls_960_;
v_h_x3f_890_ = v___x_973_;
v___y_891_ = v___y_954_;
v___y_892_ = v___y_955_;
goto v___jp_884_;
}
}
else
{
lean_object* v___x_974_; 
lean_dec(v___x_967_);
v___x_974_ = lean_box(0);
v___y_885_ = v___x_962_;
v___y_886_ = v_body_966_;
v___y_887_ = v___x_965_;
v___y_888_ = v___x_958_;
v___y_889_ = v_decls_960_;
v_h_x3f_890_ = v___x_974_;
v___y_891_ = v___y_954_;
v___y_892_ = v___y_955_;
goto v___jp_884_;
}
}
}
else
{
lean_object* v___x_975_; 
lean_dec_ref(v___y_954_);
lean_dec(v___x_618_);
lean_dec(v_stx_610_);
v___x_975_ = l_Lean_Macro_throwUnsupported___redArg(v___y_955_);
return v___x_975_;
}
}
v___jp_976_:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
lean_inc_ref(v___y_982_);
v___x_988_ = l_Array_append___redArg(v___y_982_, v___y_987_);
lean_dec_ref(v___y_987_);
lean_inc(v___y_977_);
lean_inc(v___y_978_);
v___x_989_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_989_, 0, v___y_978_);
lean_ctor_set(v___x_989_, 1, v___y_977_);
lean_ctor_set(v___x_989_, 2, v___x_988_);
v___x_990_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
lean_inc(v___y_978_);
v___x_991_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_991_, 0, v___y_978_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
lean_inc(v___y_978_);
v___x_992_ = l_Lean_Syntax_node4(v___y_978_, v___x_776_, v___x_989_, v___y_980_, v___x_991_, v___y_981_);
lean_inc(v___y_977_);
lean_inc(v___y_978_);
v___x_993_ = l_Lean_Syntax_node1(v___y_978_, v___y_977_, v___x_992_);
v___x_994_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75));
lean_inc(v___y_978_);
v___x_995_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_995_, 0, v___y_978_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
lean_inc_ref(v___x_995_);
lean_inc(v___y_978_);
v___x_996_ = l_Lean_Syntax_node4(v___y_978_, v___x_613_, v___y_985_, v___x_993_, v___x_995_, v___y_986_);
lean_inc_ref(v___y_982_);
lean_inc(v___y_977_);
lean_inc(v___y_978_);
v___x_997_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_997_, 0, v___y_978_);
lean_ctor_set(v___x_997_, 1, v___y_977_);
lean_ctor_set(v___x_997_, 2, v___y_982_);
lean_inc(v___y_978_);
v___x_998_ = l_Lean_Syntax_node2(v___y_978_, v___y_984_, v___x_996_, v___x_997_);
v___x_999_ = lean_array_push(v___y_979_, v___x_998_);
v___x_1000_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_1001_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_1002_ = l_Array_append___redArg(v___y_982_, v___x_999_);
lean_dec_ref(v___x_999_);
lean_inc(v___y_978_);
v___x_1003_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1003_, 0, v___y_978_);
lean_ctor_set(v___x_1003_, 1, v___y_977_);
lean_ctor_set(v___x_1003_, 2, v___x_1002_);
lean_inc(v___y_978_);
v___x_1004_ = l_Lean_Syntax_node1(v___y_978_, v___x_1001_, v___x_1003_);
v___x_1005_ = l_Lean_Syntax_node2(v___y_978_, v___x_1000_, v___x_995_, v___x_1004_);
v___x_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set(v___x_1006_, 1, v___y_983_);
return v___x_1006_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0(uint8_t v___x_1257_, lean_object* v_inst_1258_, lean_object* v_R_1259_, lean_object* v_a_1260_, lean_object* v_b_1261_, lean_object* v_c_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_1257_, v_a_1260_, v_b_1261_, v___y_1263_, v___y_1264_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___boxed(lean_object* v___x_1266_, lean_object* v_inst_1267_, lean_object* v_R_1268_, lean_object* v_a_1269_, lean_object* v_b_1270_, lean_object* v_c_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
uint8_t v___x_147669__boxed_1274_; lean_object* v_res_1275_; 
v___x_147669__boxed_1274_ = lean_unbox(v___x_1266_);
v_res_1275_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0(v___x_147669__boxed_1274_, v_inst_1267_, v_R_1268_, v_a_1269_, v_b_1270_, v_c_1271_, v___y_1272_, v___y_1273_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1(){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1283_ = l_Lean_Elab_macroAttribute;
v___x_1284_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
v___x_1285_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1));
v___x_1286_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_expandDoFor), 3, 0);
v___x_1287_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1283_, v___x_1284_, v___x_1285_, v___x_1286_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___boxed(lean_object* v_a_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1();
return v_res_1289_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1290_ = lean_box(0);
v___x_1291_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1292_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
lean_ctor_set(v___x_1292_, 1, v___x_1290_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg(){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0);
v___x_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___boxed(lean_object* v___y_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0(lean_object* v_00_u03b1_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___boxed(lean_object* v_00_u03b1_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0(v_00_u03b1_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec_ref(v___y_1309_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0(lean_object* v_k_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v_b_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v___x_1328_; 
v___x_1328_ = lean_apply_9(v_k_1318_, v_b_1322_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, lean_box(0));
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0___boxed(lean_object* v_k_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v_b_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0(v_k_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v_b_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(lean_object* v_name_1340_, uint8_t v_bi_1341_, lean_object* v_type_1342_, lean_object* v_k_1343_, uint8_t v_kind_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v___f_1353_; lean_object* v___x_1354_; 
v___f_1353_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1353_, 0, v_k_1343_);
lean_closure_set(v___f_1353_, 1, v___y_1345_);
lean_closure_set(v___f_1353_, 2, v___y_1346_);
lean_closure_set(v___f_1353_, 3, v___y_1347_);
v___x_1354_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1340_, v_bi_1341_, v_type_1342_, v___f_1353_, v_kind_1344_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
if (lean_obj_tag(v___x_1354_) == 0)
{
return v___x_1354_;
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1354_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1354_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___boxed(lean_object* v_name_1363_, lean_object* v_bi_1364_, lean_object* v_type_1365_, lean_object* v_k_1366_, lean_object* v_kind_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
uint8_t v_bi_boxed_1376_; uint8_t v_kind_boxed_1377_; lean_object* v_res_1378_; 
v_bi_boxed_1376_ = lean_unbox(v_bi_1364_);
v_kind_boxed_1377_ = lean_unbox(v_kind_1367_);
v_res_1378_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_name_1363_, v_bi_boxed_1376_, v_type_1365_, v_k_1366_, v_kind_boxed_1377_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3(lean_object* v_00_u03b1_1379_, lean_object* v_name_1380_, uint8_t v_bi_1381_, lean_object* v_type_1382_, lean_object* v_k_1383_, uint8_t v_kind_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v___x_1393_; 
v___x_1393_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_name_1380_, v_bi_1381_, v_type_1382_, v_k_1383_, v_kind_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___boxed(lean_object* v_00_u03b1_1394_, lean_object* v_name_1395_, lean_object* v_bi_1396_, lean_object* v_type_1397_, lean_object* v_k_1398_, lean_object* v_kind_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
uint8_t v_bi_boxed_1408_; uint8_t v_kind_boxed_1409_; lean_object* v_res_1410_; 
v_bi_boxed_1408_ = lean_unbox(v_bi_1396_);
v_kind_boxed_1409_ = lean_unbox(v_kind_1399_);
v_res_1410_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3(v_00_u03b1_1394_, v_name_1395_, v_bi_boxed_1408_, v_type_1397_, v_k_1398_, v_kind_boxed_1409_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__0(lean_object* v_a_1411_, lean_object* v_x_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1421_, 0, v_a_1411_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__0___boxed(lean_object* v_a_1422_, lean_object* v_x_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Lean_Elab_Do_elabDoFor___lam__0(v_a_1422_, v_x_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec_ref(v_x_1423_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__1(lean_object* v_x_1433_, lean_object* v___f_1434_, lean_object* v___x_1435_, lean_object* v_x_1436_, lean_object* v_x_1437_){
_start:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1438_ = l_Lean_TSyntax_getId(v_x_1433_);
v___x_1439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1438_);
lean_ctor_set(v___x_1439_, 1, v___f_1434_);
v___x_1440_ = lean_mk_empty_array_with_capacity(v___x_1435_);
v___x_1441_ = lean_array_push(v___x_1440_, v___x_1439_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__1___boxed(lean_object* v_x_1442_, lean_object* v___f_1443_, lean_object* v___x_1444_, lean_object* v_x_1445_, lean_object* v_x_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Lean_Elab_Do_elabDoFor___lam__1(v_x_1442_, v___f_1443_, v___x_1444_, v_x_1445_, v_x_1446_);
lean_dec(v_x_1446_);
lean_dec(v_x_1445_);
lean_dec(v___x_1444_);
lean_dec(v_x_1442_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__3(lean_object* v_a_1448_, lean_object* v___x_1449_, uint8_t v___x_1450_, lean_object* v_r_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v_k_1460_; lean_object* v___x_1461_; 
v_k_1460_ = lean_ctor_get(v_a_1448_, 1);
lean_inc_ref(v_k_1460_);
lean_dec_ref(v_a_1448_);
lean_inc(v___y_1458_);
lean_inc_ref(v___y_1457_);
lean_inc(v___y_1456_);
lean_inc_ref(v___y_1455_);
lean_inc_ref(v_r_1451_);
v___x_1461_ = lean_apply_9(v_k_1460_, v_r_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, lean_box(0));
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; uint8_t v___x_1465_; uint8_t v___x_1466_; lean_object* v___x_1467_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_a_1462_);
lean_dec_ref(v___x_1461_);
v___x_1463_ = lean_mk_empty_array_with_capacity(v___x_1449_);
v___x_1464_ = lean_array_push(v___x_1463_, v_r_1451_);
v___x_1465_ = 0;
v___x_1466_ = 1;
v___x_1467_ = l_Lean_Meta_mkLambdaFVars(v___x_1464_, v_a_1462_, v___x_1465_, v___x_1450_, v___x_1465_, v___x_1450_, v___x_1466_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec_ref(v___x_1464_);
return v___x_1467_;
}
else
{
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec_ref(v_r_1451_);
return v___x_1461_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___boxed(lean_object* v_a_1468_, lean_object* v___x_1469_, lean_object* v___x_1470_, lean_object* v_r_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
uint8_t v___x_78389__boxed_1480_; lean_object* v_res_1481_; 
v___x_78389__boxed_1480_ = lean_unbox(v___x_1470_);
v_res_1481_ = l_Lean_Elab_Do_elabDoFor___lam__3(v_a_1468_, v___x_1469_, v___x_78389__boxed_1480_, v_r_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
lean_dec(v___x_1469_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1(lean_object* v___x_1482_, lean_object* v_as_1483_, size_t v_sz_1484_, size_t v_i_1485_, lean_object* v_b_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
uint8_t v___x_1494_; 
v___x_1494_ = lean_usize_dec_lt(v_i_1485_, v_sz_1484_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; 
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec_ref(v___x_1482_);
v___x_1495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1495_, 0, v_b_1486_);
return v___x_1495_;
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v_a_1496_ = lean_array_uget_borrowed(v_as_1483_, v_i_1485_);
v___x_1497_ = l_Lean_TSyntax_getId(v_a_1496_);
v___x_1498_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_1497_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v_a_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; uint8_t v___x_1503_; lean_object* v___x_1504_; 
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_a_1499_);
lean_dec_ref(v___x_1498_);
lean_inc(v_a_1499_);
v___x_1500_ = l_Lean_LocalDecl_toExpr(v_a_1499_);
v___x_1501_ = lean_box(0);
v___x_1502_ = lean_box(0);
v___x_1503_ = 0;
lean_inc(v___y_1492_);
lean_inc_ref(v___y_1491_);
lean_inc(v___y_1490_);
lean_inc_ref(v___y_1489_);
lean_inc(v___y_1488_);
lean_inc_ref(v___y_1487_);
lean_inc_ref(v___x_1500_);
lean_inc(v_a_1496_);
v___x_1504_ = l_Lean_Elab_Term_addTermInfo_x27(v_a_1496_, v___x_1500_, v___x_1501_, v___x_1501_, v___x_1502_, v___x_1503_, v___x_1503_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_u_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
lean_dec_ref(v___x_1504_);
v_u_1505_ = lean_ctor_get(v___x_1482_, 1);
lean_inc(v_u_1505_);
v___x_1506_ = l_Lean_Level_succ___override(v_u_1505_);
v___x_1507_ = l_Lean_mkSort(v___x_1506_);
v___x_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
v___x_1509_ = l_Lean_LocalDecl_type(v_a_1499_);
lean_dec(v_a_1499_);
lean_inc(v___y_1492_);
lean_inc_ref(v___y_1491_);
lean_inc(v___y_1490_);
lean_inc_ref(v___y_1489_);
lean_inc(v___y_1488_);
lean_inc_ref(v___y_1487_);
v___x_1510_ = l_Lean_Elab_Term_ensureHasType(v___x_1508_, v___x_1509_, v___x_1501_, v___x_1501_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v___x_1511_; size_t v___x_1512_; size_t v___x_1513_; 
lean_dec_ref(v___x_1510_);
v___x_1511_ = lean_array_push(v_b_1486_, v___x_1500_);
v___x_1512_ = ((size_t)1ULL);
v___x_1513_ = lean_usize_add(v_i_1485_, v___x_1512_);
v_i_1485_ = v___x_1513_;
v_b_1486_ = v___x_1511_;
goto _start;
}
else
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1522_; 
lean_dec_ref(v___x_1500_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec_ref(v_b_1486_);
lean_dec_ref(v___x_1482_);
v_a_1515_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1517_ = v___x_1510_;
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1510_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1520_; 
if (v_isShared_1518_ == 0)
{
v___x_1520_ = v___x_1517_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_a_1515_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
else
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1530_; 
lean_dec_ref(v___x_1500_);
lean_dec(v_a_1499_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec_ref(v_b_1486_);
lean_dec_ref(v___x_1482_);
v_a_1523_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1525_ = v___x_1504_;
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1504_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1523_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
else
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec_ref(v_b_1486_);
lean_dec_ref(v___x_1482_);
v_a_1531_ = lean_ctor_get(v___x_1498_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1498_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___x_1498_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1498_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1___boxed(lean_object* v___x_1539_, lean_object* v_as_1540_, lean_object* v_sz_1541_, lean_object* v_i_1542_, lean_object* v_b_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
size_t v_sz_boxed_1551_; size_t v_i_boxed_1552_; lean_object* v_res_1553_; 
v_sz_boxed_1551_ = lean_unbox_usize(v_sz_1541_);
lean_dec(v_sz_1541_);
v_i_boxed_1552_ = lean_unbox_usize(v_i_1542_);
lean_dec(v_i_1542_);
v_res_1553_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1(v___x_1539_, v_as_1540_, v_sz_boxed_1551_, v_i_boxed_1552_, v_b_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
lean_dec_ref(v_as_1540_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(lean_object* v_msgData_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
lean_object* v___x_1560_; lean_object* v_env_1561_; lean_object* v___x_1562_; lean_object* v_mctx_1563_; lean_object* v_lctx_1564_; lean_object* v_options_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1560_ = lean_st_ref_get(v___y_1558_);
v_env_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc_ref(v_env_1561_);
lean_dec(v___x_1560_);
v___x_1562_ = lean_st_ref_get(v___y_1556_);
v_mctx_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc_ref(v_mctx_1563_);
lean_dec(v___x_1562_);
v_lctx_1564_ = lean_ctor_get(v___y_1555_, 2);
v_options_1565_ = lean_ctor_get(v___y_1557_, 2);
lean_inc_ref(v_options_1565_);
lean_inc_ref(v_lctx_1564_);
v___x_1566_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1566_, 0, v_env_1561_);
lean_ctor_set(v___x_1566_, 1, v_mctx_1563_);
lean_ctor_set(v___x_1566_, 2, v_lctx_1564_);
lean_ctor_set(v___x_1566_, 3, v_options_1565_);
v___x_1567_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1566_);
lean_ctor_set(v___x_1567_, 1, v_msgData_1554_);
v___x_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2___boxed(lean_object* v_msgData_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(v_msgData_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
return v_res_1575_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0(void){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = lean_box(1);
v___x_1577_ = l_Lean_MessageData_ofFormat(v___x_1576_);
return v___x_1577_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3(void){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1581_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__2));
v___x_1582_ = l_Lean_MessageData_ofFormat(v___x_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6(lean_object* v_x_1583_, lean_object* v_x_1584_){
_start:
{
if (lean_obj_tag(v_x_1584_) == 0)
{
return v_x_1583_;
}
else
{
lean_object* v_head_1585_; lean_object* v_tail_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1608_; 
v_head_1585_ = lean_ctor_get(v_x_1584_, 0);
v_tail_1586_ = lean_ctor_get(v_x_1584_, 1);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_x_1584_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1588_ = v_x_1584_;
v_isShared_1589_ = v_isSharedCheck_1608_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_tail_1586_);
lean_inc(v_head_1585_);
lean_dec(v_x_1584_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1608_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v_before_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1606_; 
v_before_1590_ = lean_ctor_get(v_head_1585_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_head_1585_);
if (v_isSharedCheck_1606_ == 0)
{
lean_object* v_unused_1607_; 
v_unused_1607_ = lean_ctor_get(v_head_1585_, 1);
lean_dec(v_unused_1607_);
v___x_1592_ = v_head_1585_;
v_isShared_1593_ = v_isSharedCheck_1606_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_before_1590_);
lean_dec(v_head_1585_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1606_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1594_; lean_object* v___x_1596_; 
v___x_1594_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0);
if (v_isShared_1593_ == 0)
{
lean_ctor_set_tag(v___x_1592_, 7);
lean_ctor_set(v___x_1592_, 1, v___x_1594_);
lean_ctor_set(v___x_1592_, 0, v_x_1583_);
v___x_1596_ = v___x_1592_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_x_1583_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v___x_1594_);
v___x_1596_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
lean_object* v___x_1597_; lean_object* v___x_1599_; 
v___x_1597_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3);
if (v_isShared_1589_ == 0)
{
lean_ctor_set_tag(v___x_1588_, 7);
lean_ctor_set(v___x_1588_, 1, v___x_1597_);
lean_ctor_set(v___x_1588_, 0, v___x_1596_);
v___x_1599_ = v___x_1588_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1596_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v___x_1597_);
v___x_1599_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1600_ = l_Lean_MessageData_ofSyntax(v_before_1590_);
v___x_1601_ = l_Lean_indentD(v___x_1600_);
v___x_1602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1599_);
lean_ctor_set(v___x_1602_, 1, v___x_1601_);
v_x_1583_ = v___x_1602_;
v_x_1584_ = v_tail_1586_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5(lean_object* v_opts_1609_, lean_object* v_opt_1610_){
_start:
{
lean_object* v_name_1611_; lean_object* v_defValue_1612_; lean_object* v_map_1613_; lean_object* v___x_1614_; 
v_name_1611_ = lean_ctor_get(v_opt_1610_, 0);
v_defValue_1612_ = lean_ctor_get(v_opt_1610_, 1);
v_map_1613_ = lean_ctor_get(v_opts_1609_, 0);
v___x_1614_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1613_, v_name_1611_);
if (lean_obj_tag(v___x_1614_) == 0)
{
uint8_t v___x_1615_; 
v___x_1615_ = lean_unbox(v_defValue_1612_);
return v___x_1615_;
}
else
{
lean_object* v_val_1616_; 
v_val_1616_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_val_1616_);
lean_dec_ref(v___x_1614_);
if (lean_obj_tag(v_val_1616_) == 1)
{
uint8_t v_v_1617_; 
v_v_1617_ = lean_ctor_get_uint8(v_val_1616_, 0);
lean_dec_ref(v_val_1616_);
return v_v_1617_;
}
else
{
uint8_t v___x_1618_; 
lean_dec(v_val_1616_);
v___x_1618_ = lean_unbox(v_defValue_1612_);
return v___x_1618_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5___boxed(lean_object* v_opts_1619_, lean_object* v_opt_1620_){
_start:
{
uint8_t v_res_1621_; lean_object* v_r_1622_; 
v_res_1621_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5(v_opts_1619_, v_opt_1620_);
lean_dec_ref(v_opt_1620_);
lean_dec_ref(v_opts_1619_);
v_r_1622_ = lean_box(v_res_1621_);
return v_r_1622_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1626_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__1));
v___x_1627_ = l_Lean_MessageData_ofFormat(v___x_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(lean_object* v_msgData_1628_, lean_object* v_macroStack_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v_options_1632_; lean_object* v___x_1633_; uint8_t v___x_1634_; 
v_options_1632_ = lean_ctor_get(v___y_1630_, 2);
v___x_1633_ = l_Lean_Elab_pp_macroStack;
v___x_1634_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5(v_options_1632_, v___x_1633_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; 
lean_dec(v_macroStack_1629_);
v___x_1635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1635_, 0, v_msgData_1628_);
return v___x_1635_;
}
else
{
if (lean_obj_tag(v_macroStack_1629_) == 0)
{
lean_object* v___x_1636_; 
v___x_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1636_, 0, v_msgData_1628_);
return v___x_1636_;
}
else
{
lean_object* v_head_1637_; lean_object* v_after_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1653_; 
v_head_1637_ = lean_ctor_get(v_macroStack_1629_, 0);
lean_inc(v_head_1637_);
v_after_1638_ = lean_ctor_get(v_head_1637_, 1);
v_isSharedCheck_1653_ = !lean_is_exclusive(v_head_1637_);
if (v_isSharedCheck_1653_ == 0)
{
lean_object* v_unused_1654_; 
v_unused_1654_ = lean_ctor_get(v_head_1637_, 0);
lean_dec(v_unused_1654_);
v___x_1640_ = v_head_1637_;
v_isShared_1641_ = v_isSharedCheck_1653_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_after_1638_);
lean_dec(v_head_1637_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1653_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1642_; lean_object* v___x_1644_; 
v___x_1642_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0);
if (v_isShared_1641_ == 0)
{
lean_ctor_set_tag(v___x_1640_, 7);
lean_ctor_set(v___x_1640_, 1, v___x_1642_);
lean_ctor_set(v___x_1640_, 0, v_msgData_1628_);
v___x_1644_ = v___x_1640_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_msgData_1628_);
lean_ctor_set(v_reuseFailAlloc_1652_, 1, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v_msgData_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1645_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2);
v___x_1646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1644_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
v___x_1647_ = l_Lean_MessageData_ofSyntax(v_after_1638_);
v___x_1648_ = l_Lean_indentD(v___x_1647_);
v_msgData_1649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1649_, 0, v___x_1646_);
lean_ctor_set(v_msgData_1649_, 1, v___x_1648_);
v___x_1650_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6(v_msgData_1649_, v_macroStack_1629_);
v___x_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
return v___x_1651_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___boxed(lean_object* v_msgData_1655_, lean_object* v_macroStack_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(v_msgData_1655_, v_macroStack_1656_, v___y_1657_);
lean_dec_ref(v___y_1657_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(lean_object* v_msg_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v_ref_1668_; lean_object* v___x_1669_; lean_object* v_a_1670_; lean_object* v_macroStack_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1682_; 
v_ref_1668_ = lean_ctor_get(v___y_1665_, 5);
v___x_1669_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(v_msg_1660_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
lean_inc(v_a_1670_);
lean_dec_ref(v___x_1669_);
v_macroStack_1671_ = lean_ctor_get(v___y_1661_, 1);
lean_inc(v_macroStack_1671_);
lean_dec_ref(v___y_1661_);
lean_inc(v_macroStack_1671_);
v___x_1672_ = l_Lean_Elab_getBetterRef(v_ref_1668_, v_macroStack_1671_);
v___x_1673_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(v_a_1670_, v_macroStack_1671_, v___y_1665_);
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1676_ = v___x_1673_;
v_isShared_1677_ = v_isSharedCheck_1682_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v___x_1673_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1682_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1678_; lean_object* v___x_1680_; 
v___x_1678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1672_);
lean_ctor_set(v___x_1678_, 1, v_a_1674_);
if (v_isShared_1677_ == 0)
{
lean_ctor_set_tag(v___x_1676_, 1);
lean_ctor_set(v___x_1676_, 0, v___x_1678_);
v___x_1680_ = v___x_1676_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg___boxed(lean_object* v_msg_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v_msg_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
return v_res_1691_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1697_ = lean_box(0);
v___x_1698_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__2___closed__2));
v___x_1699_ = l_Lean_mkConst(v___x_1698_, v___x_1697_);
return v___x_1699_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__2___closed__5(void){
_start:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1701_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__2___closed__4));
v___x_1702_ = l_Lean_stringToMessageData(v___x_1701_);
return v___x_1702_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__2___closed__7(void){
_start:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__2___closed__6));
v___x_1705_ = l_Lean_stringToMessageData(v___x_1704_);
return v___x_1705_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__2___closed__10(void){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__2___closed__9));
v___x_1710_ = l_Lean_MessageData_ofFormat(v___x_1709_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__2(lean_object* v___y_1711_, lean_object* v_monadInfo_1712_, uint8_t v_returnsEarly_1713_, lean_object* v___x_1714_, lean_object* v_a_1715_, uint8_t v___x_1716_, lean_object* v_e_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v_defs_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___x_1749_; lean_object* v_returnVar_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1784_; lean_object* v___y_1785_; 
v___x_1749_ = lean_mk_empty_array_with_capacity(v___x_1714_);
if (lean_obj_tag(v_e_1717_) == 0)
{
if (v___x_1716_ == 0)
{
goto v___jp_1798_;
}
else
{
goto v___jp_1759_;
}
}
else
{
goto v___jp_1798_;
}
v___jp_1725_:
{
size_t v_sz_1733_; size_t v___x_1734_; lean_object* v___x_1735_; 
v_sz_1733_ = lean_array_size(v___y_1711_);
v___x_1734_ = ((size_t)0ULL);
v___x_1735_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1(v_monadInfo_1712_, v___y_1711_, v_sz_1733_, v___x_1734_, v_defs_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
if (lean_obj_tag(v___x_1735_) == 0)
{
if (v_returnsEarly_1713_ == 0)
{
return v___x_1735_;
}
else
{
lean_object* v_a_1736_; lean_object* v___x_1737_; uint8_t v___x_1738_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1736_);
v___x_1737_ = lean_array_get_size(v___y_1711_);
v___x_1738_ = lean_nat_dec_eq(v___x_1737_, v___x_1714_);
if (v___x_1738_ == 0)
{
lean_dec(v_a_1736_);
return v___x_1735_;
}
else
{
lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1747_; 
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1747_ == 0)
{
lean_object* v_unused_1748_; 
v_unused_1748_ = lean_ctor_get(v___x_1735_, 0);
lean_dec(v_unused_1748_);
v___x_1740_ = v___x_1735_;
v_isShared_1741_ = v_isSharedCheck_1747_;
goto v_resetjp_1739_;
}
else
{
lean_dec(v___x_1735_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1747_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1745_; 
v___x_1742_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__2___closed__3, &l_Lean_Elab_Do_elabDoFor___lam__2___closed__3_once, _init_l_Lean_Elab_Do_elabDoFor___lam__2___closed__3);
v___x_1743_ = lean_array_push(v_a_1736_, v___x_1742_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 0, v___x_1743_);
v___x_1745_ = v___x_1740_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1743_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
}
else
{
return v___x_1735_;
}
}
v___jp_1750_:
{
lean_object* v___x_1758_; 
v___x_1758_ = lean_array_push(v___x_1749_, v_returnVar_1751_);
v_defs_1726_ = v___x_1758_;
v___y_1727_ = v___y_1752_;
v___y_1728_ = v___y_1753_;
v___y_1729_ = v___y_1754_;
v___y_1730_ = v___y_1755_;
v___y_1731_ = v___y_1756_;
v___y_1732_ = v___y_1757_;
goto v___jp_1725_;
}
v___jp_1759_:
{
if (v_returnsEarly_1713_ == 0)
{
lean_dec(v_e_1717_);
lean_dec_ref(v_a_1715_);
v_defs_1726_ = v___x_1749_;
v___y_1727_ = v___y_1718_;
v___y_1728_ = v___y_1719_;
v___y_1729_ = v___y_1720_;
v___y_1730_ = v___y_1721_;
v___y_1731_ = v___y_1722_;
v___y_1732_ = v___y_1723_;
goto v___jp_1725_;
}
else
{
if (lean_obj_tag(v_e_1717_) == 0)
{
lean_object* v_resultType_1760_; lean_object* v___x_1761_; 
v_resultType_1760_ = lean_ctor_get(v_a_1715_, 0);
lean_inc_ref(v_resultType_1760_);
lean_dec_ref(v_a_1715_);
lean_inc(v___y_1723_);
lean_inc_ref(v___y_1722_);
lean_inc(v___y_1721_);
lean_inc_ref(v___y_1720_);
v___x_1761_ = l_Lean_Meta_mkNone(v_resultType_1760_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1762_);
lean_dec_ref(v___x_1761_);
v_returnVar_1751_ = v_a_1762_;
v___y_1752_ = v___y_1718_;
v___y_1753_ = v___y_1719_;
v___y_1754_ = v___y_1720_;
v___y_1755_ = v___y_1721_;
v___y_1756_ = v___y_1722_;
v___y_1757_ = v___y_1723_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
lean_dec_ref(v___x_1749_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec_ref(v_monadInfo_1712_);
v_a_1763_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1761_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1761_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1763_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
else
{
lean_object* v_val_1771_; lean_object* v_resultType_1772_; lean_object* v___x_1773_; 
v_val_1771_ = lean_ctor_get(v_e_1717_, 0);
lean_inc(v_val_1771_);
lean_dec_ref(v_e_1717_);
v_resultType_1772_ = lean_ctor_get(v_a_1715_, 0);
lean_inc_ref(v_resultType_1772_);
lean_dec_ref(v_a_1715_);
lean_inc(v___y_1723_);
lean_inc_ref(v___y_1722_);
lean_inc(v___y_1721_);
lean_inc_ref(v___y_1720_);
v___x_1773_ = l_Lean_Meta_mkSome(v_resultType_1772_, v_val_1771_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_a_1774_);
lean_dec_ref(v___x_1773_);
v_returnVar_1751_ = v_a_1774_;
v___y_1752_ = v___y_1718_;
v___y_1753_ = v___y_1719_;
v___y_1754_ = v___y_1720_;
v___y_1755_ = v___y_1721_;
v___y_1756_ = v___y_1722_;
v___y_1757_ = v___y_1723_;
goto v___jp_1750_;
}
else
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1782_; 
lean_dec_ref(v___x_1749_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec_ref(v_monadInfo_1712_);
v_a_1775_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1777_ = v___x_1773_;
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1773_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1780_; 
if (v_isShared_1778_ == 0)
{
v___x_1780_ = v___x_1777_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_a_1775_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
}
}
v___jp_1783_:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1797_; 
v___x_1786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1786_, 0, v___y_1784_);
lean_ctor_set(v___x_1786_, 1, v___y_1785_);
v___x_1787_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__2___closed__5, &l_Lean_Elab_Do_elabDoFor___lam__2___closed__5_once, _init_l_Lean_Elab_Do_elabDoFor___lam__2___closed__5);
v___x_1788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1786_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
v___x_1789_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v___x_1788_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1792_ = v___x_1789_;
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1789_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1793_ == 0)
{
v___x_1795_ = v___x_1792_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1790_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
v___jp_1798_:
{
if (v_returnsEarly_1713_ == 0)
{
lean_object* v___x_1799_; 
lean_dec_ref(v___x_1749_);
lean_dec_ref(v_a_1715_);
lean_dec_ref(v_monadInfo_1712_);
v___x_1799_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__2___closed__7, &l_Lean_Elab_Do_elabDoFor___lam__2___closed__7_once, _init_l_Lean_Elab_Do_elabDoFor___lam__2___closed__7);
if (lean_obj_tag(v_e_1717_) == 0)
{
lean_object* v___x_1800_; 
v___x_1800_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__2___closed__10, &l_Lean_Elab_Do_elabDoFor___lam__2___closed__10_once, _init_l_Lean_Elab_Do_elabDoFor___lam__2___closed__10);
v___y_1784_ = v___x_1799_;
v___y_1785_ = v___x_1800_;
goto v___jp_1783_;
}
else
{
lean_object* v_val_1801_; lean_object* v___x_1802_; 
v_val_1801_ = lean_ctor_get(v_e_1717_, 0);
lean_inc(v_val_1801_);
lean_dec_ref(v_e_1717_);
v___x_1802_ = l_Lean_MessageData_ofExpr(v_val_1801_);
v___y_1784_ = v___x_1799_;
v___y_1785_ = v___x_1802_;
goto v___jp_1783_;
}
}
else
{
goto v___jp_1759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__2___boxed(lean_object* v___y_1803_, lean_object* v_monadInfo_1804_, lean_object* v_returnsEarly_1805_, lean_object* v___x_1806_, lean_object* v_a_1807_, lean_object* v___x_1808_, lean_object* v_e_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
uint8_t v_returnsEarly_boxed_1817_; uint8_t v___x_78805__boxed_1818_; lean_object* v_res_1819_; 
v_returnsEarly_boxed_1817_ = lean_unbox(v_returnsEarly_1805_);
v___x_78805__boxed_1818_ = lean_unbox(v___x_1808_);
v_res_1819_ = l_Lean_Elab_Do_elabDoFor___lam__2(v___y_1803_, v_monadInfo_1804_, v_returnsEarly_boxed_1817_, v___x_1806_, v_a_1807_, v___x_78805__boxed_1818_, v_e_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
lean_dec(v___x_1806_);
lean_dec_ref(v___y_1803_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__4(lean_object* v___f_1821_, lean_object* v_u_1822_, lean_object* v___x_1823_, lean_object* v___x_1824_, lean_object* v_snd_1825_, lean_object* v___x_1826_, lean_object* v_e_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1836_, 0, v_e_1827_);
lean_inc(v___y_1834_);
lean_inc_ref(v___y_1833_);
lean_inc(v___y_1832_);
lean_inc_ref(v___y_1831_);
lean_inc(v___y_1830_);
lean_inc_ref(v___y_1829_);
v___x_1837_ = lean_apply_8(v___f_1821_, v___x_1836_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, lean_box(0));
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1839_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc(v_a_1838_);
lean_dec_ref(v___x_1837_);
lean_inc(v___y_1834_);
lean_inc_ref(v___y_1833_);
lean_inc(v___y_1832_);
lean_inc_ref(v___y_1831_);
v___x_1839_ = l_Lean_Meta_mkProdMkN(v_a_1838_, v_u_1822_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; lean_object* v_fst_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
lean_inc(v_a_1840_);
lean_dec_ref(v___x_1839_);
v_fst_1841_ = lean_ctor_get(v_a_1840_, 0);
lean_inc(v_fst_1841_);
lean_dec(v_a_1840_);
v___x_1842_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__4___closed__0));
v___x_1843_ = l_Lean_Name_mkStr2(v___x_1823_, v___x_1842_);
v___x_1844_ = l_Lean_mkConst(v___x_1843_, v___x_1824_);
v___x_1845_ = l_Lean_mkAppB(v___x_1844_, v_snd_1825_, v_fst_1841_);
v___x_1846_ = l_Lean_Elab_Do_mkPureApp(v___x_1826_, v___x_1845_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
return v___x_1846_;
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec_ref(v___x_1826_);
lean_dec_ref(v_snd_1825_);
lean_dec(v___x_1824_);
lean_dec_ref(v___x_1823_);
v_a_1847_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1839_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1839_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec_ref(v___x_1826_);
lean_dec_ref(v_snd_1825_);
lean_dec(v___x_1824_);
lean_dec_ref(v___x_1823_);
lean_dec(v_u_1822_);
v_a_1855_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1837_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1837_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___boxed(lean_object* v___f_1863_, lean_object* v_u_1864_, lean_object* v___x_1865_, lean_object* v___x_1866_, lean_object* v_snd_1867_, lean_object* v___x_1868_, lean_object* v_e_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_Lean_Elab_Do_elabDoFor___lam__4(v___f_1863_, v_u_1864_, v___x_1865_, v___x_1866_, v_snd_1867_, v___x_1868_, v_e_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__5(lean_object* v___f_1880_, lean_object* v___x_1881_, lean_object* v_u_1882_, lean_object* v___x_1883_, lean_object* v___x_1884_, lean_object* v_snd_1885_, lean_object* v___x_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v___x_1895_; 
lean_inc(v___y_1893_);
lean_inc_ref(v___y_1892_);
lean_inc(v___y_1891_);
lean_inc_ref(v___y_1890_);
lean_inc(v___y_1889_);
lean_inc_ref(v___y_1888_);
v___x_1895_ = lean_apply_8(v___f_1880_, v___x_1881_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, lean_box(0));
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; lean_object* v___x_1897_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_a_1896_);
lean_dec_ref(v___x_1895_);
lean_inc(v___y_1893_);
lean_inc_ref(v___y_1892_);
lean_inc(v___y_1891_);
lean_inc_ref(v___y_1890_);
v___x_1897_ = l_Lean_Meta_mkProdMkN(v_a_1896_, v_u_1882_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; lean_object* v_fst_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_a_1898_);
lean_dec_ref(v___x_1897_);
v_fst_1899_ = lean_ctor_get(v_a_1898_, 0);
lean_inc(v_fst_1899_);
lean_dec(v_a_1898_);
v___x_1900_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__5___closed__0));
v___x_1901_ = l_Lean_Name_mkStr2(v___x_1883_, v___x_1900_);
v___x_1902_ = l_Lean_mkConst(v___x_1901_, v___x_1884_);
v___x_1903_ = l_Lean_mkAppB(v___x_1902_, v_snd_1885_, v_fst_1899_);
v___x_1904_ = l_Lean_Elab_Do_mkPureApp(v___x_1886_, v___x_1903_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
return v___x_1904_;
}
else
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec_ref(v___x_1886_);
lean_dec_ref(v_snd_1885_);
lean_dec(v___x_1884_);
lean_dec_ref(v___x_1883_);
v_a_1905_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1907_ = v___x_1897_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1897_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
else
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec_ref(v___x_1886_);
lean_dec_ref(v_snd_1885_);
lean_dec(v___x_1884_);
lean_dec_ref(v___x_1883_);
lean_dec(v_u_1882_);
v_a_1913_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v___x_1895_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1895_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__5___boxed(lean_object* v___f_1921_, lean_object* v___x_1922_, lean_object* v_u_1923_, lean_object* v___x_1924_, lean_object* v___x_1925_, lean_object* v_snd_1926_, lean_object* v___x_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Lean_Elab_Do_elabDoFor___lam__5(v___f_1921_, v___x_1922_, v_u_1923_, v___x_1924_, v___x_1925_, v_snd_1926_, v___x_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__6(lean_object* v___f_1937_, lean_object* v___x_1938_, lean_object* v_u_1939_, lean_object* v___x_1940_, lean_object* v___x_1941_, lean_object* v_snd_1942_, lean_object* v___x_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
lean_object* v___x_1952_; 
lean_inc(v___y_1950_);
lean_inc_ref(v___y_1949_);
lean_inc(v___y_1948_);
lean_inc_ref(v___y_1947_);
lean_inc(v___y_1946_);
lean_inc_ref(v___y_1945_);
v___x_1952_ = lean_apply_8(v___f_1937_, v___x_1938_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, lean_box(0));
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; lean_object* v___x_1954_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1953_);
lean_dec_ref(v___x_1952_);
lean_inc(v___y_1950_);
lean_inc_ref(v___y_1949_);
lean_inc(v___y_1948_);
lean_inc_ref(v___y_1947_);
v___x_1954_ = l_Lean_Meta_mkProdMkN(v_a_1953_, v_u_1939_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; lean_object* v_fst_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_a_1955_);
lean_dec_ref(v___x_1954_);
v_fst_1956_ = lean_ctor_get(v_a_1955_, 0);
lean_inc(v_fst_1956_);
lean_dec(v_a_1955_);
v___x_1957_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__4___closed__0));
v___x_1958_ = l_Lean_Name_mkStr2(v___x_1940_, v___x_1957_);
v___x_1959_ = l_Lean_mkConst(v___x_1958_, v___x_1941_);
v___x_1960_ = l_Lean_mkAppB(v___x_1959_, v_snd_1942_, v_fst_1956_);
v___x_1961_ = l_Lean_Elab_Do_mkPureApp(v___x_1943_, v___x_1960_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
return v___x_1961_;
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec_ref(v___x_1943_);
lean_dec_ref(v_snd_1942_);
lean_dec(v___x_1941_);
lean_dec_ref(v___x_1940_);
v_a_1962_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1954_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1954_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
else
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec_ref(v___x_1943_);
lean_dec_ref(v_snd_1942_);
lean_dec(v___x_1941_);
lean_dec_ref(v___x_1940_);
lean_dec(v_u_1939_);
v_a_1970_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v___x_1952_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1952_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__6___boxed(lean_object* v___f_1978_, lean_object* v___x_1979_, lean_object* v_u_1980_, lean_object* v___x_1981_, lean_object* v___x_1982_, lean_object* v_snd_1983_, lean_object* v___x_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Lean_Elab_Do_elabDoFor___lam__6(v___f_1978_, v___x_1979_, v_u_1980_, v___x_1981_, v___x_1982_, v_snd_1983_, v___x_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__7(lean_object* v___x_1994_, lean_object* v___f_1995_, lean_object* v___f_1996_, lean_object* v___x_1997_, lean_object* v___x_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
lean_object* v_monadInfo_2007_; lean_object* v_mutVars_2008_; lean_object* v_mutVarDefs_2009_; lean_object* v_contInfo_2010_; uint8_t v_deadCode_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2019_; 
v_monadInfo_2007_ = lean_ctor_get(v___y_1999_, 0);
v_mutVars_2008_ = lean_ctor_get(v___y_1999_, 1);
v_mutVarDefs_2009_ = lean_ctor_get(v___y_1999_, 2);
v_contInfo_2010_ = lean_ctor_get(v___y_1999_, 4);
v_deadCode_2011_ = lean_ctor_get_uint8(v___y_1999_, sizeof(void*)*5);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___y_1999_);
if (v_isSharedCheck_2019_ == 0)
{
lean_object* v_unused_2020_; 
v_unused_2020_ = lean_ctor_get(v___y_1999_, 3);
lean_dec(v_unused_2020_);
v___x_2013_ = v___y_1999_;
v_isShared_2014_ = v_isSharedCheck_2019_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_contInfo_2010_);
lean_inc(v_mutVarDefs_2009_);
lean_inc(v_mutVars_2008_);
lean_inc(v_monadInfo_2007_);
lean_dec(v___y_1999_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2019_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 3, v___x_1994_);
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_monadInfo_2007_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v_mutVars_2008_);
lean_ctor_set(v_reuseFailAlloc_2018_, 2, v_mutVarDefs_2009_);
lean_ctor_set(v_reuseFailAlloc_2018_, 3, v___x_1994_);
lean_ctor_set(v_reuseFailAlloc_2018_, 4, v_contInfo_2010_);
lean_ctor_set_uint8(v_reuseFailAlloc_2018_, sizeof(void*)*5, v_deadCode_2011_);
v___x_2016_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
lean_object* v___x_2017_; 
v___x_2017_ = l_Lean_Elab_Do_enterLoopBody___redArg(v___f_1995_, v___f_1996_, v___x_1997_, v___x_1998_, v___x_2016_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
return v___x_2017_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__7___boxed(lean_object* v___x_2021_, lean_object* v___f_2022_, lean_object* v___f_2023_, lean_object* v___x_2024_, lean_object* v___x_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_Lean_Elab_Do_elabDoFor___lam__7(v___x_2021_, v___f_2022_, v___f_2023_, v___x_2024_, v___x_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__8(lean_object* v_a_2038_, lean_object* v_u_2039_, lean_object* v_snd_2040_, lean_object* v___f_2041_, lean_object* v___x_2042_, lean_object* v_resultName_2043_, lean_object* v_resultType_2044_, lean_object* v_body_2045_, uint8_t v___x_2046_, lean_object* v___y_2047_, lean_object* v_xh_2048_, lean_object* v_loopS_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
lean_object* v_resultType_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2086_; 
v_resultType_2058_ = lean_ctor_get(v_a_2038_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v_a_2038_);
if (v_isSharedCheck_2086_ == 0)
{
lean_object* v_unused_2087_; 
v_unused_2087_ = lean_ctor_get(v_a_2038_, 1);
lean_dec(v_unused_2087_);
v___x_2060_ = v_a_2038_;
v_isShared_2061_ = v_isSharedCheck_2086_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_resultType_2058_);
lean_dec(v_a_2038_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2086_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___f_2069_; lean_object* v___f_2070_; lean_object* v___f_2071_; lean_object* v___x_2073_; 
v___x_2062_ = l_Lean_Expr_fvarId_x21(v_loopS_2049_);
v___x_2063_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__8___closed__0));
v___x_2064_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__8___closed__1));
v___x_2065_ = lean_box(0);
lean_inc(v_u_2039_);
v___x_2066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2066_, 0, v_u_2039_);
lean_ctor_set(v___x_2066_, 1, v___x_2065_);
lean_inc_ref(v___x_2066_);
v___x_2067_ = l_Lean_mkConst(v___x_2064_, v___x_2066_);
lean_inc_ref(v_snd_2040_);
v___x_2068_ = l_Lean_Expr_app___override(v___x_2067_, v_snd_2040_);
lean_inc_ref(v___x_2068_);
lean_inc_ref(v_snd_2040_);
lean_inc_ref(v___x_2066_);
lean_inc(v_u_2039_);
lean_inc_ref(v___f_2041_);
v___f_2069_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__4___boxed), 15, 6);
lean_closure_set(v___f_2069_, 0, v___f_2041_);
lean_closure_set(v___f_2069_, 1, v_u_2039_);
lean_closure_set(v___f_2069_, 2, v___x_2063_);
lean_closure_set(v___f_2069_, 3, v___x_2066_);
lean_closure_set(v___f_2069_, 4, v_snd_2040_);
lean_closure_set(v___f_2069_, 5, v___x_2068_);
lean_inc_ref(v___x_2068_);
lean_inc_ref(v_snd_2040_);
lean_inc_ref(v___x_2066_);
lean_inc(v_u_2039_);
lean_inc(v___x_2042_);
lean_inc_ref(v___f_2041_);
v___f_2070_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__5___boxed), 15, 7);
lean_closure_set(v___f_2070_, 0, v___f_2041_);
lean_closure_set(v___f_2070_, 1, v___x_2042_);
lean_closure_set(v___f_2070_, 2, v_u_2039_);
lean_closure_set(v___f_2070_, 3, v___x_2063_);
lean_closure_set(v___f_2070_, 4, v___x_2066_);
lean_closure_set(v___f_2070_, 5, v_snd_2040_);
lean_closure_set(v___f_2070_, 6, v___x_2068_);
lean_inc_ref(v___x_2068_);
v___f_2071_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__6___boxed), 15, 7);
lean_closure_set(v___f_2071_, 0, v___f_2041_);
lean_closure_set(v___f_2071_, 1, v___x_2042_);
lean_closure_set(v___f_2071_, 2, v_u_2039_);
lean_closure_set(v___f_2071_, 3, v___x_2063_);
lean_closure_set(v___f_2071_, 4, v___x_2066_);
lean_closure_set(v___f_2071_, 5, v_snd_2040_);
lean_closure_set(v___f_2071_, 6, v___x_2068_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 1, v___f_2069_);
v___x_2073_ = v___x_2060_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_resultType_2058_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v___f_2069_);
v___x_2073_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
uint8_t v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___f_2078_; lean_object* v___x_2079_; 
v___x_2074_ = 1;
lean_inc_ref(v___f_2070_);
v___x_2075_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2075_, 0, v_resultName_2043_);
lean_ctor_set(v___x_2075_, 1, v_resultType_2044_);
lean_ctor_set(v___x_2075_, 2, v___f_2070_);
lean_ctor_set_uint8(v___x_2075_, sizeof(void*)*3, v___x_2074_);
v___x_2076_ = lean_box(v___x_2046_);
v___x_2077_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoSeq___boxed), 11, 3);
lean_closure_set(v___x_2077_, 0, v_body_2045_);
lean_closure_set(v___x_2077_, 1, v___x_2075_);
lean_closure_set(v___x_2077_, 2, v___x_2076_);
v___f_2078_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__7___boxed), 13, 5);
lean_closure_set(v___f_2078_, 0, v___x_2068_);
lean_closure_set(v___f_2078_, 1, v___f_2071_);
lean_closure_set(v___f_2078_, 2, v___f_2070_);
lean_closure_set(v___f_2078_, 3, v___x_2073_);
lean_closure_set(v___f_2078_, 4, v___x_2077_);
lean_inc(v___y_2056_);
lean_inc_ref(v___y_2055_);
lean_inc(v___y_2054_);
lean_inc_ref(v___y_2053_);
v___x_2079_ = l_Lean_Elab_Do_bindMutVarsFromTuple(v___y_2047_, v___x_2062_, v___f_2078_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; uint8_t v___x_2083_; lean_object* v___x_2084_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc(v_a_2080_);
lean_dec_ref(v___x_2079_);
v___x_2081_ = lean_array_push(v_xh_2048_, v_loopS_2049_);
v___x_2082_ = 0;
v___x_2083_ = 1;
v___x_2084_ = l_Lean_Meta_mkLambdaFVars(v___x_2081_, v_a_2080_, v___x_2082_, v___x_2046_, v___x_2082_, v___x_2046_, v___x_2083_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
lean_dec_ref(v___x_2081_);
return v___x_2084_;
}
else
{
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
lean_dec_ref(v_loopS_2049_);
lean_dec_ref(v_xh_2048_);
return v___x_2079_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__8___boxed(lean_object** _args){
lean_object* v_a_2088_ = _args[0];
lean_object* v_u_2089_ = _args[1];
lean_object* v_snd_2090_ = _args[2];
lean_object* v___f_2091_ = _args[3];
lean_object* v___x_2092_ = _args[4];
lean_object* v_resultName_2093_ = _args[5];
lean_object* v_resultType_2094_ = _args[6];
lean_object* v_body_2095_ = _args[7];
lean_object* v___x_2096_ = _args[8];
lean_object* v___y_2097_ = _args[9];
lean_object* v_xh_2098_ = _args[10];
lean_object* v_loopS_2099_ = _args[11];
lean_object* v___y_2100_ = _args[12];
lean_object* v___y_2101_ = _args[13];
lean_object* v___y_2102_ = _args[14];
lean_object* v___y_2103_ = _args[15];
lean_object* v___y_2104_ = _args[16];
lean_object* v___y_2105_ = _args[17];
lean_object* v___y_2106_ = _args[18];
lean_object* v___y_2107_ = _args[19];
_start:
{
uint8_t v___x_79361__boxed_2108_; lean_object* v_res_2109_; 
v___x_79361__boxed_2108_ = lean_unbox(v___x_2096_);
v_res_2109_ = l_Lean_Elab_Do_elabDoFor___lam__8(v_a_2088_, v_u_2089_, v_snd_2090_, v___f_2091_, v___x_2092_, v_resultName_2093_, v_resultType_2094_, v_body_2095_, v___x_79361__boxed_2108_, v___y_2097_, v_xh_2098_, v_loopS_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9(lean_object* v_a_2110_, lean_object* v_u_2111_, lean_object* v_snd_2112_, lean_object* v___f_2113_, lean_object* v___x_2114_, lean_object* v_resultName_2115_, lean_object* v_resultType_2116_, lean_object* v_body_2117_, uint8_t v___x_2118_, lean_object* v___y_2119_, lean_object* v_a_2120_, lean_object* v_xh_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v___x_2130_; lean_object* v___f_2131_; uint8_t v___x_2132_; uint8_t v___x_2133_; lean_object* v___x_2134_; 
v___x_2130_ = lean_box(v___x_2118_);
lean_inc_ref(v_snd_2112_);
v___f_2131_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__8___boxed), 20, 11);
lean_closure_set(v___f_2131_, 0, v_a_2110_);
lean_closure_set(v___f_2131_, 1, v_u_2111_);
lean_closure_set(v___f_2131_, 2, v_snd_2112_);
lean_closure_set(v___f_2131_, 3, v___f_2113_);
lean_closure_set(v___f_2131_, 4, v___x_2114_);
lean_closure_set(v___f_2131_, 5, v_resultName_2115_);
lean_closure_set(v___f_2131_, 6, v_resultType_2116_);
lean_closure_set(v___f_2131_, 7, v_body_2117_);
lean_closure_set(v___f_2131_, 8, v___x_2130_);
lean_closure_set(v___f_2131_, 9, v___y_2119_);
lean_closure_set(v___f_2131_, 10, v_xh_2121_);
v___x_2132_ = 0;
v___x_2133_ = 1;
v___x_2134_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_a_2120_, v___x_2132_, v_snd_2112_, v___f_2131_, v___x_2133_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9___boxed(lean_object** _args){
lean_object* v_a_2135_ = _args[0];
lean_object* v_u_2136_ = _args[1];
lean_object* v_snd_2137_ = _args[2];
lean_object* v___f_2138_ = _args[3];
lean_object* v___x_2139_ = _args[4];
lean_object* v_resultName_2140_ = _args[5];
lean_object* v_resultType_2141_ = _args[6];
lean_object* v_body_2142_ = _args[7];
lean_object* v___x_2143_ = _args[8];
lean_object* v___y_2144_ = _args[9];
lean_object* v_a_2145_ = _args[10];
lean_object* v_xh_2146_ = _args[11];
lean_object* v___y_2147_ = _args[12];
lean_object* v___y_2148_ = _args[13];
lean_object* v___y_2149_ = _args[14];
lean_object* v___y_2150_ = _args[15];
lean_object* v___y_2151_ = _args[16];
lean_object* v___y_2152_ = _args[17];
lean_object* v___y_2153_ = _args[18];
lean_object* v___y_2154_ = _args[19];
_start:
{
uint8_t v___x_79465__boxed_2155_; lean_object* v_res_2156_; 
v___x_79465__boxed_2155_ = lean_unbox(v___x_2143_);
v_res_2156_ = l_Lean_Elab_Do_elabDoFor___lam__9(v_a_2135_, v_u_2136_, v_snd_2137_, v___f_2138_, v___x_2139_, v_resultName_2140_, v_resultType_2141_, v_body_2142_, v___x_79465__boxed_2155_, v___y_2144_, v_a_2145_, v_xh_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(lean_object* v_name_2157_, lean_object* v_type_2158_, lean_object* v_k_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
uint8_t v___x_2168_; uint8_t v___x_2169_; lean_object* v___x_2170_; 
v___x_2168_ = 0;
v___x_2169_ = 0;
v___x_2170_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_name_2157_, v___x_2168_, v_type_2158_, v_k_2159_, v___x_2169_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg___boxed(lean_object* v_name_2171_, lean_object* v_type_2172_, lean_object* v_k_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(v_name_2171_, v_type_2172_, v_k_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__10(uint8_t v_returnsEarly_2200_, lean_object* v_dec_2201_, lean_object* v_a_2202_, lean_object* v_doBlockResultType_2203_, lean_object* v_a_2204_, lean_object* v_v_2205_, lean_object* v_u_2206_, lean_object* v___f_2207_, lean_object* v___y_2208_, lean_object* v___x_2209_, lean_object* v___x_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v_ret_2220_; lean_object* v___y_2221_; lean_object* v___y_2222_; lean_object* v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; 
if (v_returnsEarly_2200_ == 0)
{
lean_object* v___x_2274_; 
lean_dec_ref(v___f_2207_);
lean_dec(v_u_2206_);
lean_dec(v_v_2205_);
lean_dec_ref(v_a_2204_);
lean_dec_ref(v_doBlockResultType_2203_);
lean_dec(v_a_2202_);
v___x_2274_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_dec_2201_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
return v___x_2274_;
}
else
{
lean_object* v___x_2275_; 
v___x_2275_ = l_Lean_Meta_getFVarFromUserName(v_a_2202_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v_a_2276_; lean_object* v___x_2277_; uint8_t v___x_2278_; 
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_a_2276_);
lean_dec_ref(v___x_2275_);
v___x_2277_ = lean_array_get_size(v___y_2208_);
v___x_2278_ = lean_nat_dec_eq(v___x_2277_, v___x_2209_);
if (v___x_2278_ == 0)
{
v_ret_2220_ = v_a_2276_;
v___y_2221_ = v___y_2211_;
v___y_2222_ = v___y_2212_;
v___y_2223_ = v___y_2213_;
v___y_2224_ = v___y_2214_;
v___y_2225_ = v___y_2215_;
v___y_2226_ = v___y_2216_;
v___y_2227_ = v___y_2217_;
goto v___jp_2219_;
}
else
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2279_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__10___closed__9));
v___x_2280_ = lean_mk_empty_array_with_capacity(v___x_2210_);
v___x_2281_ = lean_array_push(v___x_2280_, v_a_2276_);
lean_inc(v___y_2217_);
lean_inc_ref(v___y_2216_);
lean_inc(v___y_2215_);
lean_inc_ref(v___y_2214_);
v___x_2282_ = l_Lean_Meta_mkAppM(v___x_2279_, v___x_2281_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_a_2283_);
lean_dec_ref(v___x_2282_);
v_ret_2220_ = v_a_2283_;
v___y_2221_ = v___y_2211_;
v___y_2222_ = v___y_2212_;
v___y_2223_ = v___y_2213_;
v___y_2224_ = v___y_2214_;
v___y_2225_ = v___y_2215_;
v___y_2226_ = v___y_2216_;
v___y_2227_ = v___y_2217_;
goto v___jp_2219_;
}
else
{
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec_ref(v___f_2207_);
lean_dec(v_u_2206_);
lean_dec(v_v_2205_);
lean_dec_ref(v_a_2204_);
lean_dec_ref(v_doBlockResultType_2203_);
lean_dec_ref(v_dec_2201_);
return v___x_2282_;
}
}
}
else
{
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec_ref(v___f_2207_);
lean_dec(v_u_2206_);
lean_dec(v_v_2205_);
lean_dec_ref(v_a_2204_);
lean_dec_ref(v_doBlockResultType_2203_);
lean_dec_ref(v_dec_2201_);
return v___x_2275_;
}
}
v___jp_2219_:
{
lean_object* v___x_2228_; 
lean_inc(v___y_2227_);
lean_inc_ref(v___y_2226_);
lean_inc(v___y_2225_);
lean_inc_ref(v___y_2224_);
lean_inc_ref(v_ret_2220_);
v___x_2228_ = lean_infer_type(v_ret_2220_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; lean_object* v___x_2230_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc(v_a_2229_);
lean_dec_ref(v___x_2228_);
lean_inc_ref(v___y_2221_);
v___x_2230_ = l_Lean_Elab_Do_mkMonadicType___redArg(v_doBlockResultType_2203_, v___y_2221_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_a_2231_; lean_object* v___x_2232_; 
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_a_2231_);
lean_dec_ref(v___x_2230_);
lean_inc(v___y_2227_);
lean_inc_ref(v___y_2226_);
lean_inc(v___y_2225_);
lean_inc_ref(v___y_2224_);
lean_inc(v___y_2223_);
lean_inc_ref(v___y_2222_);
lean_inc_ref(v___y_2221_);
v___x_2232_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_dec_2201_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2233_);
lean_dec_ref(v___x_2232_);
v___x_2234_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__10___closed__1));
lean_inc(v___y_2227_);
lean_inc_ref(v___y_2226_);
v___x_2235_ = l_Lean_Core_mkFreshUserName(v___x_2234_, v___y_2226_, v___y_2227_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; lean_object* v_resultType_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2264_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2236_);
lean_dec_ref(v___x_2235_);
v_resultType_2237_ = lean_ctor_get(v_a_2204_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v_a_2204_);
if (v_isSharedCheck_2264_ == 0)
{
lean_object* v_unused_2265_; 
v_unused_2265_ = lean_ctor_get(v_a_2204_, 1);
lean_dec(v_unused_2265_);
v___x_2239_ = v_a_2204_;
v_isShared_2240_ = v_isSharedCheck_2264_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_resultType_2237_);
lean_dec(v_a_2204_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2264_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2241_; uint8_t v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2248_; 
v___x_2241_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__10___closed__2));
v___x_2242_ = 0;
v___x_2243_ = l_Lean_mkLambda(v___x_2241_, v___x_2242_, v_a_2229_, v_a_2231_);
v___x_2244_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__10___closed__6));
v___x_2245_ = l_Lean_Level_succ___override(v_v_2205_);
v___x_2246_ = lean_box(0);
if (v_isShared_2240_ == 0)
{
lean_ctor_set_tag(v___x_2239_, 1);
lean_ctor_set(v___x_2239_, 1, v___x_2246_);
lean_ctor_set(v___x_2239_, 0, v___x_2245_);
v___x_2248_ = v___x_2239_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v___x_2245_);
lean_ctor_set(v_reuseFailAlloc_2263_, 1, v___x_2246_);
v___x_2248_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2249_, 0, v_u_2206_);
lean_ctor_set(v___x_2249_, 1, v___x_2248_);
v___x_2250_ = l_Lean_mkConst(v___x_2244_, v___x_2249_);
lean_inc_ref(v_resultType_2237_);
v___x_2251_ = l_Lean_mkApp3(v___x_2250_, v_resultType_2237_, v___x_2243_, v_ret_2220_);
v___x_2252_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(v_a_2236_, v_resultType_2237_, v___f_2207_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2262_; 
v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2255_ = v___x_2252_;
v_isShared_2256_ = v_isSharedCheck_2262_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2252_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2262_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2260_; 
v___x_2257_ = l_Lean_mkSimpleThunk(v_a_2233_);
v___x_2258_ = l_Lean_mkAppB(v___x_2251_, v_a_2253_, v___x_2257_);
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 0, v___x_2258_);
v___x_2260_ = v___x_2255_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v___x_2258_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
else
{
lean_dec_ref(v___x_2251_);
lean_dec(v_a_2233_);
return v___x_2252_;
}
}
}
}
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
lean_dec(v_a_2233_);
lean_dec(v_a_2231_);
lean_dec(v_a_2229_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec_ref(v_ret_2220_);
lean_dec_ref(v___f_2207_);
lean_dec(v_u_2206_);
lean_dec(v_v_2205_);
lean_dec_ref(v_a_2204_);
v_a_2266_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2235_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2235_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
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
lean_dec(v_a_2231_);
lean_dec(v_a_2229_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec_ref(v_ret_2220_);
lean_dec_ref(v___f_2207_);
lean_dec(v_u_2206_);
lean_dec(v_v_2205_);
lean_dec_ref(v_a_2204_);
return v___x_2232_;
}
}
else
{
lean_dec(v_a_2229_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec_ref(v_ret_2220_);
lean_dec_ref(v___f_2207_);
lean_dec(v_u_2206_);
lean_dec(v_v_2205_);
lean_dec_ref(v_a_2204_);
lean_dec_ref(v_dec_2201_);
return v___x_2230_;
}
}
else
{
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec_ref(v_ret_2220_);
lean_dec_ref(v___f_2207_);
lean_dec(v_u_2206_);
lean_dec(v_v_2205_);
lean_dec_ref(v_a_2204_);
lean_dec_ref(v_doBlockResultType_2203_);
lean_dec_ref(v_dec_2201_);
return v___x_2228_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___boxed(lean_object** _args){
lean_object* v_returnsEarly_2284_ = _args[0];
lean_object* v_dec_2285_ = _args[1];
lean_object* v_a_2286_ = _args[2];
lean_object* v_doBlockResultType_2287_ = _args[3];
lean_object* v_a_2288_ = _args[4];
lean_object* v_v_2289_ = _args[5];
lean_object* v_u_2290_ = _args[6];
lean_object* v___f_2291_ = _args[7];
lean_object* v___y_2292_ = _args[8];
lean_object* v___x_2293_ = _args[9];
lean_object* v___x_2294_ = _args[10];
lean_object* v___y_2295_ = _args[11];
lean_object* v___y_2296_ = _args[12];
lean_object* v___y_2297_ = _args[13];
lean_object* v___y_2298_ = _args[14];
lean_object* v___y_2299_ = _args[15];
lean_object* v___y_2300_ = _args[16];
lean_object* v___y_2301_ = _args[17];
lean_object* v___y_2302_ = _args[18];
_start:
{
uint8_t v_returnsEarly_boxed_2303_; lean_object* v_res_2304_; 
v_returnsEarly_boxed_2303_ = lean_unbox(v_returnsEarly_2284_);
v_res_2304_ = l_Lean_Elab_Do_elabDoFor___lam__10(v_returnsEarly_boxed_2303_, v_dec_2285_, v_a_2286_, v_doBlockResultType_2287_, v_a_2288_, v_v_2289_, v_u_2290_, v___f_2291_, v___y_2292_, v___x_2293_, v___x_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
lean_dec(v___x_2294_);
lean_dec(v___x_2293_);
lean_dec_ref(v___y_2292_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__11(lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___x_2307_, uint8_t v___x_2308_, lean_object* v_postS_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2318_ = l_Lean_Expr_fvarId_x21(v_postS_2309_);
lean_inc(v___y_2316_);
lean_inc_ref(v___y_2315_);
lean_inc(v___y_2314_);
lean_inc_ref(v___y_2313_);
v___x_2319_ = l_Lean_Elab_Do_bindMutVarsFromTuple(v___y_2305_, v___x_2318_, v___y_2306_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; uint8_t v___x_2323_; uint8_t v___x_2324_; lean_object* v___x_2325_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_a_2320_);
lean_dec_ref(v___x_2319_);
v___x_2321_ = lean_mk_empty_array_with_capacity(v___x_2307_);
v___x_2322_ = lean_array_push(v___x_2321_, v_postS_2309_);
v___x_2323_ = 0;
v___x_2324_ = 1;
v___x_2325_ = l_Lean_Meta_mkLambdaFVars(v___x_2322_, v_a_2320_, v___x_2323_, v___x_2308_, v___x_2323_, v___x_2308_, v___x_2324_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec_ref(v___x_2322_);
return v___x_2325_;
}
else
{
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec_ref(v_postS_2309_);
return v___x_2319_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__11___boxed(lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___x_2328_, lean_object* v___x_2329_, lean_object* v_postS_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
uint8_t v___x_79775__boxed_2339_; lean_object* v_res_2340_; 
v___x_79775__boxed_2339_ = lean_unbox(v___x_2329_);
v_res_2340_ = l_Lean_Elab_Do_elabDoFor___lam__11(v___y_2326_, v___y_2327_, v___x_2328_, v___x_79775__boxed_2339_, v_postS_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
lean_dec(v___x_2328_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__12(lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v___x_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_val_2351_, lean_object* v_a_2352_, lean_object* v_x_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2362_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__12___closed__2));
v___x_2363_ = lean_box(0);
v___x_2364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2364_, 0, v_a_2346_);
lean_ctor_set(v___x_2364_, 1, v___x_2363_);
v___x_2365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2365_, 0, v_a_2347_);
lean_ctor_set(v___x_2365_, 1, v___x_2364_);
v___x_2366_ = l_Lean_mkConst(v___x_2362_, v___x_2365_);
v___x_2367_ = l_Lean_instInhabitedExpr;
v___x_2368_ = lean_array_get_borrowed(v___x_2367_, v_x_2353_, v___x_2348_);
lean_inc(v___x_2368_);
v___x_2369_ = l_Lean_mkApp5(v___x_2366_, v_a_2349_, v_a_2350_, v_val_2351_, v_a_2352_, v___x_2368_);
v___x_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2369_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__12___boxed(lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v___x_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_val_2376_, lean_object* v_a_2377_, lean_object* v_x_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l_Lean_Elab_Do_elabDoFor___lam__12(v_a_2371_, v_a_2372_, v___x_2373_, v_a_2374_, v_a_2375_, v_val_2376_, v_a_2377_, v_x_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec_ref(v_x_2378_);
lean_dec(v___x_2373_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___lam__0(lean_object* v___x_2388_, lean_object* v_a_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
lean_object* v___x_2398_; lean_object* v___x_78161__overap_2399_; lean_object* v___x_2400_; 
v___x_2398_ = l_Lean_instInhabitedExpr;
v___x_78161__overap_2399_ = l_instInhabitedOfMonad___redArg(v___x_2388_, v___x_2398_);
v___x_2400_ = lean_apply_8(v___x_78161__overap_2399_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, lean_box(0));
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___lam__0___boxed(lean_object* v___x_2401_, lean_object* v_a_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___lam__0(v___x_2401_, v_a_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
lean_dec_ref(v_a_2402_);
return v_res_2411_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_2412_; 
v___x_2412_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_2412_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2413_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__0);
v___x_2414_ = l_ReaderT_instMonad___redArg(v___x_2413_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___lam__1___boxed(lean_object* v_acc_2421_, lean_object* v_declInfos_2422_, lean_object* v_k_2423_, lean_object* v_kind_2424_, lean_object* v_x_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
uint8_t v_kind_boxed_2434_; lean_object* v_res_2435_; 
v_kind_boxed_2434_ = lean_unbox(v_kind_2424_);
v_res_2435_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___lam__1(v_acc_2421_, v_declInfos_2422_, v_k_2423_, v_kind_boxed_2434_, v_x_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg(lean_object* v_declInfos_2436_, lean_object* v_k_2437_, uint8_t v_kind_2438_, lean_object* v_acc_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v___x_2448_; lean_object* v_toApplicative_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2567_; 
v___x_2448_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__1);
v_toApplicative_2449_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2567_ == 0)
{
lean_object* v_unused_2568_; 
v_unused_2568_ = lean_ctor_get(v___x_2448_, 1);
lean_dec(v_unused_2568_);
v___x_2451_ = v___x_2448_;
v_isShared_2452_ = v_isSharedCheck_2567_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_toApplicative_2449_);
lean_dec(v___x_2448_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2567_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v_toFunctor_2453_; lean_object* v_toSeq_2454_; lean_object* v_toSeqLeft_2455_; lean_object* v_toSeqRight_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2565_; 
v_toFunctor_2453_ = lean_ctor_get(v_toApplicative_2449_, 0);
v_toSeq_2454_ = lean_ctor_get(v_toApplicative_2449_, 2);
v_toSeqLeft_2455_ = lean_ctor_get(v_toApplicative_2449_, 3);
v_toSeqRight_2456_ = lean_ctor_get(v_toApplicative_2449_, 4);
v_isSharedCheck_2565_ = !lean_is_exclusive(v_toApplicative_2449_);
if (v_isSharedCheck_2565_ == 0)
{
lean_object* v_unused_2566_; 
v_unused_2566_ = lean_ctor_get(v_toApplicative_2449_, 1);
lean_dec(v_unused_2566_);
v___x_2458_ = v_toApplicative_2449_;
v_isShared_2459_ = v_isSharedCheck_2565_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_toSeqRight_2456_);
lean_inc(v_toSeqLeft_2455_);
lean_inc(v_toSeq_2454_);
lean_inc(v_toFunctor_2453_);
lean_dec(v_toApplicative_2449_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2565_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___f_2460_; lean_object* v___f_2461_; lean_object* v___f_2462_; lean_object* v___f_2463_; lean_object* v___x_2464_; lean_object* v___f_2465_; lean_object* v___f_2466_; lean_object* v___f_2467_; lean_object* v___x_2469_; 
v___f_2460_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__2));
v___f_2461_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__3));
lean_inc_ref(v_toFunctor_2453_);
v___f_2462_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2462_, 0, v_toFunctor_2453_);
v___f_2463_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2463_, 0, v_toFunctor_2453_);
v___x_2464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___f_2462_);
lean_ctor_set(v___x_2464_, 1, v___f_2463_);
v___f_2465_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2465_, 0, v_toSeqRight_2456_);
v___f_2466_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2466_, 0, v_toSeqLeft_2455_);
v___f_2467_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2467_, 0, v_toSeq_2454_);
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 4, v___f_2465_);
lean_ctor_set(v___x_2458_, 3, v___f_2466_);
lean_ctor_set(v___x_2458_, 2, v___f_2467_);
lean_ctor_set(v___x_2458_, 1, v___f_2460_);
lean_ctor_set(v___x_2458_, 0, v___x_2464_);
v___x_2469_ = v___x_2458_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2464_);
lean_ctor_set(v_reuseFailAlloc_2564_, 1, v___f_2460_);
lean_ctor_set(v_reuseFailAlloc_2564_, 2, v___f_2467_);
lean_ctor_set(v_reuseFailAlloc_2564_, 3, v___f_2466_);
lean_ctor_set(v_reuseFailAlloc_2564_, 4, v___f_2465_);
v___x_2469_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
lean_object* v___x_2471_; 
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 1, v___f_2461_);
lean_ctor_set(v___x_2451_, 0, v___x_2469_);
v___x_2471_ = v___x_2451_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2469_);
lean_ctor_set(v_reuseFailAlloc_2563_, 1, v___f_2461_);
v___x_2471_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
lean_object* v___x_2472_; lean_object* v_toApplicative_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2561_; 
v___x_2472_ = l_ReaderT_instMonad___redArg(v___x_2471_);
v_toApplicative_2473_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2561_ == 0)
{
lean_object* v_unused_2562_; 
v_unused_2562_ = lean_ctor_get(v___x_2472_, 1);
lean_dec(v_unused_2562_);
v___x_2475_ = v___x_2472_;
v_isShared_2476_ = v_isSharedCheck_2561_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_toApplicative_2473_);
lean_dec(v___x_2472_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2561_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v_toFunctor_2477_; lean_object* v_toSeq_2478_; lean_object* v_toSeqLeft_2479_; lean_object* v_toSeqRight_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2559_; 
v_toFunctor_2477_ = lean_ctor_get(v_toApplicative_2473_, 0);
v_toSeq_2478_ = lean_ctor_get(v_toApplicative_2473_, 2);
v_toSeqLeft_2479_ = lean_ctor_get(v_toApplicative_2473_, 3);
v_toSeqRight_2480_ = lean_ctor_get(v_toApplicative_2473_, 4);
v_isSharedCheck_2559_ = !lean_is_exclusive(v_toApplicative_2473_);
if (v_isSharedCheck_2559_ == 0)
{
lean_object* v_unused_2560_; 
v_unused_2560_ = lean_ctor_get(v_toApplicative_2473_, 1);
lean_dec(v_unused_2560_);
v___x_2482_ = v_toApplicative_2473_;
v_isShared_2483_ = v_isSharedCheck_2559_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_toSeqRight_2480_);
lean_inc(v_toSeqLeft_2479_);
lean_inc(v_toSeq_2478_);
lean_inc(v_toFunctor_2477_);
lean_dec(v_toApplicative_2473_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2559_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___f_2484_; lean_object* v___f_2485_; lean_object* v___f_2486_; lean_object* v___f_2487_; lean_object* v___x_2488_; lean_object* v___f_2489_; lean_object* v___f_2490_; lean_object* v___f_2491_; lean_object* v___x_2493_; 
v___f_2484_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__4));
v___f_2485_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__5));
lean_inc_ref(v_toFunctor_2477_);
v___f_2486_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2486_, 0, v_toFunctor_2477_);
v___f_2487_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2487_, 0, v_toFunctor_2477_);
v___x_2488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___f_2486_);
lean_ctor_set(v___x_2488_, 1, v___f_2487_);
v___f_2489_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2489_, 0, v_toSeqRight_2480_);
v___f_2490_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2490_, 0, v_toSeqLeft_2479_);
v___f_2491_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2491_, 0, v_toSeq_2478_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 4, v___f_2489_);
lean_ctor_set(v___x_2482_, 3, v___f_2490_);
lean_ctor_set(v___x_2482_, 2, v___f_2491_);
lean_ctor_set(v___x_2482_, 1, v___f_2484_);
lean_ctor_set(v___x_2482_, 0, v___x_2488_);
v___x_2493_ = v___x_2482_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v___x_2488_);
lean_ctor_set(v_reuseFailAlloc_2558_, 1, v___f_2484_);
lean_ctor_set(v_reuseFailAlloc_2558_, 2, v___f_2491_);
lean_ctor_set(v_reuseFailAlloc_2558_, 3, v___f_2490_);
lean_ctor_set(v_reuseFailAlloc_2558_, 4, v___f_2489_);
v___x_2493_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
lean_object* v___x_2495_; 
if (v_isShared_2476_ == 0)
{
lean_ctor_set(v___x_2475_, 1, v___f_2485_);
lean_ctor_set(v___x_2475_, 0, v___x_2493_);
v___x_2495_ = v___x_2475_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v___x_2493_);
lean_ctor_set(v_reuseFailAlloc_2557_, 1, v___f_2485_);
v___x_2495_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
lean_object* v___x_2496_; lean_object* v_toApplicative_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2555_; 
v___x_2496_ = l_ReaderT_instMonad___redArg(v___x_2495_);
v_toApplicative_2497_ = lean_ctor_get(v___x_2496_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2555_ == 0)
{
lean_object* v_unused_2556_; 
v_unused_2556_ = lean_ctor_get(v___x_2496_, 1);
lean_dec(v_unused_2556_);
v___x_2499_ = v___x_2496_;
v_isShared_2500_ = v_isSharedCheck_2555_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_toApplicative_2497_);
lean_dec(v___x_2496_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2555_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v_toFunctor_2501_; lean_object* v_toSeq_2502_; lean_object* v_toSeqLeft_2503_; lean_object* v_toSeqRight_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2553_; 
v_toFunctor_2501_ = lean_ctor_get(v_toApplicative_2497_, 0);
v_toSeq_2502_ = lean_ctor_get(v_toApplicative_2497_, 2);
v_toSeqLeft_2503_ = lean_ctor_get(v_toApplicative_2497_, 3);
v_toSeqRight_2504_ = lean_ctor_get(v_toApplicative_2497_, 4);
v_isSharedCheck_2553_ = !lean_is_exclusive(v_toApplicative_2497_);
if (v_isSharedCheck_2553_ == 0)
{
lean_object* v_unused_2554_; 
v_unused_2554_ = lean_ctor_get(v_toApplicative_2497_, 1);
lean_dec(v_unused_2554_);
v___x_2506_ = v_toApplicative_2497_;
v_isShared_2507_ = v_isSharedCheck_2553_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_toSeqRight_2504_);
lean_inc(v_toSeqLeft_2503_);
lean_inc(v_toSeq_2502_);
lean_inc(v_toFunctor_2501_);
lean_dec(v_toApplicative_2497_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2553_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___f_2508_; lean_object* v___f_2509_; lean_object* v___f_2510_; lean_object* v___f_2511_; lean_object* v___x_2512_; lean_object* v___f_2513_; lean_object* v___f_2514_; lean_object* v___f_2515_; lean_object* v___x_2517_; 
v___f_2508_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__6));
v___f_2509_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__7));
lean_inc_ref(v_toFunctor_2501_);
v___f_2510_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2510_, 0, v_toFunctor_2501_);
v___f_2511_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2511_, 0, v_toFunctor_2501_);
v___x_2512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___f_2510_);
lean_ctor_set(v___x_2512_, 1, v___f_2511_);
v___f_2513_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2513_, 0, v_toSeqRight_2504_);
v___f_2514_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2514_, 0, v_toSeqLeft_2503_);
v___f_2515_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2515_, 0, v_toSeq_2502_);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 4, v___f_2513_);
lean_ctor_set(v___x_2506_, 3, v___f_2514_);
lean_ctor_set(v___x_2506_, 2, v___f_2515_);
lean_ctor_set(v___x_2506_, 1, v___f_2508_);
lean_ctor_set(v___x_2506_, 0, v___x_2512_);
v___x_2517_ = v___x_2506_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2512_);
lean_ctor_set(v_reuseFailAlloc_2552_, 1, v___f_2508_);
lean_ctor_set(v_reuseFailAlloc_2552_, 2, v___f_2515_);
lean_ctor_set(v_reuseFailAlloc_2552_, 3, v___f_2514_);
lean_ctor_set(v_reuseFailAlloc_2552_, 4, v___f_2513_);
v___x_2517_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
lean_object* v___x_2519_; 
if (v_isShared_2500_ == 0)
{
lean_ctor_set(v___x_2499_, 1, v___f_2509_);
lean_ctor_set(v___x_2499_, 0, v___x_2517_);
v___x_2519_ = v___x_2499_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v___x_2517_);
lean_ctor_set(v_reuseFailAlloc_2551_, 1, v___f_2509_);
v___x_2519_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; uint8_t v___x_2523_; 
v___x_2520_ = l_ReaderT_instMonad___redArg(v___x_2519_);
v___x_2521_ = lean_array_get_size(v_acc_2439_);
v___x_2522_ = lean_array_get_size(v_declInfos_2436_);
v___x_2523_ = lean_nat_dec_lt(v___x_2521_, v___x_2522_);
if (v___x_2523_ == 0)
{
lean_object* v___x_2524_; 
lean_dec_ref(v___x_2520_);
lean_dec_ref(v_declInfos_2436_);
v___x_2524_ = lean_apply_9(v_k_2437_, v_acc_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, lean_box(0));
return v___x_2524_;
}
else
{
lean_object* v___f_2525_; lean_object* v___x_2526_; uint8_t v___x_2527_; lean_object* v___f_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v_snd_2533_; lean_object* v_fst_2534_; lean_object* v_fst_2535_; lean_object* v_snd_2536_; lean_object* v___x_2537_; 
v___f_2525_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2525_, 0, v___x_2520_);
v___x_2526_ = lean_box(0);
v___x_2527_ = 0;
v___f_2528_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2528_, 0, v___f_2525_);
v___x_2529_ = lean_box(v___x_2527_);
v___x_2530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2529_);
lean_ctor_set(v___x_2530_, 1, v___f_2528_);
v___x_2531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2526_);
lean_ctor_set(v___x_2531_, 1, v___x_2530_);
v___x_2532_ = lean_array_get_borrowed(v___x_2531_, v_declInfos_2436_, v___x_2521_);
v_snd_2533_ = lean_ctor_get(v___x_2532_, 1);
v_fst_2534_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_fst_2534_);
v_fst_2535_ = lean_ctor_get(v_snd_2533_, 0);
lean_inc(v_fst_2535_);
v_snd_2536_ = lean_ctor_get(v_snd_2533_, 1);
lean_inc(v_snd_2536_);
lean_inc(v___y_2446_);
lean_inc_ref(v___y_2445_);
lean_inc(v___y_2444_);
lean_inc_ref(v___y_2443_);
lean_inc(v___y_2442_);
lean_inc_ref(v___y_2441_);
lean_inc_ref(v___y_2440_);
lean_inc_ref(v_acc_2439_);
v___x_2537_ = lean_apply_9(v_snd_2536_, v_acc_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, lean_box(0));
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_object* v_a_2538_; lean_object* v___x_2539_; lean_object* v___f_2540_; uint8_t v___x_2541_; lean_object* v___x_2542_; 
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
lean_inc(v_a_2538_);
lean_dec_ref(v___x_2537_);
v___x_2539_ = lean_box(v_kind_2438_);
v___f_2540_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___lam__1___boxed), 13, 4);
lean_closure_set(v___f_2540_, 0, v_acc_2439_);
lean_closure_set(v___f_2540_, 1, v_declInfos_2436_);
lean_closure_set(v___f_2540_, 2, v_k_2437_);
lean_closure_set(v___f_2540_, 3, v___x_2539_);
v___x_2541_ = lean_unbox(v_fst_2535_);
lean_dec(v_fst_2535_);
v___x_2542_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_fst_2534_, v___x_2541_, v_a_2538_, v___f_2540_, v_kind_2438_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
return v___x_2542_;
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
lean_dec(v_fst_2535_);
lean_dec(v_fst_2534_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec_ref(v_acc_2439_);
lean_dec_ref(v_k_2437_);
lean_dec_ref(v_declInfos_2436_);
v_a_2543_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___x_2537_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2537_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2548_; 
if (v_isShared_2546_ == 0)
{
v___x_2548_ = v___x_2545_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___lam__1(lean_object* v_acc_2569_, lean_object* v_declInfos_2570_, lean_object* v_k_2571_, uint8_t v_kind_2572_, lean_object* v_x_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2582_ = lean_array_push(v_acc_2569_, v_x_2573_);
v___x_2583_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg(v_declInfos_2570_, v_k_2571_, v_kind_2572_, v___x_2582_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_declInfos_2584_, lean_object* v_k_2585_, lean_object* v_kind_2586_, lean_object* v_acc_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
uint8_t v_kind_boxed_2596_; lean_object* v_res_2597_; 
v_kind_boxed_2596_ = lean_unbox(v_kind_2586_);
v_res_2597_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg(v_declInfos_2584_, v_k_2585_, v_kind_boxed_2596_, v_acc_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___redArg(lean_object* v_inst_2600_, lean_object* v_declInfos_2601_, lean_object* v_k_2602_, uint8_t v_kind_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___redArg___closed__0));
v___x_2613_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg(v_declInfos_2601_, v_k_2602_, v_kind_2603_, v___x_2612_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___redArg___boxed(lean_object* v_inst_2614_, lean_object* v_declInfos_2615_, lean_object* v_k_2616_, lean_object* v_kind_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_){
_start:
{
uint8_t v_kind_boxed_2626_; lean_object* v_res_2627_; 
v_kind_boxed_2626_ = lean_unbox(v_kind_2617_);
v_res_2627_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___redArg(v_inst_2614_, v_declInfos_2615_, v_k_2616_, v_kind_boxed_2626_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
lean_dec(v_inst_2614_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(size_t v_sz_2628_, size_t v_i_2629_, lean_object* v_bs_2630_){
_start:
{
uint8_t v___x_2631_; 
v___x_2631_ = lean_usize_dec_lt(v_i_2629_, v_sz_2628_);
if (v___x_2631_ == 0)
{
return v_bs_2630_;
}
else
{
lean_object* v_v_2632_; lean_object* v_fst_2633_; lean_object* v_snd_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2650_; 
v_v_2632_ = lean_array_uget(v_bs_2630_, v_i_2629_);
v_fst_2633_ = lean_ctor_get(v_v_2632_, 0);
v_snd_2634_ = lean_ctor_get(v_v_2632_, 1);
v_isSharedCheck_2650_ = !lean_is_exclusive(v_v_2632_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2636_ = v_v_2632_;
v_isShared_2637_ = v_isSharedCheck_2650_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_snd_2634_);
lean_inc(v_fst_2633_);
lean_dec(v_v_2632_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2650_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2638_; lean_object* v_bs_x27_2639_; uint8_t v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2643_; 
v___x_2638_ = lean_unsigned_to_nat(0u);
v_bs_x27_2639_ = lean_array_uset(v_bs_2630_, v_i_2629_, v___x_2638_);
v___x_2640_ = 0;
v___x_2641_ = lean_box(v___x_2640_);
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 0, v___x_2641_);
v___x_2643_ = v___x_2636_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2641_);
lean_ctor_set(v_reuseFailAlloc_2649_, 1, v_snd_2634_);
v___x_2643_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
lean_object* v___x_2644_; size_t v___x_2645_; size_t v___x_2646_; lean_object* v___x_2647_; 
v___x_2644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2644_, 0, v_fst_2633_);
lean_ctor_set(v___x_2644_, 1, v___x_2643_);
v___x_2645_ = ((size_t)1ULL);
v___x_2646_ = lean_usize_add(v_i_2629_, v___x_2645_);
v___x_2647_ = lean_array_uset(v_bs_x27_2639_, v_i_2629_, v___x_2644_);
v_i_2629_ = v___x_2646_;
v_bs_2630_ = v___x_2647_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6___boxed(lean_object* v_sz_2651_, lean_object* v_i_2652_, lean_object* v_bs_2653_){
_start:
{
size_t v_sz_boxed_2654_; size_t v_i_boxed_2655_; lean_object* v_res_2656_; 
v_sz_boxed_2654_ = lean_unbox_usize(v_sz_2651_);
lean_dec(v_sz_2651_);
v_i_boxed_2655_ = lean_unbox_usize(v_i_2652_);
lean_dec(v_i_2652_);
v_res_2656_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(v_sz_boxed_2654_, v_i_boxed_2655_, v_bs_2653_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4___redArg(lean_object* v_inst_2657_, lean_object* v_declInfos_2658_, lean_object* v_k_2659_, uint8_t v_kind_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
_start:
{
size_t v_sz_2669_; size_t v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v_sz_2669_ = lean_array_size(v_declInfos_2658_);
v___x_2670_ = ((size_t)0ULL);
v___x_2671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(v_sz_2669_, v___x_2670_, v_declInfos_2658_);
v___x_2672_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___redArg(v_inst_2657_, v___x_2671_, v_k_2659_, v_kind_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4___redArg___boxed(lean_object* v_inst_2673_, lean_object* v_declInfos_2674_, lean_object* v_k_2675_, lean_object* v_kind_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
uint8_t v_kind_boxed_2685_; lean_object* v_res_2686_; 
v_kind_boxed_2685_ = lean_unbox(v_kind_2676_);
v_res_2686_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4___redArg(v_inst_2673_, v_declInfos_2674_, v_k_2675_, v_kind_boxed_2685_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
lean_dec(v_inst_2673_);
return v_res_2686_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0(uint8_t v___y_2694_, uint8_t v_suppressElabErrors_2695_, lean_object* v_x_2696_){
_start:
{
if (lean_obj_tag(v_x_2696_) == 1)
{
lean_object* v_pre_2697_; 
v_pre_2697_ = lean_ctor_get(v_x_2696_, 0);
switch(lean_obj_tag(v_pre_2697_))
{
case 1:
{
lean_object* v_pre_2698_; 
v_pre_2698_ = lean_ctor_get(v_pre_2697_, 0);
switch(lean_obj_tag(v_pre_2698_))
{
case 0:
{
lean_object* v_str_2699_; lean_object* v_str_2700_; lean_object* v___x_2701_; uint8_t v___x_2702_; 
v_str_2699_ = lean_ctor_get(v_x_2696_, 1);
v_str_2700_ = lean_ctor_get(v_pre_2697_, 1);
v___x_2701_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65));
v___x_2702_ = lean_string_dec_eq(v_str_2700_, v___x_2701_);
if (v___x_2702_ == 0)
{
lean_object* v___x_2703_; uint8_t v___x_2704_; 
v___x_2703_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__0));
v___x_2704_ = lean_string_dec_eq(v_str_2700_, v___x_2703_);
if (v___x_2704_ == 0)
{
return v___y_2694_;
}
else
{
lean_object* v___x_2705_; uint8_t v___x_2706_; 
v___x_2705_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__1));
v___x_2706_ = lean_string_dec_eq(v_str_2699_, v___x_2705_);
if (v___x_2706_ == 0)
{
return v___y_2694_;
}
else
{
return v_suppressElabErrors_2695_;
}
}
}
else
{
lean_object* v___x_2707_; uint8_t v___x_2708_; 
v___x_2707_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__2));
v___x_2708_ = lean_string_dec_eq(v_str_2699_, v___x_2707_);
if (v___x_2708_ == 0)
{
return v___y_2694_;
}
else
{
return v_suppressElabErrors_2695_;
}
}
}
case 1:
{
lean_object* v_pre_2709_; 
v_pre_2709_ = lean_ctor_get(v_pre_2698_, 0);
if (lean_obj_tag(v_pre_2709_) == 0)
{
lean_object* v_str_2710_; lean_object* v_str_2711_; lean_object* v_str_2712_; lean_object* v___x_2713_; uint8_t v___x_2714_; 
v_str_2710_ = lean_ctor_get(v_x_2696_, 1);
v_str_2711_ = lean_ctor_get(v_pre_2697_, 1);
v_str_2712_ = lean_ctor_get(v_pre_2698_, 1);
v___x_2713_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__3));
v___x_2714_ = lean_string_dec_eq(v_str_2712_, v___x_2713_);
if (v___x_2714_ == 0)
{
return v___y_2694_;
}
else
{
lean_object* v___x_2715_; uint8_t v___x_2716_; 
v___x_2715_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__4));
v___x_2716_ = lean_string_dec_eq(v_str_2711_, v___x_2715_);
if (v___x_2716_ == 0)
{
return v___y_2694_;
}
else
{
lean_object* v___x_2717_; uint8_t v___x_2718_; 
v___x_2717_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__5));
v___x_2718_ = lean_string_dec_eq(v_str_2710_, v___x_2717_);
if (v___x_2718_ == 0)
{
return v___y_2694_;
}
else
{
return v_suppressElabErrors_2695_;
}
}
}
}
else
{
return v___y_2694_;
}
}
default: 
{
return v___y_2694_;
}
}
}
case 0:
{
lean_object* v_str_2719_; lean_object* v___x_2720_; uint8_t v___x_2721_; 
v_str_2719_ = lean_ctor_get(v_x_2696_, 1);
v___x_2720_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__6));
v___x_2721_ = lean_string_dec_eq(v_str_2719_, v___x_2720_);
if (v___x_2721_ == 0)
{
return v___y_2694_;
}
else
{
return v_suppressElabErrors_2695_;
}
}
default: 
{
return v___y_2694_;
}
}
}
else
{
return v___y_2694_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___boxed(lean_object* v___y_2722_, lean_object* v_suppressElabErrors_2723_, lean_object* v_x_2724_){
_start:
{
uint8_t v___y_80346__boxed_2725_; uint8_t v_suppressElabErrors_boxed_2726_; uint8_t v_res_2727_; lean_object* v_r_2728_; 
v___y_80346__boxed_2725_ = lean_unbox(v___y_2722_);
v_suppressElabErrors_boxed_2726_ = lean_unbox(v_suppressElabErrors_2723_);
v_res_2727_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0(v___y_80346__boxed_2725_, v_suppressElabErrors_boxed_2726_, v_x_2724_);
lean_dec(v_x_2724_);
v_r_2728_ = lean_box(v_res_2727_);
return v_r_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg(lean_object* v_ref_2729_, lean_object* v_msgData_2730_, uint8_t v_severity_2731_, uint8_t v_isSilent_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v___y_2743_; uint8_t v___y_2744_; uint8_t v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2775_; lean_object* v___y_2776_; uint8_t v___y_2777_; uint8_t v___y_2778_; lean_object* v___y_2779_; uint8_t v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; uint8_t v___y_2803_; uint8_t v___y_2804_; uint8_t v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2811_; lean_object* v___y_2812_; uint8_t v___y_2813_; lean_object* v___y_2814_; uint8_t v___y_2815_; lean_object* v___y_2816_; uint8_t v___y_2817_; uint8_t v___x_2822_; lean_object* v___y_2824_; uint8_t v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; uint8_t v___y_2829_; uint8_t v___y_2830_; uint8_t v___y_2832_; uint8_t v___x_2847_; 
v___x_2822_ = 2;
v___x_2847_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2731_, v___x_2822_);
if (v___x_2847_ == 0)
{
v___y_2832_ = v___x_2847_;
goto v___jp_2831_;
}
else
{
uint8_t v___x_2848_; 
lean_inc_ref(v_msgData_2730_);
v___x_2848_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2730_);
v___y_2832_ = v___x_2848_;
goto v___jp_2831_;
}
v___jp_2738_:
{
lean_object* v___x_2748_; lean_object* v_currNamespace_2749_; lean_object* v_openDecls_2750_; lean_object* v_env_2751_; lean_object* v_nextMacroScope_2752_; lean_object* v_ngen_2753_; lean_object* v_auxDeclNGen_2754_; lean_object* v_traceState_2755_; lean_object* v_cache_2756_; lean_object* v_messages_2757_; lean_object* v_infoState_2758_; lean_object* v_snapshotTasks_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2773_; 
v___x_2748_ = lean_st_ref_take(v___y_2747_);
v_currNamespace_2749_ = lean_ctor_get(v___y_2746_, 6);
lean_inc(v_currNamespace_2749_);
v_openDecls_2750_ = lean_ctor_get(v___y_2746_, 7);
lean_inc(v_openDecls_2750_);
lean_dec_ref(v___y_2746_);
v_env_2751_ = lean_ctor_get(v___x_2748_, 0);
v_nextMacroScope_2752_ = lean_ctor_get(v___x_2748_, 1);
v_ngen_2753_ = lean_ctor_get(v___x_2748_, 2);
v_auxDeclNGen_2754_ = lean_ctor_get(v___x_2748_, 3);
v_traceState_2755_ = lean_ctor_get(v___x_2748_, 4);
v_cache_2756_ = lean_ctor_get(v___x_2748_, 5);
v_messages_2757_ = lean_ctor_get(v___x_2748_, 6);
v_infoState_2758_ = lean_ctor_get(v___x_2748_, 7);
v_snapshotTasks_2759_ = lean_ctor_get(v___x_2748_, 8);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2761_ = v___x_2748_;
v_isShared_2762_ = v_isSharedCheck_2773_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_snapshotTasks_2759_);
lean_inc(v_infoState_2758_);
lean_inc(v_messages_2757_);
lean_inc(v_cache_2756_);
lean_inc(v_traceState_2755_);
lean_inc(v_auxDeclNGen_2754_);
lean_inc(v_ngen_2753_);
lean_inc(v_nextMacroScope_2752_);
lean_inc(v_env_2751_);
lean_dec(v___x_2748_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2773_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2768_; 
v___x_2763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2763_, 0, v_currNamespace_2749_);
lean_ctor_set(v___x_2763_, 1, v_openDecls_2750_);
v___x_2764_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2763_);
lean_ctor_set(v___x_2764_, 1, v___y_2741_);
v___x_2765_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2765_, 0, v___y_2740_);
lean_ctor_set(v___x_2765_, 1, v___y_2739_);
lean_ctor_set(v___x_2765_, 2, v___y_2742_);
lean_ctor_set(v___x_2765_, 3, v___y_2743_);
lean_ctor_set(v___x_2765_, 4, v___x_2764_);
lean_ctor_set_uint8(v___x_2765_, sizeof(void*)*5, v___y_2745_);
lean_ctor_set_uint8(v___x_2765_, sizeof(void*)*5 + 1, v___y_2744_);
lean_ctor_set_uint8(v___x_2765_, sizeof(void*)*5 + 2, v_isSilent_2732_);
v___x_2766_ = l_Lean_MessageLog_add(v___x_2765_, v_messages_2757_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 6, v___x_2766_);
v___x_2768_ = v___x_2761_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_env_2751_);
lean_ctor_set(v_reuseFailAlloc_2772_, 1, v_nextMacroScope_2752_);
lean_ctor_set(v_reuseFailAlloc_2772_, 2, v_ngen_2753_);
lean_ctor_set(v_reuseFailAlloc_2772_, 3, v_auxDeclNGen_2754_);
lean_ctor_set(v_reuseFailAlloc_2772_, 4, v_traceState_2755_);
lean_ctor_set(v_reuseFailAlloc_2772_, 5, v_cache_2756_);
lean_ctor_set(v_reuseFailAlloc_2772_, 6, v___x_2766_);
lean_ctor_set(v_reuseFailAlloc_2772_, 7, v_infoState_2758_);
lean_ctor_set(v_reuseFailAlloc_2772_, 8, v_snapshotTasks_2759_);
v___x_2768_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2769_ = lean_st_ref_set(v___y_2747_, v___x_2768_);
v___x_2770_ = lean_box(0);
v___x_2771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2771_, 0, v___x_2770_);
return v___x_2771_;
}
}
}
v___jp_2774_:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2798_; 
v___x_2783_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2730_);
v___x_2784_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(v___x_2783_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2787_ = v___x_2784_;
v_isShared_2788_ = v_isSharedCheck_2798_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2784_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2798_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
lean_inc_ref(v___y_2781_);
v___x_2789_ = l_Lean_FileMap_toPosition(v___y_2781_, v___y_2779_);
lean_dec(v___y_2779_);
v___x_2790_ = l_Lean_FileMap_toPosition(v___y_2781_, v___y_2782_);
lean_dec(v___y_2782_);
v___x_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2790_);
v___x_2792_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__63));
if (v___y_2777_ == 0)
{
lean_del_object(v___x_2787_);
lean_dec_ref(v___y_2775_);
v___y_2739_ = v___x_2789_;
v___y_2740_ = v___y_2776_;
v___y_2741_ = v_a_2785_;
v___y_2742_ = v___x_2791_;
v___y_2743_ = v___x_2792_;
v___y_2744_ = v___y_2778_;
v___y_2745_ = v___y_2780_;
v___y_2746_ = v___y_2735_;
v___y_2747_ = v___y_2736_;
goto v___jp_2738_;
}
else
{
uint8_t v___x_2793_; 
lean_inc(v_a_2785_);
v___x_2793_ = l_Lean_MessageData_hasTag(v___y_2775_, v_a_2785_);
if (v___x_2793_ == 0)
{
lean_object* v___x_2794_; lean_object* v___x_2796_; 
lean_dec_ref(v___x_2791_);
lean_dec_ref(v___x_2789_);
lean_dec(v_a_2785_);
lean_dec_ref(v___y_2776_);
lean_dec_ref(v___y_2735_);
v___x_2794_ = lean_box(0);
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 0, v___x_2794_);
v___x_2796_ = v___x_2787_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2794_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
else
{
lean_del_object(v___x_2787_);
v___y_2739_ = v___x_2789_;
v___y_2740_ = v___y_2776_;
v___y_2741_ = v_a_2785_;
v___y_2742_ = v___x_2791_;
v___y_2743_ = v___x_2792_;
v___y_2744_ = v___y_2778_;
v___y_2745_ = v___y_2780_;
v___y_2746_ = v___y_2735_;
v___y_2747_ = v___y_2736_;
goto v___jp_2738_;
}
}
}
}
v___jp_2799_:
{
lean_object* v___x_2808_; 
v___x_2808_ = l_Lean_Syntax_getTailPos_x3f(v___y_2802_, v___y_2805_);
lean_dec(v___y_2802_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_inc(v___y_2807_);
v___y_2775_ = v___y_2800_;
v___y_2776_ = v___y_2801_;
v___y_2777_ = v___y_2803_;
v___y_2778_ = v___y_2804_;
v___y_2779_ = v___y_2807_;
v___y_2780_ = v___y_2805_;
v___y_2781_ = v___y_2806_;
v___y_2782_ = v___y_2807_;
goto v___jp_2774_;
}
else
{
lean_object* v_val_2809_; 
v_val_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_val_2809_);
lean_dec_ref(v___x_2808_);
v___y_2775_ = v___y_2800_;
v___y_2776_ = v___y_2801_;
v___y_2777_ = v___y_2803_;
v___y_2778_ = v___y_2804_;
v___y_2779_ = v___y_2807_;
v___y_2780_ = v___y_2805_;
v___y_2781_ = v___y_2806_;
v___y_2782_ = v_val_2809_;
goto v___jp_2774_;
}
}
v___jp_2810_:
{
lean_object* v_ref_2818_; lean_object* v___x_2819_; 
v_ref_2818_ = l_Lean_replaceRef(v_ref_2729_, v___y_2814_);
lean_dec(v___y_2814_);
v___x_2819_ = l_Lean_Syntax_getPos_x3f(v_ref_2818_, v___y_2815_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v___x_2820_; 
v___x_2820_ = lean_unsigned_to_nat(0u);
v___y_2800_ = v___y_2811_;
v___y_2801_ = v___y_2812_;
v___y_2802_ = v_ref_2818_;
v___y_2803_ = v___y_2813_;
v___y_2804_ = v___y_2817_;
v___y_2805_ = v___y_2815_;
v___y_2806_ = v___y_2816_;
v___y_2807_ = v___x_2820_;
goto v___jp_2799_;
}
else
{
lean_object* v_val_2821_; 
v_val_2821_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_val_2821_);
lean_dec_ref(v___x_2819_);
v___y_2800_ = v___y_2811_;
v___y_2801_ = v___y_2812_;
v___y_2802_ = v_ref_2818_;
v___y_2803_ = v___y_2813_;
v___y_2804_ = v___y_2817_;
v___y_2805_ = v___y_2815_;
v___y_2806_ = v___y_2816_;
v___y_2807_ = v_val_2821_;
goto v___jp_2799_;
}
}
v___jp_2823_:
{
if (v___y_2830_ == 0)
{
v___y_2811_ = v___y_2826_;
v___y_2812_ = v___y_2824_;
v___y_2813_ = v___y_2825_;
v___y_2814_ = v___y_2827_;
v___y_2815_ = v___y_2829_;
v___y_2816_ = v___y_2828_;
v___y_2817_ = v_severity_2731_;
goto v___jp_2810_;
}
else
{
v___y_2811_ = v___y_2826_;
v___y_2812_ = v___y_2824_;
v___y_2813_ = v___y_2825_;
v___y_2814_ = v___y_2827_;
v___y_2815_ = v___y_2829_;
v___y_2816_ = v___y_2828_;
v___y_2817_ = v___x_2822_;
goto v___jp_2810_;
}
}
v___jp_2831_:
{
if (v___y_2832_ == 0)
{
lean_object* v_fileName_2833_; lean_object* v_fileMap_2834_; lean_object* v_options_2835_; lean_object* v_ref_2836_; uint8_t v_suppressElabErrors_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___f_2840_; uint8_t v___x_2841_; uint8_t v___x_2842_; 
v_fileName_2833_ = lean_ctor_get(v___y_2735_, 0);
v_fileMap_2834_ = lean_ctor_get(v___y_2735_, 1);
v_options_2835_ = lean_ctor_get(v___y_2735_, 2);
v_ref_2836_ = lean_ctor_get(v___y_2735_, 5);
v_suppressElabErrors_2837_ = lean_ctor_get_uint8(v___y_2735_, sizeof(void*)*14 + 1);
v___x_2838_ = lean_box(v___y_2832_);
v___x_2839_ = lean_box(v_suppressElabErrors_2837_);
v___f_2840_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2840_, 0, v___x_2838_);
lean_closure_set(v___f_2840_, 1, v___x_2839_);
v___x_2841_ = 1;
v___x_2842_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2731_, v___x_2841_);
if (v___x_2842_ == 0)
{
lean_inc_ref(v_fileMap_2834_);
lean_inc(v_ref_2836_);
lean_inc_ref(v_fileName_2833_);
v___y_2824_ = v_fileName_2833_;
v___y_2825_ = v_suppressElabErrors_2837_;
v___y_2826_ = v___f_2840_;
v___y_2827_ = v_ref_2836_;
v___y_2828_ = v_fileMap_2834_;
v___y_2829_ = v___y_2832_;
v___y_2830_ = v___x_2842_;
goto v___jp_2823_;
}
else
{
lean_object* v___x_2843_; uint8_t v___x_2844_; 
v___x_2843_ = l_Lean_warningAsError;
v___x_2844_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5(v_options_2835_, v___x_2843_);
lean_inc_ref(v_fileMap_2834_);
lean_inc(v_ref_2836_);
lean_inc_ref(v_fileName_2833_);
v___y_2824_ = v_fileName_2833_;
v___y_2825_ = v_suppressElabErrors_2837_;
v___y_2826_ = v___f_2840_;
v___y_2827_ = v_ref_2836_;
v___y_2828_ = v_fileMap_2834_;
v___y_2829_ = v___y_2832_;
v___y_2830_ = v___x_2844_;
goto v___jp_2823_;
}
}
else
{
lean_object* v___x_2845_; lean_object* v___x_2846_; 
lean_dec_ref(v___y_2735_);
lean_dec_ref(v_msgData_2730_);
v___x_2845_ = lean_box(0);
v___x_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2845_);
return v___x_2846_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___boxed(lean_object* v_ref_2849_, lean_object* v_msgData_2850_, lean_object* v_severity_2851_, lean_object* v_isSilent_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_){
_start:
{
uint8_t v_severity_boxed_2858_; uint8_t v_isSilent_boxed_2859_; lean_object* v_res_2860_; 
v_severity_boxed_2858_ = lean_unbox(v_severity_2851_);
v_isSilent_boxed_2859_ = lean_unbox(v_isSilent_2852_);
v_res_2860_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg(v_ref_2849_, v_msgData_2850_, v_severity_boxed_2858_, v_isSilent_boxed_2859_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
lean_dec(v___y_2856_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec(v_ref_2849_);
return v_res_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10(lean_object* v_msgData_2861_, uint8_t v_severity_2862_, uint8_t v_isSilent_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_){
_start:
{
lean_object* v_ref_2872_; lean_object* v___x_2873_; 
v_ref_2872_ = lean_ctor_get(v___y_2869_, 5);
lean_inc(v_ref_2872_);
v___x_2873_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg(v_ref_2872_, v_msgData_2861_, v_severity_2862_, v_isSilent_2863_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_);
lean_dec(v_ref_2872_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10___boxed(lean_object* v_msgData_2874_, lean_object* v_severity_2875_, lean_object* v_isSilent_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
uint8_t v_severity_boxed_2885_; uint8_t v_isSilent_boxed_2886_; lean_object* v_res_2887_; 
v_severity_boxed_2885_ = lean_unbox(v_severity_2875_);
v_isSilent_boxed_2886_ = lean_unbox(v_isSilent_2876_);
v_res_2887_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10(v_msgData_2874_, v_severity_boxed_2885_, v_isSilent_boxed_2886_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
lean_dec(v___y_2883_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec_ref(v___y_2877_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6(lean_object* v_msgData_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_){
_start:
{
uint8_t v___x_2897_; uint8_t v___x_2898_; lean_object* v___x_2899_; 
v___x_2897_ = 2;
v___x_2898_ = 0;
v___x_2899_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10(v_msgData_2888_, v___x_2897_, v___x_2898_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6___boxed(lean_object* v_msgData_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l_Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6(v_msgData_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
lean_dec(v___y_2907_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec_ref(v___y_2901_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__8(lean_object* v_a_2910_, lean_object* v_as_2911_, size_t v_i_2912_, size_t v_stop_2913_, lean_object* v_b_2914_){
_start:
{
lean_object* v___y_2916_; uint8_t v___x_2920_; 
v___x_2920_ = lean_usize_dec_eq(v_i_2912_, v_stop_2913_);
if (v___x_2920_ == 0)
{
lean_object* v_reassigns_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; uint8_t v___x_2924_; 
v_reassigns_2921_ = lean_ctor_get(v_a_2910_, 1);
v___x_2922_ = lean_array_uget_borrowed(v_as_2911_, v_i_2912_);
v___x_2923_ = l_Lean_TSyntax_getId(v___x_2922_);
v___x_2924_ = l_Lean_NameSet_contains(v_reassigns_2921_, v___x_2923_);
lean_dec(v___x_2923_);
if (v___x_2924_ == 0)
{
v___y_2916_ = v_b_2914_;
goto v___jp_2915_;
}
else
{
lean_object* v___x_2925_; 
lean_inc(v___x_2922_);
v___x_2925_ = lean_array_push(v_b_2914_, v___x_2922_);
v___y_2916_ = v___x_2925_;
goto v___jp_2915_;
}
}
else
{
return v_b_2914_;
}
v___jp_2915_:
{
size_t v___x_2917_; size_t v___x_2918_; 
v___x_2917_ = ((size_t)1ULL);
v___x_2918_ = lean_usize_add(v_i_2912_, v___x_2917_);
v_i_2912_ = v___x_2918_;
v_b_2914_ = v___y_2916_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__8___boxed(lean_object* v_a_2926_, lean_object* v_as_2927_, lean_object* v_i_2928_, lean_object* v_stop_2929_, lean_object* v_b_2930_){
_start:
{
size_t v_i_boxed_2931_; size_t v_stop_boxed_2932_; lean_object* v_res_2933_; 
v_i_boxed_2931_ = lean_unbox_usize(v_i_2928_);
lean_dec(v_i_2928_);
v_stop_boxed_2932_ = lean_unbox_usize(v_stop_2929_);
lean_dec(v_stop_2929_);
v_res_2933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__8(v_a_2926_, v_as_2927_, v_i_boxed_2931_, v_stop_boxed_2932_, v_b_2930_);
lean_dec_ref(v_as_2927_);
lean_dec_ref(v_a_2926_);
return v_res_2933_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__7(size_t v_sz_2934_, size_t v_i_2935_, lean_object* v_bs_2936_){
_start:
{
uint8_t v___x_2937_; 
v___x_2937_ = lean_usize_dec_lt(v_i_2935_, v_sz_2934_);
if (v___x_2937_ == 0)
{
return v_bs_2936_;
}
else
{
lean_object* v_v_2938_; lean_object* v___x_2939_; lean_object* v_bs_x27_2940_; lean_object* v___x_2941_; size_t v___x_2942_; size_t v___x_2943_; lean_object* v___x_2944_; 
v_v_2938_ = lean_array_uget(v_bs_2936_, v_i_2935_);
v___x_2939_ = lean_unsigned_to_nat(0u);
v_bs_x27_2940_ = lean_array_uset(v_bs_2936_, v_i_2935_, v___x_2939_);
v___x_2941_ = l_Lean_TSyntax_getId(v_v_2938_);
lean_dec(v_v_2938_);
v___x_2942_ = ((size_t)1ULL);
v___x_2943_ = lean_usize_add(v_i_2935_, v___x_2942_);
v___x_2944_ = lean_array_uset(v_bs_x27_2940_, v_i_2935_, v___x_2941_);
v_i_2935_ = v___x_2943_;
v_bs_2936_ = v___x_2944_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__7___boxed(lean_object* v_sz_2946_, lean_object* v_i_2947_, lean_object* v_bs_2948_){
_start:
{
size_t v_sz_boxed_2949_; size_t v_i_boxed_2950_; lean_object* v_res_2951_; 
v_sz_boxed_2949_ = lean_unbox_usize(v_sz_2946_);
lean_dec(v_sz_2946_);
v_i_boxed_2950_ = lean_unbox_usize(v_i_2947_);
lean_dec(v_i_2947_);
v_res_2951_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__7(v_sz_boxed_2949_, v_i_boxed_2950_, v_bs_2948_);
return v_res_2951_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___closed__12(void){
_start:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2972_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__11));
v___x_2973_ = l_Lean_stringToMessageData(v___x_2972_);
return v___x_2973_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___closed__14(void){
_start:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; 
v___x_2975_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__13));
v___x_2976_ = l_Lean_stringToMessageData(v___x_2975_);
return v___x_2976_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___closed__16(void){
_start:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2978_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__15));
v___x_2979_ = l_Lean_stringToMessageData(v___x_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor(lean_object* v_stx_2989_, lean_object* v_dec_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_){
_start:
{
lean_object* v___x_2999_; uint8_t v___x_3000_; 
v___x_2999_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
lean_inc(v_stx_2989_);
v___x_3000_ = l_Lean_Syntax_isOfKind(v_stx_2989_, v___x_2999_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; 
lean_dec(v_a_2997_);
lean_dec_ref(v_a_2996_);
lean_dec(v_a_2995_);
lean_dec_ref(v_a_2994_);
lean_dec(v_a_2993_);
lean_dec_ref(v_a_2992_);
lean_dec_ref(v_a_2991_);
lean_dec_ref(v_dec_2990_);
lean_dec(v_stx_2989_);
v___x_3001_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_3001_;
}
else
{
lean_object* v___x_3002_; lean_object* v___x_3003_; uint8_t v___x_3004_; 
v___x_3002_ = lean_unsigned_to_nat(1u);
v___x_3003_ = l_Lean_Syntax_getArg(v_stx_2989_, v___x_3002_);
lean_inc(v___x_3003_);
v___x_3004_ = l_Lean_Syntax_matchesNull(v___x_3003_, v___x_3002_);
if (v___x_3004_ == 0)
{
lean_object* v___x_3005_; 
lean_dec(v___x_3003_);
lean_dec(v_a_2997_);
lean_dec_ref(v_a_2996_);
lean_dec(v_a_2995_);
lean_dec_ref(v_a_2994_);
lean_dec(v_a_2993_);
lean_dec_ref(v_a_2992_);
lean_dec_ref(v_a_2991_);
lean_dec_ref(v_dec_2990_);
lean_dec(v_stx_2989_);
v___x_3005_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_3005_;
}
else
{
lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; uint8_t v___x_3009_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; uint8_t v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3045_; lean_object* v___y_3046_; uint8_t v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v_fst_3068_; lean_object* v_snd_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3104_; lean_object* v___y_3105_; uint8_t v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; uint8_t v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3221_; lean_object* v___y_3222_; uint8_t v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; uint8_t v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; uint8_t v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; uint8_t v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v_h_x3f_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; 
v___x_3006_ = lean_unsigned_to_nat(0u);
v___x_3007_ = l_Lean_Syntax_getArg(v___x_3003_, v___x_3006_);
lean_dec(v___x_3003_);
v___x_3008_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
lean_inc(v___x_3007_);
v___x_3009_ = l_Lean_Syntax_isOfKind(v___x_3007_, v___x_3008_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3455_; 
lean_dec(v___x_3007_);
lean_dec(v_a_2997_);
lean_dec_ref(v_a_2996_);
lean_dec(v_a_2995_);
lean_dec_ref(v_a_2994_);
lean_dec(v_a_2993_);
lean_dec_ref(v_a_2992_);
lean_dec_ref(v_a_2991_);
lean_dec_ref(v_dec_2990_);
lean_dec(v_stx_2989_);
v___x_3455_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_3455_;
}
else
{
lean_object* v___x_3456_; uint8_t v___x_3457_; 
v___x_3456_ = l_Lean_Syntax_getArg(v___x_3007_, v___x_3006_);
v___x_3457_ = l_Lean_Syntax_isNone(v___x_3456_);
if (v___x_3457_ == 0)
{
lean_object* v___x_3458_; uint8_t v___x_3459_; 
v___x_3458_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3456_);
v___x_3459_ = l_Lean_Syntax_matchesNull(v___x_3456_, v___x_3458_);
if (v___x_3459_ == 0)
{
lean_object* v___x_3460_; 
lean_dec(v___x_3456_);
lean_dec(v___x_3007_);
lean_dec(v_a_2997_);
lean_dec_ref(v_a_2996_);
lean_dec(v_a_2995_);
lean_dec_ref(v_a_2994_);
lean_dec(v_a_2993_);
lean_dec_ref(v_a_2992_);
lean_dec_ref(v_a_2991_);
lean_dec_ref(v_dec_2990_);
lean_dec(v_stx_2989_);
v___x_3460_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_3460_;
}
else
{
lean_object* v_h_x3f_3461_; lean_object* v___x_3462_; 
v_h_x3f_3461_ = l_Lean_Syntax_getArg(v___x_3456_, v___x_3006_);
lean_dec(v___x_3456_);
v___x_3462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3462_, 0, v_h_x3f_3461_);
v_h_x3f_3333_ = v___x_3462_;
v___y_3334_ = v_a_2991_;
v___y_3335_ = v_a_2992_;
v___y_3336_ = v_a_2993_;
v___y_3337_ = v_a_2994_;
v___y_3338_ = v_a_2995_;
v___y_3339_ = v_a_2996_;
v___y_3340_ = v_a_2997_;
goto v___jp_3332_;
}
}
else
{
lean_object* v___x_3463_; 
lean_dec(v___x_3456_);
v___x_3463_ = lean_box(0);
v_h_x3f_3333_ = v___x_3463_;
v___y_3334_ = v_a_2991_;
v___y_3335_ = v_a_2992_;
v___y_3336_ = v_a_2993_;
v___y_3337_ = v_a_2994_;
v___y_3338_ = v_a_2995_;
v___y_3339_ = v_a_2996_;
v___y_3340_ = v_a_2997_;
goto v___jp_3332_;
}
}
v___jp_3010_:
{
lean_object* v___x_3031_; uint8_t v___x_3032_; lean_object* v___x_3033_; 
v___x_3031_ = l_Lean_instInhabitedExpr;
v___x_3032_ = 0;
lean_inc(v___y_3027_);
lean_inc_ref(v___y_3026_);
lean_inc(v___y_3022_);
lean_inc_ref(v___y_3028_);
lean_inc(v___y_3023_);
lean_inc_ref(v___y_3029_);
lean_inc_ref(v___y_3025_);
v___x_3033_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4___redArg(v___x_3031_, v___y_3030_, v___y_3011_, v___x_3032_, v___y_3025_, v___y_3029_, v___y_3023_, v___y_3028_, v___y_3022_, v___y_3026_, v___y_3027_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_object* v_a_3034_; lean_object* v_doBlockResultType_3035_; lean_object* v___x_3036_; lean_object* v___y_3037_; lean_object* v___x_3038_; lean_object* v___f_3039_; lean_object* v___x_3040_; 
v_a_3034_ = lean_ctor_get(v___x_3033_, 0);
lean_inc(v_a_3034_);
lean_dec_ref(v___x_3033_);
v_doBlockResultType_3035_ = lean_ctor_get(v___y_3025_, 3);
lean_inc_ref(v_doBlockResultType_3035_);
v___x_3036_ = lean_box(v___y_3014_);
lean_inc_ref(v_doBlockResultType_3035_);
v___y_3037_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__10___boxed), 19, 11);
lean_closure_set(v___y_3037_, 0, v___x_3036_);
lean_closure_set(v___y_3037_, 1, v_dec_2990_);
lean_closure_set(v___y_3037_, 2, v___y_3018_);
lean_closure_set(v___y_3037_, 3, v_doBlockResultType_3035_);
lean_closure_set(v___y_3037_, 4, v___y_3012_);
lean_closure_set(v___y_3037_, 5, v___y_3013_);
lean_closure_set(v___y_3037_, 6, v___y_3020_);
lean_closure_set(v___y_3037_, 7, v___y_3019_);
lean_closure_set(v___y_3037_, 8, v___y_3017_);
lean_closure_set(v___y_3037_, 9, v___x_3006_);
lean_closure_set(v___y_3037_, 10, v___x_3002_);
v___x_3038_ = lean_box(v___x_3009_);
v___f_3039_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__11___boxed), 13, 4);
lean_closure_set(v___f_3039_, 0, v___y_3015_);
lean_closure_set(v___f_3039_, 1, v___y_3037_);
lean_closure_set(v___f_3039_, 2, v___x_3002_);
lean_closure_set(v___f_3039_, 3, v___x_3038_);
lean_inc(v___y_3027_);
lean_inc_ref(v___y_3026_);
lean_inc(v___y_3022_);
lean_inc_ref(v___y_3028_);
lean_inc(v___y_3023_);
lean_inc_ref(v___y_3029_);
lean_inc_ref(v___y_3025_);
lean_inc_ref(v___y_3024_);
v___x_3040_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(v___y_3016_, v___y_3024_, v___f_3039_, v___y_3025_, v___y_3029_, v___y_3023_, v___y_3028_, v___y_3022_, v___y_3026_, v___y_3027_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v_a_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
lean_inc(v_a_3041_);
lean_dec_ref(v___x_3040_);
v___x_3042_ = l_Lean_Expr_app___override(v___y_3021_, v_a_3034_);
v___x_3043_ = l_Lean_Elab_Do_mkBindApp(v___y_3024_, v_doBlockResultType_3035_, v___x_3042_, v_a_3041_, v___y_3025_, v___y_3029_, v___y_3023_, v___y_3028_, v___y_3022_, v___y_3026_, v___y_3027_);
return v___x_3043_;
}
else
{
lean_dec_ref(v_doBlockResultType_3035_);
lean_dec(v_a_3034_);
lean_dec_ref(v___y_3029_);
lean_dec_ref(v___y_3028_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec_ref(v___y_3024_);
lean_dec(v___y_3023_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
return v___x_3040_;
}
}
else
{
lean_dec_ref(v___y_3029_);
lean_dec_ref(v___y_3028_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec_ref(v___y_3024_);
lean_dec(v___y_3023_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec(v___y_3015_);
lean_dec(v___y_3013_);
lean_dec_ref(v___y_3012_);
lean_dec_ref(v_dec_2990_);
return v___x_3033_;
}
}
v___jp_3044_:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3077_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17));
lean_inc(v___y_3076_);
lean_inc_ref(v___y_3075_);
v___x_3078_ = l_Lean_Core_mkFreshUserName(v___x_3077_, v___y_3075_, v___y_3076_);
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_object* v_a_3079_; lean_object* v___x_3080_; lean_object* v___f_3081_; 
v_a_3079_ = lean_ctor_get(v___x_3078_, 0);
lean_inc(v_a_3079_);
lean_dec_ref(v___x_3078_);
v___x_3080_ = lean_box(v___x_3009_);
lean_inc(v_a_3079_);
lean_inc(v___y_3057_);
lean_inc_ref(v___y_3049_);
lean_inc(v___y_3053_);
lean_inc_ref(v___y_3055_);
v___f_3081_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__9___boxed), 20, 11);
lean_closure_set(v___f_3081_, 0, v___y_3055_);
lean_closure_set(v___f_3081_, 1, v___y_3053_);
lean_closure_set(v___f_3081_, 2, v___y_3049_);
lean_closure_set(v___f_3081_, 3, v___y_3058_);
lean_closure_set(v___f_3081_, 4, v___y_3061_);
lean_closure_set(v___f_3081_, 5, v___y_3051_);
lean_closure_set(v___f_3081_, 6, v___y_3054_);
lean_closure_set(v___f_3081_, 7, v___y_3059_);
lean_closure_set(v___f_3081_, 8, v___x_3080_);
lean_closure_set(v___f_3081_, 9, v___y_3057_);
lean_closure_set(v___f_3081_, 10, v_a_3079_);
if (lean_obj_tag(v___y_3065_) == 1)
{
if (lean_obj_tag(v_snd_3069_) == 1)
{
lean_object* v_val_3082_; lean_object* v_val_3083_; lean_object* v___f_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
lean_dec_ref(v___y_3064_);
v_val_3082_ = lean_ctor_get(v___y_3065_, 0);
lean_inc(v_val_3082_);
lean_dec_ref(v___y_3065_);
v_val_3083_ = lean_ctor_get(v_snd_3069_, 0);
lean_inc(v_val_3083_);
lean_dec_ref(v_snd_3069_);
v___f_3084_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__12___boxed), 16, 7);
lean_closure_set(v___f_3084_, 0, v___y_3060_);
lean_closure_set(v___f_3084_, 1, v___y_3045_);
lean_closure_set(v___f_3084_, 2, v___x_3006_);
lean_closure_set(v___f_3084_, 3, v___y_3050_);
lean_closure_set(v___f_3084_, 4, v___y_3048_);
lean_closure_set(v___f_3084_, 5, v_val_3083_);
lean_closure_set(v___f_3084_, 6, v___y_3046_);
v___x_3085_ = l_Lean_TSyntax_getId(v___y_3067_);
lean_dec(v___y_3067_);
v___x_3086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3085_);
lean_ctor_set(v___x_3086_, 1, v___y_3066_);
v___x_3087_ = l_Lean_TSyntax_getId(v_val_3082_);
lean_dec(v_val_3082_);
v___x_3088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3087_);
lean_ctor_set(v___x_3088_, 1, v___f_3084_);
v___x_3089_ = lean_unsigned_to_nat(2u);
v___x_3090_ = lean_mk_empty_array_with_capacity(v___x_3089_);
v___x_3091_ = lean_array_push(v___x_3090_, v___x_3086_);
v___x_3092_ = lean_array_push(v___x_3091_, v___x_3088_);
v___y_3011_ = v___f_3081_;
v___y_3012_ = v___y_3055_;
v___y_3013_ = v___y_3056_;
v___y_3014_ = v___y_3047_;
v___y_3015_ = v___y_3057_;
v___y_3016_ = v_a_3079_;
v___y_3017_ = v___y_3062_;
v___y_3018_ = v___y_3063_;
v___y_3019_ = v___y_3052_;
v___y_3020_ = v___y_3053_;
v___y_3021_ = v_fst_3068_;
v___y_3022_ = v___y_3074_;
v___y_3023_ = v___y_3072_;
v___y_3024_ = v___y_3049_;
v___y_3025_ = v___y_3070_;
v___y_3026_ = v___y_3075_;
v___y_3027_ = v___y_3076_;
v___y_3028_ = v___y_3073_;
v___y_3029_ = v___y_3071_;
v___y_3030_ = v___x_3092_;
goto v___jp_3010_;
}
else
{
lean_object* v___x_3093_; 
lean_dec(v___y_3067_);
lean_dec_ref(v___y_3066_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3050_);
lean_dec_ref(v___y_3048_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
v___x_3093_ = lean_apply_2(v___y_3064_, v___y_3065_, v_snd_3069_);
v___y_3011_ = v___f_3081_;
v___y_3012_ = v___y_3055_;
v___y_3013_ = v___y_3056_;
v___y_3014_ = v___y_3047_;
v___y_3015_ = v___y_3057_;
v___y_3016_ = v_a_3079_;
v___y_3017_ = v___y_3062_;
v___y_3018_ = v___y_3063_;
v___y_3019_ = v___y_3052_;
v___y_3020_ = v___y_3053_;
v___y_3021_ = v_fst_3068_;
v___y_3022_ = v___y_3074_;
v___y_3023_ = v___y_3072_;
v___y_3024_ = v___y_3049_;
v___y_3025_ = v___y_3070_;
v___y_3026_ = v___y_3075_;
v___y_3027_ = v___y_3076_;
v___y_3028_ = v___y_3073_;
v___y_3029_ = v___y_3071_;
v___y_3030_ = v___x_3093_;
goto v___jp_3010_;
}
}
else
{
lean_object* v___x_3094_; 
lean_dec(v___y_3067_);
lean_dec_ref(v___y_3066_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3050_);
lean_dec_ref(v___y_3048_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
v___x_3094_ = lean_apply_2(v___y_3064_, v___y_3065_, v_snd_3069_);
v___y_3011_ = v___f_3081_;
v___y_3012_ = v___y_3055_;
v___y_3013_ = v___y_3056_;
v___y_3014_ = v___y_3047_;
v___y_3015_ = v___y_3057_;
v___y_3016_ = v_a_3079_;
v___y_3017_ = v___y_3062_;
v___y_3018_ = v___y_3063_;
v___y_3019_ = v___y_3052_;
v___y_3020_ = v___y_3053_;
v___y_3021_ = v_fst_3068_;
v___y_3022_ = v___y_3074_;
v___y_3023_ = v___y_3072_;
v___y_3024_ = v___y_3049_;
v___y_3025_ = v___y_3070_;
v___y_3026_ = v___y_3075_;
v___y_3027_ = v___y_3076_;
v___y_3028_ = v___y_3073_;
v___y_3029_ = v___y_3071_;
v___y_3030_ = v___x_3094_;
goto v___jp_3010_;
}
}
else
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3102_; 
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec_ref(v___y_3070_);
lean_dec(v_snd_3069_);
lean_dec_ref(v_fst_3068_);
lean_dec(v___y_3067_);
lean_dec_ref(v___y_3066_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3061_);
lean_dec(v___y_3060_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec(v___y_3057_);
lean_dec(v___y_3056_);
lean_dec_ref(v___y_3055_);
lean_dec_ref(v___y_3054_);
lean_dec(v___y_3053_);
lean_dec_ref(v___y_3052_);
lean_dec(v___y_3051_);
lean_dec_ref(v___y_3050_);
lean_dec_ref(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v_dec_2990_);
v_a_3095_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3097_ = v___x_3078_;
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_3078_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3100_; 
if (v_isShared_3098_ == 0)
{
v___x_3100_ = v___x_3097_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_a_3095_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
}
v___jp_3103_:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3138_ = lean_box(0);
lean_inc(v___y_3137_);
lean_inc_ref(v___y_3136_);
lean_inc(v___y_3135_);
lean_inc_ref(v___y_3134_);
lean_inc(v___y_3133_);
lean_inc_ref(v___y_3132_);
v___x_3139_ = lean_apply_8(v___y_3126_, v___x_3138_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, lean_box(0));
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; lean_object* v_m_3141_; lean_object* v_u_3142_; lean_object* v_v_3143_; lean_object* v___x_3144_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
lean_inc(v_a_3140_);
lean_dec_ref(v___x_3139_);
v_m_3141_ = lean_ctor_get(v___y_3120_, 0);
lean_inc_ref(v_m_3141_);
v_u_3142_ = lean_ctor_get(v___y_3120_, 1);
lean_inc(v_u_3142_);
v_v_3143_ = lean_ctor_get(v___y_3120_, 2);
lean_inc(v_v_3143_);
lean_dec_ref(v___y_3120_);
lean_inc(v___y_3137_);
lean_inc_ref(v___y_3136_);
lean_inc(v___y_3135_);
lean_inc_ref(v___y_3134_);
lean_inc(v_u_3142_);
v___x_3144_ = l_Lean_Meta_mkProdMkN(v_a_3140_, v_u_3142_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v_a_3145_; 
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
lean_inc(v_a_3145_);
lean_dec_ref(v___x_3144_);
if (lean_obj_tag(v___y_3124_) == 0)
{
lean_object* v_fst_3146_; lean_object* v_snd_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3166_; 
v_fst_3146_ = lean_ctor_get(v_a_3145_, 0);
v_snd_3147_ = lean_ctor_get(v_a_3145_, 1);
v_isSharedCheck_3166_ = !lean_is_exclusive(v_a_3145_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3149_ = v_a_3145_;
v_isShared_3150_ = v_isSharedCheck_3166_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_snd_3147_);
lean_inc(v_fst_3146_);
lean_dec(v_a_3145_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3166_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3154_; 
v___x_3151_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__1));
v___x_3152_ = lean_box(0);
lean_inc(v_v_3143_);
if (v_isShared_3150_ == 0)
{
lean_ctor_set_tag(v___x_3149_, 1);
lean_ctor_set(v___x_3149_, 1, v___x_3152_);
lean_ctor_set(v___x_3149_, 0, v_v_3143_);
v___x_3154_ = v___x_3149_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_v_3143_);
lean_ctor_set(v_reuseFailAlloc_3165_, 1, v___x_3152_);
v___x_3154_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; 
lean_inc(v_u_3142_);
v___x_3155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3155_, 0, v_u_3142_);
lean_ctor_set(v___x_3155_, 1, v___x_3154_);
v___x_3156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3156_, 0, v___y_3119_);
lean_ctor_set(v___x_3156_, 1, v___x_3155_);
v___x_3157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3157_, 0, v___y_3127_);
lean_ctor_set(v___x_3157_, 1, v___x_3156_);
lean_inc_ref(v___x_3157_);
v___x_3158_ = l_Lean_mkConst(v___x_3151_, v___x_3157_);
lean_inc_ref(v___y_3128_);
lean_inc_ref(v___y_3122_);
lean_inc_ref(v_m_3141_);
v___x_3159_ = l_Lean_mkApp3(v___x_3158_, v_m_3141_, v___y_3122_, v___y_3128_);
lean_inc(v___y_3137_);
lean_inc_ref(v___y_3136_);
lean_inc(v___y_3135_);
lean_inc_ref(v___y_3134_);
lean_inc_ref(v___y_3132_);
v___x_3160_ = l_Lean_Elab_Term_mkInstMVar(v___x_3159_, v___x_3138_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_object* v_a_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v_a_3161_ = lean_ctor_get(v___x_3160_, 0);
lean_inc(v_a_3161_);
lean_dec_ref(v___x_3160_);
v___x_3162_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__3));
v___x_3163_ = l_Lean_mkConst(v___x_3162_, v___x_3157_);
lean_inc(v_snd_3147_);
v___x_3164_ = l_Lean_mkApp7(v___x_3163_, v_m_3141_, v___y_3122_, v___y_3128_, v_a_3161_, v_snd_3147_, v___y_3121_, v_fst_3146_);
v___y_3045_ = v___y_3104_;
v___y_3046_ = v___y_3105_;
v___y_3047_ = v___y_3106_;
v___y_3048_ = v___y_3107_;
v___y_3049_ = v_snd_3147_;
v___y_3050_ = v___y_3108_;
v___y_3051_ = v___y_3109_;
v___y_3052_ = v___y_3110_;
v___y_3053_ = v_u_3142_;
v___y_3054_ = v___y_3111_;
v___y_3055_ = v___y_3112_;
v___y_3056_ = v_v_3143_;
v___y_3057_ = v___y_3113_;
v___y_3058_ = v___y_3114_;
v___y_3059_ = v___y_3115_;
v___y_3060_ = v___y_3117_;
v___y_3061_ = v___x_3138_;
v___y_3062_ = v___y_3116_;
v___y_3063_ = v___y_3118_;
v___y_3064_ = v___y_3123_;
v___y_3065_ = v___y_3124_;
v___y_3066_ = v___y_3130_;
v___y_3067_ = v___y_3129_;
v_fst_3068_ = v___x_3164_;
v_snd_3069_ = v___x_3138_;
v___y_3070_ = v___y_3131_;
v___y_3071_ = v___y_3132_;
v___y_3072_ = v___y_3133_;
v___y_3073_ = v___y_3134_;
v___y_3074_ = v___y_3135_;
v___y_3075_ = v___y_3136_;
v___y_3076_ = v___y_3137_;
goto v___jp_3044_;
}
else
{
lean_dec_ref(v___x_3157_);
lean_dec(v_snd_3147_);
lean_dec(v_fst_3146_);
lean_dec(v_v_3143_);
lean_dec(v_u_3142_);
lean_dec_ref(v_m_3141_);
lean_dec(v___y_3137_);
lean_dec_ref(v___y_3136_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec_ref(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec_ref(v___y_3121_);
lean_dec(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec_ref(v___y_3105_);
lean_dec(v___y_3104_);
lean_dec_ref(v_dec_2990_);
return v___x_3160_;
}
}
}
}
else
{
lean_object* v_fst_3167_; lean_object* v_snd_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3203_; 
v_fst_3167_ = lean_ctor_get(v_a_3145_, 0);
v_snd_3168_ = lean_ctor_get(v_a_3145_, 1);
v_isSharedCheck_3203_ = !lean_is_exclusive(v_a_3145_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3170_ = v_a_3145_;
v_isShared_3171_ = v_isSharedCheck_3203_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_snd_3168_);
lean_inc(v_fst_3167_);
lean_dec(v_a_3145_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3203_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3175_; 
v___x_3172_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__4));
v___x_3173_ = lean_box(0);
lean_inc(v___y_3127_);
if (v_isShared_3171_ == 0)
{
lean_ctor_set_tag(v___x_3170_, 1);
lean_ctor_set(v___x_3170_, 1, v___x_3173_);
lean_ctor_set(v___x_3170_, 0, v___y_3127_);
v___x_3175_ = v___x_3170_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___y_3127_);
lean_ctor_set(v_reuseFailAlloc_3202_, 1, v___x_3173_);
v___x_3175_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
lean_inc(v___y_3119_);
v___x_3176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3176_, 0, v___y_3119_);
lean_ctor_set(v___x_3176_, 1, v___x_3175_);
v___x_3177_ = l_Lean_mkConst(v___x_3172_, v___x_3176_);
lean_inc_ref(v___y_3122_);
lean_inc_ref(v___y_3128_);
v___x_3178_ = l_Lean_mkAppB(v___x_3177_, v___y_3128_, v___y_3122_);
v___x_3179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3178_);
v___x_3180_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__6));
lean_inc_ref(v___y_3134_);
v___x_3181_ = l_Lean_Meta_mkFreshExprMVar(v___x_3179_, v___y_3125_, v___x_3180_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_object* v_a_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v_a_3182_ = lean_ctor_get(v___x_3181_, 0);
lean_inc(v_a_3182_);
lean_dec_ref(v___x_3181_);
v___x_3183_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__8));
lean_inc(v_v_3143_);
v___x_3184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3184_, 0, v_v_3143_);
lean_ctor_set(v___x_3184_, 1, v___x_3173_);
lean_inc(v_u_3142_);
v___x_3185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3185_, 0, v_u_3142_);
lean_ctor_set(v___x_3185_, 1, v___x_3184_);
v___x_3186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3186_, 0, v___y_3119_);
lean_ctor_set(v___x_3186_, 1, v___x_3185_);
v___x_3187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3187_, 0, v___y_3127_);
lean_ctor_set(v___x_3187_, 1, v___x_3186_);
lean_inc_ref(v___x_3187_);
v___x_3188_ = l_Lean_mkConst(v___x_3183_, v___x_3187_);
lean_inc(v_a_3182_);
lean_inc_ref(v___y_3128_);
lean_inc_ref(v___y_3122_);
lean_inc_ref(v_m_3141_);
v___x_3189_ = l_Lean_mkApp4(v___x_3188_, v_m_3141_, v___y_3122_, v___y_3128_, v_a_3182_);
lean_inc(v___y_3137_);
lean_inc_ref(v___y_3136_);
lean_inc(v___y_3135_);
lean_inc_ref(v___y_3134_);
lean_inc_ref(v___y_3132_);
v___x_3190_ = l_Lean_Elab_Term_mkInstMVar(v___x_3189_, v___x_3138_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3201_; 
v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3193_ = v___x_3190_;
v_isShared_3194_ = v_isSharedCheck_3201_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_3190_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3201_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3199_; 
v___x_3195_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__10));
v___x_3196_ = l_Lean_mkConst(v___x_3195_, v___x_3187_);
lean_inc(v_snd_3168_);
lean_inc(v_a_3182_);
v___x_3197_ = l_Lean_mkApp8(v___x_3196_, v_m_3141_, v___y_3122_, v___y_3128_, v_a_3182_, v_a_3191_, v_snd_3168_, v___y_3121_, v_fst_3167_);
if (v_isShared_3194_ == 0)
{
lean_ctor_set_tag(v___x_3193_, 1);
lean_ctor_set(v___x_3193_, 0, v_a_3182_);
v___x_3199_ = v___x_3193_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_a_3182_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
v___y_3045_ = v___y_3104_;
v___y_3046_ = v___y_3105_;
v___y_3047_ = v___y_3106_;
v___y_3048_ = v___y_3107_;
v___y_3049_ = v_snd_3168_;
v___y_3050_ = v___y_3108_;
v___y_3051_ = v___y_3109_;
v___y_3052_ = v___y_3110_;
v___y_3053_ = v_u_3142_;
v___y_3054_ = v___y_3111_;
v___y_3055_ = v___y_3112_;
v___y_3056_ = v_v_3143_;
v___y_3057_ = v___y_3113_;
v___y_3058_ = v___y_3114_;
v___y_3059_ = v___y_3115_;
v___y_3060_ = v___y_3117_;
v___y_3061_ = v___x_3138_;
v___y_3062_ = v___y_3116_;
v___y_3063_ = v___y_3118_;
v___y_3064_ = v___y_3123_;
v___y_3065_ = v___y_3124_;
v___y_3066_ = v___y_3130_;
v___y_3067_ = v___y_3129_;
v_fst_3068_ = v___x_3197_;
v_snd_3069_ = v___x_3199_;
v___y_3070_ = v___y_3131_;
v___y_3071_ = v___y_3132_;
v___y_3072_ = v___y_3133_;
v___y_3073_ = v___y_3134_;
v___y_3074_ = v___y_3135_;
v___y_3075_ = v___y_3136_;
v___y_3076_ = v___y_3137_;
goto v___jp_3044_;
}
}
}
else
{
lean_dec_ref(v___x_3187_);
lean_dec(v_a_3182_);
lean_dec(v_snd_3168_);
lean_dec(v_fst_3167_);
lean_dec_ref(v___y_3124_);
lean_dec(v_v_3143_);
lean_dec(v_u_3142_);
lean_dec_ref(v_m_3141_);
lean_dec(v___y_3137_);
lean_dec_ref(v___y_3136_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec_ref(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec_ref(v___y_3121_);
lean_dec(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec_ref(v___y_3105_);
lean_dec(v___y_3104_);
lean_dec_ref(v_dec_2990_);
return v___x_3190_;
}
}
else
{
lean_dec(v_snd_3168_);
lean_dec_ref(v___y_3124_);
lean_dec(v_fst_3167_);
lean_dec(v_v_3143_);
lean_dec(v_u_3142_);
lean_dec_ref(v_m_3141_);
lean_dec(v___y_3137_);
lean_dec_ref(v___y_3136_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec_ref(v___y_3121_);
lean_dec(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec_ref(v___y_3105_);
lean_dec(v___y_3104_);
lean_dec_ref(v_dec_2990_);
return v___x_3181_;
}
}
}
}
}
else
{
lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3211_; 
lean_dec(v_v_3143_);
lean_dec(v_u_3142_);
lean_dec_ref(v_m_3141_);
lean_dec(v___y_3137_);
lean_dec_ref(v___y_3136_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec(v___y_3127_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec_ref(v___y_3121_);
lean_dec(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec_ref(v___y_3105_);
lean_dec(v___y_3104_);
lean_dec_ref(v_dec_2990_);
v_a_3204_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3206_ = v___x_3144_;
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_3144_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3209_; 
if (v_isShared_3207_ == 0)
{
v___x_3209_ = v___x_3206_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_a_3204_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
}
}
else
{
lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3219_; 
lean_dec(v___y_3137_);
lean_dec_ref(v___y_3136_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec(v___y_3127_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec_ref(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec_ref(v___y_3105_);
lean_dec(v___y_3104_);
lean_dec_ref(v_dec_2990_);
v_a_3212_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3214_ = v___x_3139_;
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_3139_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3217_; 
if (v_isShared_3215_ == 0)
{
v___x_3217_ = v___x_3214_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_a_3212_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
return v___x_3217_;
}
}
}
}
v___jp_3220_:
{
lean_object* v___x_3252_; 
v___x_3252_ = l_Lean_Elab_Do_mkPUnit___redArg(v___y_3247_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v_a_3253_; lean_object* v_resultName_3254_; lean_object* v_resultType_3255_; lean_object* v___x_3256_; 
v_a_3253_ = lean_ctor_get(v___x_3252_, 0);
lean_inc(v_a_3253_);
lean_dec_ref(v___x_3252_);
v_resultName_3254_ = lean_ctor_get(v_dec_2990_, 0);
v_resultType_3255_ = lean_ctor_get(v_dec_2990_, 1);
lean_inc(v___y_3240_);
lean_inc_ref(v___y_3242_);
lean_inc(v___y_3235_);
lean_inc_ref(v___y_3244_);
lean_inc_ref(v_resultType_3255_);
v___x_3256_ = l_Lean_Meta_isExprDefEq(v_resultType_3255_, v_a_3253_, v___y_3244_, v___y_3235_, v___y_3242_, v___y_3240_);
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v_a_3257_; uint8_t v___x_3258_; 
v_a_3257_ = lean_ctor_get(v___x_3256_, 0);
lean_inc(v_a_3257_);
lean_dec_ref(v___x_3256_);
v___x_3258_ = lean_unbox(v_a_3257_);
lean_dec(v_a_3257_);
if (v___x_3258_ == 0)
{
lean_object* v___x_3259_; 
v___x_3259_ = l_Lean_Elab_Do_mkPUnit___redArg(v___y_3247_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v_a_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
lean_inc(v_a_3260_);
lean_dec_ref(v___x_3259_);
v___x_3261_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___closed__12, &l_Lean_Elab_Do_elabDoFor___closed__12_once, _init_l_Lean_Elab_Do_elabDoFor___closed__12);
v___x_3262_ = l_Lean_MessageData_ofExpr(v_a_3260_);
v___x_3263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3263_, 0, v___x_3261_);
lean_ctor_set(v___x_3263_, 1, v___x_3262_);
v___x_3264_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___closed__14, &l_Lean_Elab_Do_elabDoFor___closed__14_once, _init_l_Lean_Elab_Do_elabDoFor___closed__14);
v___x_3265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3263_);
lean_ctor_set(v___x_3265_, 1, v___x_3264_);
lean_inc_ref(v_resultType_3255_);
v___x_3266_ = l_Lean_MessageData_ofExpr(v_resultType_3255_);
v___x_3267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3265_);
lean_ctor_set(v___x_3267_, 1, v___x_3266_);
v___x_3268_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___closed__16, &l_Lean_Elab_Do_elabDoFor___closed__16_once, _init_l_Lean_Elab_Do_elabDoFor___closed__16);
v___x_3269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3267_);
lean_ctor_set(v___x_3269_, 1, v___x_3268_);
lean_inc_ref(v___y_3242_);
v___x_3270_ = l_Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6(v___x_3269_, v___y_3247_, v___y_3246_, v___y_3249_, v___y_3244_, v___y_3235_, v___y_3242_, v___y_3240_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_dec_ref(v___x_3270_);
lean_inc_ref(v___y_3226_);
lean_inc_ref(v_resultType_3255_);
lean_inc(v_resultName_3254_);
v___y_3104_ = v___y_3221_;
v___y_3105_ = v___y_3224_;
v___y_3106_ = v___y_3223_;
v___y_3107_ = v___y_3225_;
v___y_3108_ = v___y_3231_;
v___y_3109_ = v_resultName_3254_;
v___y_3110_ = v___y_3232_;
v___y_3111_ = v_resultType_3255_;
v___y_3112_ = v___y_3222_;
v___y_3113_ = v___y_3251_;
v___y_3114_ = v___y_3226_;
v___y_3115_ = v___y_3227_;
v___y_3116_ = v___y_3229_;
v___y_3117_ = v___y_3228_;
v___y_3118_ = v___y_3230_;
v___y_3119_ = v___y_3233_;
v___y_3120_ = v___y_3243_;
v___y_3121_ = v___y_3234_;
v___y_3122_ = v___y_3236_;
v___y_3123_ = v___y_3237_;
v___y_3124_ = v___y_3238_;
v___y_3125_ = v___y_3245_;
v___y_3126_ = v___y_3226_;
v___y_3127_ = v___y_3248_;
v___y_3128_ = v___y_3239_;
v___y_3129_ = v___y_3250_;
v___y_3130_ = v___y_3241_;
v___y_3131_ = v___y_3247_;
v___y_3132_ = v___y_3246_;
v___y_3133_ = v___y_3249_;
v___y_3134_ = v___y_3244_;
v___y_3135_ = v___y_3235_;
v___y_3136_ = v___y_3242_;
v___y_3137_ = v___y_3240_;
goto v___jp_3103_;
}
else
{
lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3278_; 
lean_dec(v___y_3251_);
lean_dec(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec_ref(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec(v___y_3233_);
lean_dec_ref(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec_ref(v___y_3222_);
lean_dec(v___y_3221_);
lean_dec_ref(v_dec_2990_);
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3273_ = v___x_3270_;
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3270_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3276_; 
if (v_isShared_3274_ == 0)
{
v___x_3276_ = v___x_3273_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_a_3271_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
else
{
lean_dec(v___y_3251_);
lean_dec(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec_ref(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec(v___y_3233_);
lean_dec_ref(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec_ref(v___y_3222_);
lean_dec(v___y_3221_);
lean_dec_ref(v_dec_2990_);
return v___x_3259_;
}
}
else
{
lean_inc_ref(v___y_3226_);
lean_inc_ref(v_resultType_3255_);
lean_inc(v_resultName_3254_);
v___y_3104_ = v___y_3221_;
v___y_3105_ = v___y_3224_;
v___y_3106_ = v___y_3223_;
v___y_3107_ = v___y_3225_;
v___y_3108_ = v___y_3231_;
v___y_3109_ = v_resultName_3254_;
v___y_3110_ = v___y_3232_;
v___y_3111_ = v_resultType_3255_;
v___y_3112_ = v___y_3222_;
v___y_3113_ = v___y_3251_;
v___y_3114_ = v___y_3226_;
v___y_3115_ = v___y_3227_;
v___y_3116_ = v___y_3229_;
v___y_3117_ = v___y_3228_;
v___y_3118_ = v___y_3230_;
v___y_3119_ = v___y_3233_;
v___y_3120_ = v___y_3243_;
v___y_3121_ = v___y_3234_;
v___y_3122_ = v___y_3236_;
v___y_3123_ = v___y_3237_;
v___y_3124_ = v___y_3238_;
v___y_3125_ = v___y_3245_;
v___y_3126_ = v___y_3226_;
v___y_3127_ = v___y_3248_;
v___y_3128_ = v___y_3239_;
v___y_3129_ = v___y_3250_;
v___y_3130_ = v___y_3241_;
v___y_3131_ = v___y_3247_;
v___y_3132_ = v___y_3246_;
v___y_3133_ = v___y_3249_;
v___y_3134_ = v___y_3244_;
v___y_3135_ = v___y_3235_;
v___y_3136_ = v___y_3242_;
v___y_3137_ = v___y_3240_;
goto v___jp_3103_;
}
}
else
{
lean_object* v_a_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3286_; 
lean_dec(v___y_3251_);
lean_dec(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec_ref(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec(v___y_3233_);
lean_dec_ref(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec_ref(v___y_3222_);
lean_dec(v___y_3221_);
lean_dec_ref(v_dec_2990_);
v_a_3279_ = lean_ctor_get(v___x_3256_, 0);
v_isSharedCheck_3286_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3281_ = v___x_3256_;
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_a_3279_);
lean_dec(v___x_3256_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v___x_3284_; 
if (v_isShared_3282_ == 0)
{
v___x_3284_ = v___x_3281_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_a_3279_);
v___x_3284_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
return v___x_3284_;
}
}
}
}
else
{
lean_dec(v___y_3251_);
lean_dec(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec_ref(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec(v___y_3233_);
lean_dec_ref(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec_ref(v___y_3222_);
lean_dec(v___y_3221_);
lean_dec_ref(v_dec_2990_);
return v___x_3252_;
}
}
v___jp_3287_:
{
uint8_t v_returnsEarly_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___f_3322_; 
v_returnsEarly_3319_ = lean_ctor_get_uint8(v___y_3313_, sizeof(void*)*2 + 2);
lean_dec_ref(v___y_3313_);
v___x_3320_ = lean_box(v_returnsEarly_3319_);
v___x_3321_ = lean_box(v___y_3300_);
lean_inc_ref(v___y_3296_);
lean_inc_ref(v___y_3295_);
lean_inc_ref(v___y_3318_);
v___f_3322_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__2___boxed), 14, 6);
lean_closure_set(v___f_3322_, 0, v___y_3318_);
lean_closure_set(v___f_3322_, 1, v___y_3295_);
lean_closure_set(v___f_3322_, 2, v___x_3320_);
lean_closure_set(v___f_3322_, 3, v___x_3006_);
lean_closure_set(v___f_3322_, 4, v___y_3296_);
lean_closure_set(v___f_3322_, 5, v___x_3321_);
if (v_returnsEarly_3319_ == 0)
{
size_t v_sz_3323_; size_t v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
lean_dec(v___y_3315_);
v_sz_3323_ = lean_array_size(v___y_3318_);
v___x_3324_ = ((size_t)0ULL);
lean_inc_ref(v___y_3318_);
v___x_3325_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__7(v_sz_3323_, v___x_3324_, v___y_3318_);
v___x_3326_ = lean_array_to_list(v___x_3325_);
v___y_3221_ = v___y_3288_;
v___y_3222_ = v___y_3296_;
v___y_3223_ = v_returnsEarly_3319_;
v___y_3224_ = v___y_3289_;
v___y_3225_ = v___y_3290_;
v___y_3226_ = v___f_3322_;
v___y_3227_ = v___y_3297_;
v___y_3228_ = v___y_3298_;
v___y_3229_ = v___y_3318_;
v___y_3230_ = v___y_3299_;
v___y_3231_ = v___y_3292_;
v___y_3232_ = v___y_3293_;
v___y_3233_ = v___y_3301_;
v___y_3234_ = v___y_3302_;
v___y_3235_ = v___y_3303_;
v___y_3236_ = v___y_3304_;
v___y_3237_ = v___y_3291_;
v___y_3238_ = v___y_3305_;
v___y_3239_ = v___y_3306_;
v___y_3240_ = v___y_3307_;
v___y_3241_ = v___y_3294_;
v___y_3242_ = v___y_3308_;
v___y_3243_ = v___y_3295_;
v___y_3244_ = v___y_3309_;
v___y_3245_ = v___y_3310_;
v___y_3246_ = v___y_3312_;
v___y_3247_ = v___y_3311_;
v___y_3248_ = v___y_3314_;
v___y_3249_ = v___y_3317_;
v___y_3250_ = v___y_3316_;
v___y_3251_ = v___x_3326_;
goto v___jp_3220_;
}
else
{
size_t v_sz_3327_; size_t v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; 
v_sz_3327_ = lean_array_size(v___y_3318_);
v___x_3328_ = ((size_t)0ULL);
lean_inc_ref(v___y_3318_);
v___x_3329_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__7(v_sz_3327_, v___x_3328_, v___y_3318_);
v___x_3330_ = lean_array_to_list(v___x_3329_);
v___x_3331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3331_, 0, v___y_3315_);
lean_ctor_set(v___x_3331_, 1, v___x_3330_);
v___y_3221_ = v___y_3288_;
v___y_3222_ = v___y_3296_;
v___y_3223_ = v_returnsEarly_3319_;
v___y_3224_ = v___y_3289_;
v___y_3225_ = v___y_3290_;
v___y_3226_ = v___f_3322_;
v___y_3227_ = v___y_3297_;
v___y_3228_ = v___y_3298_;
v___y_3229_ = v___y_3318_;
v___y_3230_ = v___y_3299_;
v___y_3231_ = v___y_3292_;
v___y_3232_ = v___y_3293_;
v___y_3233_ = v___y_3301_;
v___y_3234_ = v___y_3302_;
v___y_3235_ = v___y_3303_;
v___y_3236_ = v___y_3304_;
v___y_3237_ = v___y_3291_;
v___y_3238_ = v___y_3305_;
v___y_3239_ = v___y_3306_;
v___y_3240_ = v___y_3307_;
v___y_3241_ = v___y_3294_;
v___y_3242_ = v___y_3308_;
v___y_3243_ = v___y_3295_;
v___y_3244_ = v___y_3309_;
v___y_3245_ = v___y_3310_;
v___y_3246_ = v___y_3312_;
v___y_3247_ = v___y_3311_;
v___y_3248_ = v___y_3314_;
v___y_3249_ = v___y_3317_;
v___y_3250_ = v___y_3316_;
v___y_3251_ = v___x_3331_;
goto v___jp_3220_;
}
}
v___jp_3332_:
{
lean_object* v_x_3341_; lean_object* v___x_3342_; uint8_t v___x_3343_; 
v_x_3341_ = l_Lean_Syntax_getArg(v___x_3007_, v___x_3002_);
v___x_3342_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__16));
lean_inc(v_x_3341_);
v___x_3343_ = l_Lean_Syntax_isOfKind(v_x_3341_, v___x_3342_);
if (v___x_3343_ == 0)
{
lean_object* v___x_3344_; 
lean_dec(v_x_3341_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v_h_x3f_3333_);
lean_dec(v___x_3007_);
lean_dec_ref(v_dec_2990_);
lean_dec(v_stx_2989_);
v___x_3344_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_3344_;
}
else
{
lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3345_ = lean_mk_empty_array_with_capacity(v___x_3002_);
lean_inc(v_x_3341_);
v___x_3346_ = lean_array_push(v___x_3345_, v_x_3341_);
lean_inc_ref(v___y_3339_);
v___x_3347_ = l_Lean_Elab_Do_checkMutVarsForShadowing(v___x_3346_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
lean_dec_ref(v___x_3346_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v___x_3348_; 
lean_dec_ref(v___x_3347_);
v___x_3348_ = l_Lean_Meta_mkFreshLevelMVar(v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_object* v_a_3349_; lean_object* v___x_3350_; 
v_a_3349_ = lean_ctor_get(v___x_3348_, 0);
lean_inc(v_a_3349_);
lean_dec_ref(v___x_3348_);
v___x_3350_ = l_Lean_Meta_mkFreshLevelMVar(v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_object* v_a_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; uint8_t v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
v_a_3351_ = lean_ctor_get(v___x_3350_, 0);
lean_inc(v_a_3351_);
lean_dec_ref(v___x_3350_);
lean_inc(v_a_3349_);
v___x_3352_ = l_Lean_Level_succ___override(v_a_3349_);
v___x_3353_ = l_Lean_mkSort(v___x_3352_);
v___x_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3353_);
v___x_3355_ = 0;
v___x_3356_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__18));
lean_inc_ref(v___y_3337_);
v___x_3357_ = l_Lean_Meta_mkFreshExprMVar(v___x_3354_, v___x_3355_, v___x_3356_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3430_; 
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3360_ = v___x_3357_;
v_isShared_3361_ = v_isSharedCheck_3430_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3357_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3430_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3365_; 
lean_inc(v_a_3351_);
v___x_3362_ = l_Lean_Level_succ___override(v_a_3351_);
v___x_3363_ = l_Lean_mkSort(v___x_3362_);
if (v_isShared_3361_ == 0)
{
lean_ctor_set_tag(v___x_3360_, 1);
lean_ctor_set(v___x_3360_, 0, v___x_3363_);
v___x_3365_ = v___x_3360_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v___x_3363_);
v___x_3365_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; 
v___x_3366_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__20));
lean_inc_ref(v___y_3337_);
v___x_3367_ = l_Lean_Meta_mkFreshExprMVar(v___x_3365_, v___x_3355_, v___x_3366_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v_a_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3428_; 
v_a_3368_ = lean_ctor_get(v___x_3367_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3370_ = v___x_3367_;
v_isShared_3371_ = v_isSharedCheck_3428_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_a_3368_);
lean_dec(v___x_3367_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3428_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3375_; 
v___x_3372_ = lean_unsigned_to_nat(3u);
v___x_3373_ = l_Lean_Syntax_getArg(v___x_3007_, v___x_3372_);
lean_dec(v___x_3007_);
lean_inc(v_a_3368_);
if (v_isShared_3371_ == 0)
{
lean_ctor_set_tag(v___x_3370_, 1);
v___x_3375_ = v___x_3370_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_a_3368_);
v___x_3375_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; 
v___x_3376_ = lean_box(0);
lean_inc(v___y_3340_);
lean_inc_ref(v___y_3339_);
lean_inc(v___y_3338_);
lean_inc_ref(v___y_3337_);
lean_inc(v___y_3336_);
lean_inc_ref(v___y_3335_);
v___x_3377_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_3373_, v___x_3375_, v___x_3009_, v___x_3009_, v___x_3376_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
if (lean_obj_tag(v___x_3377_) == 0)
{
lean_object* v_a_3378_; lean_object* v_body_3379_; lean_object* v___x_3380_; 
v_a_3378_ = lean_ctor_get(v___x_3377_, 0);
lean_inc(v_a_3378_);
lean_dec_ref(v___x_3377_);
v_body_3379_ = l_Lean_Syntax_getArg(v_stx_2989_, v___x_3372_);
lean_dec(v_stx_2989_);
lean_inc(v___y_3340_);
lean_inc_ref(v___y_3339_);
lean_inc(v___y_3338_);
lean_inc_ref(v___y_3337_);
lean_inc(v___y_3336_);
lean_inc_ref(v___y_3335_);
lean_inc(v_body_3379_);
v___x_3380_ = l_Lean_Elab_Do_inferControlInfoSeq(v_body_3379_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v_a_3381_; lean_object* v___x_3382_; 
v_a_3381_ = lean_ctor_get(v___x_3380_, 0);
lean_inc(v_a_3381_);
lean_dec_ref(v___x_3380_);
v___x_3382_ = l_Lean_Elab_Do_getReturnCont___redArg(v___y_3334_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v_a_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
lean_inc(v_a_3383_);
lean_dec_ref(v___x_3382_);
v___x_3384_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__22));
lean_inc(v___y_3340_);
lean_inc_ref(v___y_3339_);
v___x_3385_ = l_Lean_Core_mkFreshUserName(v___x_3384_, v___y_3339_, v___y_3340_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v_a_3386_; lean_object* v_monadInfo_3387_; lean_object* v_mutVars_3388_; lean_object* v___f_3389_; lean_object* v___f_3390_; lean_object* v___x_3391_; lean_object* v___f_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; uint8_t v___x_3395_; 
v_a_3386_ = lean_ctor_get(v___x_3385_, 0);
lean_inc(v_a_3386_);
lean_dec_ref(v___x_3385_);
v_monadInfo_3387_ = lean_ctor_get(v___y_3334_, 0);
lean_inc_ref(v_monadInfo_3387_);
v_mutVars_3388_ = lean_ctor_get(v___y_3334_, 1);
lean_inc(v_a_3358_);
v___f_3389_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__0___boxed), 10, 1);
lean_closure_set(v___f_3389_, 0, v_a_3358_);
lean_inc_ref(v___f_3389_);
lean_inc(v_x_3341_);
v___f_3390_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__1___boxed), 5, 3);
lean_closure_set(v___f_3390_, 0, v_x_3341_);
lean_closure_set(v___f_3390_, 1, v___f_3389_);
lean_closure_set(v___f_3390_, 2, v___x_3002_);
v___x_3391_ = lean_box(v___x_3009_);
lean_inc(v_a_3383_);
v___f_3392_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__3___boxed), 12, 3);
lean_closure_set(v___f_3392_, 0, v_a_3383_);
lean_closure_set(v___f_3392_, 1, v___x_3002_);
lean_closure_set(v___f_3392_, 2, v___x_3391_);
v___x_3393_ = lean_array_get_size(v_mutVars_3388_);
v___x_3394_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_3395_ = lean_nat_dec_lt(v___x_3006_, v___x_3393_);
if (v___x_3395_ == 0)
{
lean_inc(v_a_3386_);
lean_inc(v_a_3351_);
lean_inc(v_a_3358_);
lean_inc(v_a_3368_);
lean_inc(v_a_3378_);
lean_inc(v_a_3349_);
v___y_3288_ = v_a_3349_;
v___y_3289_ = v_a_3378_;
v___y_3290_ = v_a_3368_;
v___y_3291_ = v___f_3390_;
v___y_3292_ = v_a_3358_;
v___y_3293_ = v___f_3392_;
v___y_3294_ = v___f_3389_;
v___y_3295_ = v_monadInfo_3387_;
v___y_3296_ = v_a_3383_;
v___y_3297_ = v_body_3379_;
v___y_3298_ = v_a_3351_;
v___y_3299_ = v_a_3386_;
v___y_3300_ = v___x_3343_;
v___y_3301_ = v_a_3349_;
v___y_3302_ = v_a_3378_;
v___y_3303_ = v___y_3338_;
v___y_3304_ = v_a_3368_;
v___y_3305_ = v_h_x3f_3333_;
v___y_3306_ = v_a_3358_;
v___y_3307_ = v___y_3340_;
v___y_3308_ = v___y_3339_;
v___y_3309_ = v___y_3337_;
v___y_3310_ = v___x_3355_;
v___y_3311_ = v___y_3334_;
v___y_3312_ = v___y_3335_;
v___y_3313_ = v_a_3381_;
v___y_3314_ = v_a_3351_;
v___y_3315_ = v_a_3386_;
v___y_3316_ = v_x_3341_;
v___y_3317_ = v___y_3336_;
v___y_3318_ = v___x_3394_;
goto v___jp_3287_;
}
else
{
uint8_t v___x_3396_; 
v___x_3396_ = lean_nat_dec_le(v___x_3393_, v___x_3393_);
if (v___x_3396_ == 0)
{
if (v___x_3395_ == 0)
{
lean_inc(v_a_3386_);
lean_inc(v_a_3351_);
lean_inc(v_a_3358_);
lean_inc(v_a_3368_);
lean_inc(v_a_3378_);
lean_inc(v_a_3349_);
v___y_3288_ = v_a_3349_;
v___y_3289_ = v_a_3378_;
v___y_3290_ = v_a_3368_;
v___y_3291_ = v___f_3390_;
v___y_3292_ = v_a_3358_;
v___y_3293_ = v___f_3392_;
v___y_3294_ = v___f_3389_;
v___y_3295_ = v_monadInfo_3387_;
v___y_3296_ = v_a_3383_;
v___y_3297_ = v_body_3379_;
v___y_3298_ = v_a_3351_;
v___y_3299_ = v_a_3386_;
v___y_3300_ = v___x_3343_;
v___y_3301_ = v_a_3349_;
v___y_3302_ = v_a_3378_;
v___y_3303_ = v___y_3338_;
v___y_3304_ = v_a_3368_;
v___y_3305_ = v_h_x3f_3333_;
v___y_3306_ = v_a_3358_;
v___y_3307_ = v___y_3340_;
v___y_3308_ = v___y_3339_;
v___y_3309_ = v___y_3337_;
v___y_3310_ = v___x_3355_;
v___y_3311_ = v___y_3334_;
v___y_3312_ = v___y_3335_;
v___y_3313_ = v_a_3381_;
v___y_3314_ = v_a_3351_;
v___y_3315_ = v_a_3386_;
v___y_3316_ = v_x_3341_;
v___y_3317_ = v___y_3336_;
v___y_3318_ = v___x_3394_;
goto v___jp_3287_;
}
else
{
size_t v___x_3397_; size_t v___x_3398_; lean_object* v___x_3399_; 
v___x_3397_ = ((size_t)0ULL);
v___x_3398_ = lean_usize_of_nat(v___x_3393_);
v___x_3399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__8(v_a_3381_, v_mutVars_3388_, v___x_3397_, v___x_3398_, v___x_3394_);
lean_inc(v_a_3386_);
lean_inc(v_a_3351_);
lean_inc(v_a_3358_);
lean_inc(v_a_3368_);
lean_inc(v_a_3378_);
lean_inc(v_a_3349_);
v___y_3288_ = v_a_3349_;
v___y_3289_ = v_a_3378_;
v___y_3290_ = v_a_3368_;
v___y_3291_ = v___f_3390_;
v___y_3292_ = v_a_3358_;
v___y_3293_ = v___f_3392_;
v___y_3294_ = v___f_3389_;
v___y_3295_ = v_monadInfo_3387_;
v___y_3296_ = v_a_3383_;
v___y_3297_ = v_body_3379_;
v___y_3298_ = v_a_3351_;
v___y_3299_ = v_a_3386_;
v___y_3300_ = v___x_3343_;
v___y_3301_ = v_a_3349_;
v___y_3302_ = v_a_3378_;
v___y_3303_ = v___y_3338_;
v___y_3304_ = v_a_3368_;
v___y_3305_ = v_h_x3f_3333_;
v___y_3306_ = v_a_3358_;
v___y_3307_ = v___y_3340_;
v___y_3308_ = v___y_3339_;
v___y_3309_ = v___y_3337_;
v___y_3310_ = v___x_3355_;
v___y_3311_ = v___y_3334_;
v___y_3312_ = v___y_3335_;
v___y_3313_ = v_a_3381_;
v___y_3314_ = v_a_3351_;
v___y_3315_ = v_a_3386_;
v___y_3316_ = v_x_3341_;
v___y_3317_ = v___y_3336_;
v___y_3318_ = v___x_3399_;
goto v___jp_3287_;
}
}
else
{
size_t v___x_3400_; size_t v___x_3401_; lean_object* v___x_3402_; 
v___x_3400_ = ((size_t)0ULL);
v___x_3401_ = lean_usize_of_nat(v___x_3393_);
v___x_3402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__8(v_a_3381_, v_mutVars_3388_, v___x_3400_, v___x_3401_, v___x_3394_);
lean_inc(v_a_3386_);
lean_inc(v_a_3351_);
lean_inc(v_a_3358_);
lean_inc(v_a_3368_);
lean_inc(v_a_3378_);
lean_inc(v_a_3349_);
v___y_3288_ = v_a_3349_;
v___y_3289_ = v_a_3378_;
v___y_3290_ = v_a_3368_;
v___y_3291_ = v___f_3390_;
v___y_3292_ = v_a_3358_;
v___y_3293_ = v___f_3392_;
v___y_3294_ = v___f_3389_;
v___y_3295_ = v_monadInfo_3387_;
v___y_3296_ = v_a_3383_;
v___y_3297_ = v_body_3379_;
v___y_3298_ = v_a_3351_;
v___y_3299_ = v_a_3386_;
v___y_3300_ = v___x_3343_;
v___y_3301_ = v_a_3349_;
v___y_3302_ = v_a_3378_;
v___y_3303_ = v___y_3338_;
v___y_3304_ = v_a_3368_;
v___y_3305_ = v_h_x3f_3333_;
v___y_3306_ = v_a_3358_;
v___y_3307_ = v___y_3340_;
v___y_3308_ = v___y_3339_;
v___y_3309_ = v___y_3337_;
v___y_3310_ = v___x_3355_;
v___y_3311_ = v___y_3334_;
v___y_3312_ = v___y_3335_;
v___y_3313_ = v_a_3381_;
v___y_3314_ = v_a_3351_;
v___y_3315_ = v_a_3386_;
v___y_3316_ = v_x_3341_;
v___y_3317_ = v___y_3336_;
v___y_3318_ = v___x_3402_;
goto v___jp_3287_;
}
}
}
else
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
lean_dec(v_a_3383_);
lean_dec(v_a_3381_);
lean_dec(v_body_3379_);
lean_dec(v_a_3378_);
lean_dec(v_a_3368_);
lean_dec(v_a_3358_);
lean_dec(v_a_3351_);
lean_dec(v_a_3349_);
lean_dec(v_x_3341_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v_h_x3f_3333_);
lean_dec_ref(v_dec_2990_);
v_a_3403_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v___x_3385_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3385_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3408_; 
if (v_isShared_3406_ == 0)
{
v___x_3408_ = v___x_3405_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_a_3403_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
}
else
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
lean_dec(v_a_3381_);
lean_dec(v_body_3379_);
lean_dec(v_a_3378_);
lean_dec(v_a_3368_);
lean_dec(v_a_3358_);
lean_dec(v_a_3351_);
lean_dec(v_a_3349_);
lean_dec(v_x_3341_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v_h_x3f_3333_);
lean_dec_ref(v_dec_2990_);
v_a_3411_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3382_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3382_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3416_; 
if (v_isShared_3414_ == 0)
{
v___x_3416_ = v___x_3413_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3411_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
}
else
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3426_; 
lean_dec(v_body_3379_);
lean_dec(v_a_3378_);
lean_dec(v_a_3368_);
lean_dec(v_a_3358_);
lean_dec(v_a_3351_);
lean_dec(v_a_3349_);
lean_dec(v_x_3341_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v_h_x3f_3333_);
lean_dec_ref(v_dec_2990_);
v_a_3419_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3421_ = v___x_3380_;
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3380_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3424_; 
if (v_isShared_3422_ == 0)
{
v___x_3424_ = v___x_3421_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_a_3419_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
}
else
{
lean_dec(v_a_3368_);
lean_dec(v_a_3358_);
lean_dec(v_a_3351_);
lean_dec(v_a_3349_);
lean_dec(v_x_3341_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v_h_x3f_3333_);
lean_dec_ref(v_dec_2990_);
lean_dec(v_stx_2989_);
return v___x_3377_;
}
}
}
}
else
{
lean_dec(v_a_3358_);
lean_dec(v_a_3351_);
lean_dec(v_a_3349_);
lean_dec(v_x_3341_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v_h_x3f_3333_);
lean_dec(v___x_3007_);
lean_dec_ref(v_dec_2990_);
lean_dec(v_stx_2989_);
return v___x_3367_;
}
}
}
}
else
{
lean_dec(v_a_3351_);
lean_dec(v_a_3349_);
lean_dec(v_x_3341_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v_h_x3f_3333_);
lean_dec(v___x_3007_);
lean_dec_ref(v_dec_2990_);
lean_dec(v_stx_2989_);
return v___x_3357_;
}
}
else
{
lean_object* v_a_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3438_; 
lean_dec(v_a_3349_);
lean_dec(v_x_3341_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v_h_x3f_3333_);
lean_dec(v___x_3007_);
lean_dec_ref(v_dec_2990_);
lean_dec(v_stx_2989_);
v_a_3431_ = lean_ctor_get(v___x_3350_, 0);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3350_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3433_ = v___x_3350_;
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_a_3431_);
lean_dec(v___x_3350_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3436_; 
if (v_isShared_3434_ == 0)
{
v___x_3436_ = v___x_3433_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_a_3431_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
}
}
else
{
lean_object* v_a_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3446_; 
lean_dec(v_x_3341_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v_h_x3f_3333_);
lean_dec(v___x_3007_);
lean_dec_ref(v_dec_2990_);
lean_dec(v_stx_2989_);
v_a_3439_ = lean_ctor_get(v___x_3348_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3348_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3441_ = v___x_3348_;
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_a_3439_);
lean_dec(v___x_3348_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3444_; 
if (v_isShared_3442_ == 0)
{
v___x_3444_ = v___x_3441_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_a_3439_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
}
}
else
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
lean_dec(v_x_3341_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v_h_x3f_3333_);
lean_dec(v___x_3007_);
lean_dec_ref(v_dec_2990_);
lean_dec(v_stx_2989_);
v_a_3447_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3449_ = v___x_3347_;
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3347_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3452_; 
if (v_isShared_3450_ == 0)
{
v___x_3452_ = v___x_3449_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3447_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___boxed(lean_object* v_stx_3464_, lean_object* v_dec_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_){
_start:
{
lean_object* v_res_3474_; 
v_res_3474_ = l_Lean_Elab_Do_elabDoFor(v_stx_3464_, v_dec_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_);
return v_res_3474_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2(lean_object* v_00_u03b1_3475_, lean_object* v_msg_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_){
_start:
{
lean_object* v___x_3484_; 
v___x_3484_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v_msg_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
return v___x_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___boxed(lean_object* v_00_u03b1_3485_, lean_object* v_msg_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_){
_start:
{
lean_object* v_res_3494_; 
v_res_3494_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2(v_00_u03b1_3485_, v_msg_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec(v___y_3488_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(lean_object* v_00_u03b1_3495_, lean_object* v_inst_3496_, lean_object* v_declInfos_3497_, lean_object* v_k_3498_, uint8_t v_kind_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_){
_start:
{
lean_object* v___x_3508_; 
v___x_3508_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4___redArg(v_inst_3496_, v_declInfos_3497_, v_k_3498_, v_kind_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
return v___x_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4___boxed(lean_object* v_00_u03b1_3509_, lean_object* v_inst_3510_, lean_object* v_declInfos_3511_, lean_object* v_k_3512_, lean_object* v_kind_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_){
_start:
{
uint8_t v_kind_boxed_3522_; lean_object* v_res_3523_; 
v_kind_boxed_3522_ = lean_unbox(v_kind_3513_);
v_res_3523_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(v_00_u03b1_3509_, v_inst_3510_, v_declInfos_3511_, v_k_3512_, v_kind_boxed_3522_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_);
lean_dec(v_inst_3510_);
return v_res_3523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5(lean_object* v_00_u03b1_3524_, lean_object* v_name_3525_, lean_object* v_type_3526_, lean_object* v_k_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_){
_start:
{
lean_object* v___x_3536_; 
v___x_3536_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(v_name_3525_, v_type_3526_, v_k_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_);
return v___x_3536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___boxed(lean_object* v_00_u03b1_3537_, lean_object* v_name_3538_, lean_object* v_type_3539_, lean_object* v_k_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_){
_start:
{
lean_object* v_res_3549_; 
v_res_3549_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5(v_00_u03b1_3537_, v_name_3538_, v_type_3539_, v_k_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_);
return v_res_3549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3(lean_object* v_msgData_3550_, lean_object* v_macroStack_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_){
_start:
{
lean_object* v___x_3559_; 
v___x_3559_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(v_msgData_3550_, v_macroStack_3551_, v___y_3556_);
return v___x_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___boxed(lean_object* v_msgData_3560_, lean_object* v_macroStack_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v_res_3569_; 
v_res_3569_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3(v_msgData_3560_, v_macroStack_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_);
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7(lean_object* v_00_u03b1_3570_, lean_object* v_inst_3571_, lean_object* v_declInfos_3572_, lean_object* v_k_3573_, uint8_t v_kind_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_){
_start:
{
lean_object* v___x_3583_; 
v___x_3583_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___redArg(v_inst_3571_, v_declInfos_3572_, v_k_3573_, v_kind_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_);
return v___x_3583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___boxed(lean_object* v_00_u03b1_3584_, lean_object* v_inst_3585_, lean_object* v_declInfos_3586_, lean_object* v_k_3587_, lean_object* v_kind_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_){
_start:
{
uint8_t v_kind_boxed_3597_; lean_object* v_res_3598_; 
v_kind_boxed_3597_ = lean_unbox(v_kind_3588_);
v_res_3598_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7(v_00_u03b1_3584_, v_inst_3585_, v_declInfos_3586_, v_k_3587_, v_kind_boxed_3597_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_);
lean_dec(v_inst_3585_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(lean_object* v_00_u03b1_3599_, lean_object* v_declInfos_3600_, lean_object* v_k_3601_, uint8_t v_kind_3602_, lean_object* v_inst_3603_, lean_object* v_acc_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_){
_start:
{
lean_object* v___x_3613_; 
v___x_3613_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg(v_declInfos_3600_, v_k_3601_, v_kind_3602_, v_acc_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
return v___x_3613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b1_3614_, lean_object* v_declInfos_3615_, lean_object* v_k_3616_, lean_object* v_kind_3617_, lean_object* v_inst_3618_, lean_object* v_acc_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_){
_start:
{
uint8_t v_kind_boxed_3628_; lean_object* v_res_3629_; 
v_kind_boxed_3628_ = lean_unbox(v_kind_3617_);
v_res_3629_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(v_00_u03b1_3614_, v_declInfos_3615_, v_k_3616_, v_kind_boxed_3628_, v_inst_3618_, v_acc_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
lean_dec(v_inst_3618_);
return v_res_3629_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14(lean_object* v_ref_3630_, lean_object* v_msgData_3631_, uint8_t v_severity_3632_, uint8_t v_isSilent_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_){
_start:
{
lean_object* v___x_3642_; 
v___x_3642_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg(v_ref_3630_, v_msgData_3631_, v_severity_3632_, v_isSilent_3633_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___boxed(lean_object* v_ref_3643_, lean_object* v_msgData_3644_, lean_object* v_severity_3645_, lean_object* v_isSilent_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_){
_start:
{
uint8_t v_severity_boxed_3655_; uint8_t v_isSilent_boxed_3656_; lean_object* v_res_3657_; 
v_severity_boxed_3655_ = lean_unbox(v_severity_3645_);
v_isSilent_boxed_3656_ = lean_unbox(v_isSilent_3646_);
v_res_3657_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14(v_ref_3643_, v_msgData_3644_, v_severity_boxed_3655_, v_isSilent_boxed_3656_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_);
lean_dec(v___y_3653_);
lean_dec(v___y_3651_);
lean_dec_ref(v___y_3650_);
lean_dec(v___y_3649_);
lean_dec_ref(v___y_3648_);
lean_dec_ref(v___y_3647_);
lean_dec(v_ref_3643_);
return v_res_3657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1(){
_start:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; 
v___x_3665_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_3666_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
v___x_3667_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1));
v___x_3668_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___boxed), 10, 0);
v___x_3669_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3665_, v___x_3666_, v___x_3667_, v___x_3668_);
return v___x_3669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___boxed(lean_object* v_a_3670_){
_start:
{
lean_object* v_res_3671_; 
v_res_3671_ = l_Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1();
return v_res_3671_;
}
}
lean_object* runtime_initialize_Lean_Elab_BuiltinDo_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Do(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_ProdN(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_BuiltinDo_For(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_BuiltinDo_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_ProdN(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Do(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_BuiltinDo_For(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_BuiltinDo_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Do(uint8_t builtin);
lean_object* initialize_Init_Control_Do(uint8_t builtin);
lean_object* initialize_Lean_Meta_ProdN(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_BuiltinDo_For(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_BuiltinDo_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_ProdN(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_BuiltinDo_For(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_BuiltinDo_For(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_BuiltinDo_For(builtin);
}
#ifdef __cplusplus
}
#endif
