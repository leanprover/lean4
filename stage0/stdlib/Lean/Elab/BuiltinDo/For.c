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
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor___boxed(lean_object*, lean_object*, lean_object*);
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
lean_inc_ref(v___y_24_);
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
lean_dec_ref(v___y_39_);
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
lean_dec_ref(v___y_550_);
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
v___y_655_ = v_h_x3f_704_;
v___y_656_ = v___x_708_;
v___y_657_ = v_doElems_709_;
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
v___y_655_ = v_h_x3f_704_;
v___y_656_ = v___x_708_;
v___y_657_ = v_doElems_709_;
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
v___y_655_ = v_h_x3f_704_;
v___y_656_ = v___x_708_;
v___y_657_ = v_doElems_709_;
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
lean_inc_ref(v___y_629_);
v___x_633_ = l_Array_append___redArg(v___y_629_, v___y_632_);
lean_dec_ref(v___y_632_);
lean_inc(v___y_627_);
lean_inc(v___y_631_);
v___x_634_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_634_, 0, v___y_631_);
lean_ctor_set(v___x_634_, 1, v___y_627_);
lean_ctor_set(v___x_634_, 2, v___x_633_);
v___x_635_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
lean_inc(v___y_631_);
v___x_636_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_636_, 0, v___y_631_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
lean_inc(v___y_631_);
v___x_637_ = l_Lean_Syntax_node4(v___y_631_, v___x_620_, v___x_634_, v___y_630_, v___x_636_, v___y_628_);
lean_inc(v___y_627_);
lean_inc(v___y_631_);
v___x_638_ = l_Lean_Syntax_node1(v___y_631_, v___y_627_, v___x_637_);
v___x_639_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75));
lean_inc(v___y_631_);
v___x_640_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_640_, 0, v___y_631_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
lean_inc_ref(v___x_640_);
lean_inc(v___y_631_);
v___x_641_ = l_Lean_Syntax_node4(v___y_631_, v___x_613_, v___y_625_, v___x_638_, v___x_640_, v___y_622_);
lean_inc_ref(v___y_629_);
lean_inc(v___y_627_);
lean_inc(v___y_631_);
v___x_642_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_642_, 0, v___y_631_);
lean_ctor_set(v___x_642_, 1, v___y_627_);
lean_ctor_set(v___x_642_, 2, v___y_629_);
lean_inc(v___y_631_);
v___x_643_ = l_Lean_Syntax_node2(v___y_631_, v___y_623_, v___x_641_, v___x_642_);
v___x_644_ = lean_array_push(v___y_626_, v___x_643_);
v___x_645_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_646_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_647_ = l_Array_append___redArg(v___y_629_, v___x_644_);
lean_dec_ref(v___x_644_);
lean_inc(v___y_631_);
v___x_648_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_648_, 0, v___y_631_);
lean_ctor_set(v___x_648_, 1, v___y_627_);
lean_ctor_set(v___x_648_, 2, v___x_647_);
lean_inc(v___y_631_);
v___x_649_ = l_Lean_Syntax_node1(v___y_631_, v___x_646_, v___x_648_);
v___x_650_ = l_Lean_Syntax_node2(v___y_631_, v___x_645_, v___x_640_, v___x_649_);
v___x_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
lean_ctor_set(v___x_651_, 1, v___y_624_);
return v___x_651_;
}
v___jp_654_:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_662_ = lean_array_get_size(v_decls_653_);
v___x_663_ = l_Array_toSubarray___redArg(v_decls_653_, v___x_617_, v___x_662_);
v___x_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_664_, 0, v___y_657_);
lean_ctor_set(v___x_664_, 1, v_body_659_);
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
v___x_674_ = l_Lean_SourceInfo_fromRef(v_ref_673_, v___x_619_);
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
if (lean_obj_tag(v___y_655_) == 1)
{
lean_object* v_val_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v_val_681_ = lean_ctor_get(v___y_655_, 0);
lean_inc(v_val_681_);
lean_dec_ref(v___y_655_);
v___x_682_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
lean_inc(v___x_674_);
v___x_683_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_674_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v___x_684_ = l_Array_mkArray2___redArg(v_val_681_, v___x_683_);
v___y_622_ = v_snd_669_;
v___y_623_ = v___x_675_;
v___y_624_ = v_a_667_;
v___y_625_ = v___x_678_;
v___y_626_ = v_fst_668_;
v___y_627_ = v___x_679_;
v___y_628_ = v___y_656_;
v___y_629_ = v___x_680_;
v___y_630_ = v_x_658_;
v___y_631_ = v___x_674_;
v___y_632_ = v___x_684_;
goto v___jp_621_;
}
else
{
lean_object* v___x_685_; 
lean_dec(v___y_655_);
v___x_685_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
v___y_622_ = v_snd_669_;
v___y_623_ = v___x_675_;
v___y_624_ = v_a_667_;
v___y_625_ = v___x_678_;
v___y_626_ = v_fst_668_;
v___y_627_ = v___x_679_;
v___y_628_ = v___y_656_;
v___y_629_ = v___x_680_;
v___y_630_ = v_x_658_;
v___y_631_ = v___x_674_;
v___y_632_ = v___x_685_;
goto v___jp_621_;
}
}
}
}
else
{
lean_object* v_a_688_; lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec(v_x_658_);
lean_dec(v___y_656_);
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
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___y_778_; lean_object* v___y_779_; lean_object* v___y_780_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; uint8_t v___y_844_; lean_object* v_x_845_; lean_object* v_body_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; uint8_t v___y_889_; lean_object* v_h_x3f_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; uint8_t v___x_1007_; 
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
v___y_1011_ = v_h_x3f_1060_;
v___y_1012_ = v___x_1064_;
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
v___y_1011_ = v_h_x3f_1060_;
v___y_1012_ = v___x_1064_;
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
v___y_1011_ = v_h_x3f_1060_;
v___y_1012_ = v___x_1064_;
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
v___x_1030_ = l_Lean_SourceInfo_fromRef(v_ref_1029_, v___x_1007_);
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
if (lean_obj_tag(v___y_1011_) == 1)
{
lean_object* v_val_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v_val_1037_ = lean_ctor_get(v___y_1011_, 0);
lean_inc(v_val_1037_);
lean_dec_ref(v___y_1011_);
v___x_1038_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
lean_inc(v___x_1030_);
v___x_1039_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1030_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = l_Array_mkArray2___redArg(v_val_1037_, v___x_1039_);
v___y_977_ = v___x_1035_;
v___y_978_ = v___y_1012_;
v___y_979_ = v___x_1034_;
v___y_980_ = v_x_1014_;
v___y_981_ = v___x_1036_;
v___y_982_ = v_a_1023_;
v___y_983_ = v_fst_1024_;
v___y_984_ = v___x_1031_;
v___y_985_ = v___x_1030_;
v___y_986_ = v_snd_1025_;
v___y_987_ = v___x_1040_;
goto v___jp_976_;
}
else
{
lean_object* v___x_1041_; 
lean_dec(v___y_1011_);
v___x_1041_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
v___y_977_ = v___x_1035_;
v___y_978_ = v___y_1012_;
v___y_979_ = v___x_1034_;
v___y_980_ = v_x_1014_;
v___y_981_ = v___x_1036_;
v___y_982_ = v_a_1023_;
v___y_983_ = v_fst_1024_;
v___y_984_ = v___x_1031_;
v___y_985_ = v___x_1030_;
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
v___y_1138_ = v___x_1191_;
v___y_1139_ = v_h_x3f_1187_;
v___y_1140_ = v_doElems_1192_;
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
v___y_1138_ = v___x_1191_;
v___y_1139_ = v_h_x3f_1187_;
v___y_1140_ = v_doElems_1192_;
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
v___y_1138_ = v___x_1191_;
v___y_1139_ = v_h_x3f_1187_;
v___y_1140_ = v_doElems_1192_;
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
lean_ctor_set(v___x_1147_, 0, v___y_1140_);
lean_ctor_set(v___x_1147_, 1, v_body_1142_);
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
v___x_1157_ = l_Lean_SourceInfo_fromRef(v_ref_1156_, v___x_1134_);
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
if (lean_obj_tag(v___y_1139_) == 1)
{
lean_object* v_val_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v_val_1164_ = lean_ctor_get(v___y_1139_, 0);
lean_inc(v_val_1164_);
lean_dec_ref(v___y_1139_);
v___x_1165_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
lean_inc(v___x_1157_);
v___x_1166_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1157_);
lean_ctor_set(v___x_1166_, 1, v___x_1165_);
v___x_1167_ = l_Array_mkArray2___redArg(v_val_1164_, v___x_1166_);
v___y_778_ = v___x_1158_;
v___y_779_ = v___y_1138_;
v___y_780_ = v___x_1161_;
v___y_781_ = v_snd_1152_;
v___y_782_ = v_a_1150_;
v___y_783_ = v___x_1162_;
v___y_784_ = v___x_1157_;
v___y_785_ = v_x_1141_;
v___y_786_ = v_fst_1151_;
v___y_787_ = v___x_1163_;
v___y_788_ = v___x_1167_;
goto v___jp_777_;
}
else
{
lean_object* v___x_1168_; 
lean_dec(v___y_1139_);
v___x_1168_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
v___y_778_ = v___x_1158_;
v___y_779_ = v___y_1138_;
v___y_780_ = v___x_1161_;
v___y_781_ = v_snd_1152_;
v___y_782_ = v_a_1150_;
v___y_783_ = v___x_1162_;
v___y_784_ = v___x_1157_;
v___y_785_ = v_x_1141_;
v___y_786_ = v_fst_1151_;
v___y_787_ = v___x_1163_;
v___y_788_ = v___x_1168_;
goto v___jp_777_;
}
}
}
}
else
{
lean_object* v_a_1171_; lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
lean_dec(v_x_1141_);
lean_dec(v___y_1139_);
lean_dec(v___y_1138_);
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
lean_inc_ref(v___y_787_);
v___x_789_ = l_Array_append___redArg(v___y_787_, v___y_788_);
lean_dec_ref(v___y_788_);
lean_inc(v___y_783_);
lean_inc(v___y_784_);
v___x_790_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_790_, 0, v___y_784_);
lean_ctor_set(v___x_790_, 1, v___y_783_);
lean_ctor_set(v___x_790_, 2, v___x_789_);
v___x_791_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
lean_inc(v___y_784_);
v___x_792_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_792_, 0, v___y_784_);
lean_ctor_set(v___x_792_, 1, v___x_791_);
lean_inc(v___y_784_);
v___x_793_ = l_Lean_Syntax_node4(v___y_784_, v___x_776_, v___x_790_, v___y_785_, v___x_792_, v___y_779_);
lean_inc(v___y_783_);
lean_inc(v___y_784_);
v___x_794_ = l_Lean_Syntax_node1(v___y_784_, v___y_783_, v___x_793_);
v___x_795_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75));
lean_inc(v___y_784_);
v___x_796_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_796_, 0, v___y_784_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
lean_inc_ref(v___x_796_);
lean_inc(v___y_784_);
v___x_797_ = l_Lean_Syntax_node4(v___y_784_, v___x_613_, v___y_780_, v___x_794_, v___x_796_, v___y_781_);
lean_inc_ref(v___y_787_);
lean_inc(v___y_783_);
lean_inc(v___y_784_);
v___x_798_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_798_, 0, v___y_784_);
lean_ctor_set(v___x_798_, 1, v___y_783_);
lean_ctor_set(v___x_798_, 2, v___y_787_);
lean_inc(v___y_784_);
v___x_799_ = l_Lean_Syntax_node2(v___y_784_, v___y_778_, v___x_797_, v___x_798_);
v___x_800_ = lean_array_push(v___y_786_, v___x_799_);
v___x_801_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_802_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_803_ = l_Array_append___redArg(v___y_787_, v___x_800_);
lean_dec_ref(v___x_800_);
lean_inc(v___y_784_);
v___x_804_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_804_, 0, v___y_784_);
lean_ctor_set(v___x_804_, 1, v___y_783_);
lean_ctor_set(v___x_804_, 2, v___x_803_);
lean_inc(v___y_784_);
v___x_805_ = l_Lean_Syntax_node1(v___y_784_, v___x_802_, v___x_804_);
v___x_806_ = l_Lean_Syntax_node2(v___y_784_, v___x_801_, v___x_796_, v___x_805_);
v___x_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
lean_ctor_set(v___x_807_, 1, v___y_782_);
return v___x_807_;
}
v___jp_808_:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
lean_inc_ref(v___y_818_);
v___x_820_ = l_Array_append___redArg(v___y_818_, v___y_819_);
lean_dec_ref(v___y_819_);
lean_inc(v___y_811_);
lean_inc(v___y_815_);
v___x_821_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_821_, 0, v___y_815_);
lean_ctor_set(v___x_821_, 1, v___y_811_);
lean_ctor_set(v___x_821_, 2, v___x_820_);
v___x_822_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
lean_inc(v___y_815_);
v___x_823_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_823_, 0, v___y_815_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
lean_inc(v___y_815_);
v___x_824_ = l_Lean_Syntax_node4(v___y_815_, v___x_776_, v___x_821_, v___y_810_, v___x_823_, v___y_812_);
lean_inc(v___y_811_);
lean_inc(v___y_815_);
v___x_825_ = l_Lean_Syntax_node1(v___y_815_, v___y_811_, v___x_824_);
v___x_826_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75));
lean_inc(v___y_815_);
v___x_827_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_827_, 0, v___y_815_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
lean_inc_ref(v___x_827_);
lean_inc(v___y_815_);
v___x_828_ = l_Lean_Syntax_node4(v___y_815_, v___x_613_, v___y_814_, v___x_825_, v___x_827_, v___y_816_);
lean_inc_ref(v___y_818_);
lean_inc(v___y_811_);
lean_inc(v___y_815_);
v___x_829_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_829_, 0, v___y_815_);
lean_ctor_set(v___x_829_, 1, v___y_811_);
lean_ctor_set(v___x_829_, 2, v___y_818_);
lean_inc(v___y_815_);
v___x_830_ = l_Lean_Syntax_node2(v___y_815_, v___y_817_, v___x_828_, v___x_829_);
v___x_831_ = lean_array_push(v___y_809_, v___x_830_);
v___x_832_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_833_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_834_ = l_Array_append___redArg(v___y_818_, v___x_831_);
lean_dec_ref(v___x_831_);
lean_inc(v___y_815_);
v___x_835_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_835_, 0, v___y_815_);
lean_ctor_set(v___x_835_, 1, v___y_811_);
lean_ctor_set(v___x_835_, 2, v___x_834_);
lean_inc(v___y_815_);
v___x_836_ = l_Lean_Syntax_node1(v___y_815_, v___x_833_, v___x_835_);
v___x_837_ = l_Lean_Syntax_node2(v___y_815_, v___x_832_, v___x_827_, v___x_836_);
v___x_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
lean_ctor_set(v___x_838_, 1, v___y_813_);
return v___x_838_;
}
v___jp_839_:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_849_ = lean_array_get_size(v___y_841_);
v___x_850_ = l_Array_toSubarray___redArg(v___y_841_, v___x_617_, v___x_849_);
v___x_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_851_, 0, v___y_840_);
lean_ctor_set(v___x_851_, 1, v_body_846_);
v___x_852_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___y_844_, v___x_850_, v___x_851_, v___y_847_, v___y_848_);
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
v___x_861_ = l_Lean_SourceInfo_fromRef(v_ref_860_, v___y_844_);
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
if (lean_obj_tag(v___y_842_) == 1)
{
lean_object* v_val_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v_val_868_ = lean_ctor_get(v___y_842_, 0);
lean_inc(v_val_868_);
lean_dec_ref(v___y_842_);
v___x_869_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
lean_inc(v___x_861_);
v___x_870_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_861_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = l_Array_mkArray2___redArg(v_val_868_, v___x_870_);
v___y_809_ = v_fst_855_;
v___y_810_ = v_x_845_;
v___y_811_ = v___x_866_;
v___y_812_ = v___y_843_;
v___y_813_ = v_a_854_;
v___y_814_ = v___x_865_;
v___y_815_ = v___x_861_;
v___y_816_ = v_snd_856_;
v___y_817_ = v___x_862_;
v___y_818_ = v___x_867_;
v___y_819_ = v___x_871_;
goto v___jp_808_;
}
else
{
lean_object* v___x_872_; 
lean_dec(v___y_842_);
v___x_872_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
v___y_809_ = v_fst_855_;
v___y_810_ = v_x_845_;
v___y_811_ = v___x_866_;
v___y_812_ = v___y_843_;
v___y_813_ = v_a_854_;
v___y_814_ = v___x_865_;
v___y_815_ = v___x_861_;
v___y_816_ = v_snd_856_;
v___y_817_ = v___x_862_;
v___y_818_ = v___x_867_;
v___y_819_ = v___x_872_;
goto v___jp_808_;
}
}
}
}
else
{
lean_object* v_a_875_; lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_dec(v_x_845_);
lean_dec(v___y_843_);
lean_dec(v___y_842_);
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
v___x_894_ = l_Lean_Syntax_getArg(v___y_885_, v___y_886_);
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
v___x_899_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_893_, v___y_889_, v___y_891_, v___y_892_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v_a_901_; lean_object* v_ref_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
v_a_901_ = lean_ctor_get(v___x_899_, 1);
lean_inc(v_a_901_);
lean_dec_ref(v___x_899_);
v_ref_902_ = lean_ctor_get(v___y_891_, 5);
v___x_903_ = l_Lean_SourceInfo_fromRef(v_ref_902_, v___y_889_);
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
v___x_925_ = l_Lean_Syntax_node4(v___x_903_, v___x_918_, v___x_920_, v___x_922_, v___x_924_, v___y_888_);
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
v___y_840_ = v_doElems_895_;
v___y_841_ = v___y_887_;
v___y_842_ = v_h_x3f_890_;
v___y_843_ = v___x_894_;
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
lean_dec(v_h_x3f_890_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
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
v___x_941_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_893_, v___y_889_, v___y_891_, v___y_892_);
lean_dec(v___x_893_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; lean_object* v_a_943_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_a_942_);
v_a_943_ = lean_ctor_get(v___x_941_, 1);
lean_inc(v_a_943_);
lean_dec_ref(v___x_941_);
v___y_840_ = v_doElems_895_;
v___y_841_ = v___y_887_;
v___y_842_ = v_h_x3f_890_;
v___y_843_ = v___x_894_;
v___y_844_ = v___y_889_;
v_x_845_ = v_a_942_;
v_body_846_ = v___y_888_;
v___y_847_ = v___y_891_;
v___y_848_ = v_a_943_;
goto v___jp_839_;
}
else
{
lean_object* v_a_944_; lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
lean_dec(v___x_894_);
lean_dec(v_h_x3f_890_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
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
v___y_840_ = v_doElems_895_;
v___y_841_ = v___y_887_;
v___y_842_ = v_h_x3f_890_;
v___y_843_ = v___x_894_;
v___y_844_ = v___y_889_;
v_x_845_ = v___x_893_;
v_body_846_ = v___y_888_;
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
v___y_886_ = v___x_965_;
v___y_887_ = v_decls_960_;
v___y_888_ = v_body_966_;
v___y_889_ = v___x_958_;
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
v___y_886_ = v___x_965_;
v___y_887_ = v_decls_960_;
v___y_888_ = v_body_966_;
v___y_889_ = v___x_958_;
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
lean_dec(v___x_618_);
lean_dec(v_stx_610_);
v___x_975_ = l_Lean_Macro_throwUnsupported___redArg(v___y_955_);
return v___x_975_;
}
}
v___jp_976_:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
lean_inc_ref(v___y_981_);
v___x_988_ = l_Array_append___redArg(v___y_981_, v___y_987_);
lean_dec_ref(v___y_987_);
lean_inc(v___y_977_);
lean_inc(v___y_985_);
v___x_989_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_989_, 0, v___y_985_);
lean_ctor_set(v___x_989_, 1, v___y_977_);
lean_ctor_set(v___x_989_, 2, v___x_988_);
v___x_990_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
lean_inc(v___y_985_);
v___x_991_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_991_, 0, v___y_985_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
lean_inc(v___y_985_);
v___x_992_ = l_Lean_Syntax_node4(v___y_985_, v___x_776_, v___x_989_, v___y_980_, v___x_991_, v___y_978_);
lean_inc(v___y_977_);
lean_inc(v___y_985_);
v___x_993_ = l_Lean_Syntax_node1(v___y_985_, v___y_977_, v___x_992_);
v___x_994_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75));
lean_inc(v___y_985_);
v___x_995_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_995_, 0, v___y_985_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
lean_inc_ref(v___x_995_);
lean_inc(v___y_985_);
v___x_996_ = l_Lean_Syntax_node4(v___y_985_, v___x_613_, v___y_979_, v___x_993_, v___x_995_, v___y_986_);
lean_inc_ref(v___y_981_);
lean_inc(v___y_977_);
lean_inc(v___y_985_);
v___x_997_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_997_, 0, v___y_985_);
lean_ctor_set(v___x_997_, 1, v___y_977_);
lean_ctor_set(v___x_997_, 2, v___y_981_);
lean_inc(v___y_985_);
v___x_998_ = l_Lean_Syntax_node2(v___y_985_, v___y_984_, v___x_996_, v___x_997_);
v___x_999_ = lean_array_push(v___y_983_, v___x_998_);
v___x_1000_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_1001_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_1002_ = l_Array_append___redArg(v___y_981_, v___x_999_);
lean_dec_ref(v___x_999_);
lean_inc(v___y_985_);
v___x_1003_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1003_, 0, v___y_985_);
lean_ctor_set(v___x_1003_, 1, v___y_977_);
lean_ctor_set(v___x_1003_, 2, v___x_1002_);
lean_inc(v___y_985_);
v___x_1004_ = l_Lean_Syntax_node1(v___y_985_, v___x_1001_, v___x_1003_);
v___x_1005_ = l_Lean_Syntax_node2(v___y_985_, v___x_1000_, v___x_995_, v___x_1004_);
v___x_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set(v___x_1006_, 1, v___y_982_);
return v___x_1006_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor___boxed(lean_object* v_stx_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Lean_Elab_Do_expandDoFor(v_stx_1257_, v_a_1258_, v_a_1259_);
lean_dec_ref(v_a_1258_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0(uint8_t v___x_1261_, lean_object* v_inst_1262_, lean_object* v_R_1263_, lean_object* v_a_1264_, lean_object* v_b_1265_, lean_object* v_c_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_1261_, v_a_1264_, v_b_1265_, v___y_1267_, v___y_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___boxed(lean_object* v___x_1270_, lean_object* v_inst_1271_, lean_object* v_R_1272_, lean_object* v_a_1273_, lean_object* v_b_1274_, lean_object* v_c_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
uint8_t v___x_147668__boxed_1278_; lean_object* v_res_1279_; 
v___x_147668__boxed_1278_ = lean_unbox(v___x_1270_);
v_res_1279_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0(v___x_147668__boxed_1278_, v_inst_1271_, v_R_1272_, v_a_1273_, v_b_1274_, v_c_1275_, v___y_1276_, v___y_1277_);
lean_dec_ref(v___y_1276_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1(){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1287_ = l_Lean_Elab_macroAttribute;
v___x_1288_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
v___x_1289_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1));
v___x_1290_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_expandDoFor___boxed), 3, 0);
v___x_1291_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1287_, v___x_1288_, v___x_1289_, v___x_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___boxed(lean_object* v_a_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1();
return v_res_1293_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1294_ = lean_box(0);
v___x_1295_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1295_);
lean_ctor_set(v___x_1296_, 1, v___x_1294_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg(){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0);
v___x_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___boxed(lean_object* v___y_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0(lean_object* v_00_u03b1_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v___x_1311_; 
v___x_1311_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___boxed(lean_object* v_00_u03b1_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0(v_00_u03b1_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec_ref(v___y_1313_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0(lean_object* v_k_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v_b_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v___x_1332_; 
lean_inc(v___y_1330_);
lean_inc_ref(v___y_1329_);
lean_inc(v___y_1328_);
lean_inc_ref(v___y_1327_);
lean_inc(v___y_1325_);
lean_inc_ref(v___y_1324_);
lean_inc_ref(v___y_1323_);
v___x_1332_ = lean_apply_9(v_k_1322_, v_b_1326_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, lean_box(0));
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0___boxed(lean_object* v_k_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v_b_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0(v_k_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v_b_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec_ref(v___y_1334_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(lean_object* v_name_1344_, uint8_t v_bi_1345_, lean_object* v_type_1346_, lean_object* v_k_1347_, uint8_t v_kind_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v___f_1357_; lean_object* v___x_1358_; 
lean_inc(v___y_1351_);
lean_inc_ref(v___y_1350_);
lean_inc_ref(v___y_1349_);
v___f_1357_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1357_, 0, v_k_1347_);
lean_closure_set(v___f_1357_, 1, v___y_1349_);
lean_closure_set(v___f_1357_, 2, v___y_1350_);
lean_closure_set(v___f_1357_, 3, v___y_1351_);
v___x_1358_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1344_, v_bi_1345_, v_type_1346_, v___f_1357_, v_kind_1348_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1358_) == 0)
{
return v___x_1358_;
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___x_1358_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1358_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1359_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___boxed(lean_object* v_name_1367_, lean_object* v_bi_1368_, lean_object* v_type_1369_, lean_object* v_k_1370_, lean_object* v_kind_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
uint8_t v_bi_boxed_1380_; uint8_t v_kind_boxed_1381_; lean_object* v_res_1382_; 
v_bi_boxed_1380_ = lean_unbox(v_bi_1368_);
v_kind_boxed_1381_ = lean_unbox(v_kind_1371_);
v_res_1382_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_name_1367_, v_bi_boxed_1380_, v_type_1369_, v_k_1370_, v_kind_boxed_1381_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
lean_dec(v___y_1378_);
lean_dec_ref(v___y_1377_);
lean_dec(v___y_1376_);
lean_dec_ref(v___y_1375_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec_ref(v___y_1372_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3(lean_object* v_00_u03b1_1383_, lean_object* v_name_1384_, uint8_t v_bi_1385_, lean_object* v_type_1386_, lean_object* v_k_1387_, uint8_t v_kind_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v___x_1397_; 
v___x_1397_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_name_1384_, v_bi_1385_, v_type_1386_, v_k_1387_, v_kind_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___boxed(lean_object* v_00_u03b1_1398_, lean_object* v_name_1399_, lean_object* v_bi_1400_, lean_object* v_type_1401_, lean_object* v_k_1402_, lean_object* v_kind_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
uint8_t v_bi_boxed_1412_; uint8_t v_kind_boxed_1413_; lean_object* v_res_1414_; 
v_bi_boxed_1412_ = lean_unbox(v_bi_1400_);
v_kind_boxed_1413_ = lean_unbox(v_kind_1403_);
v_res_1414_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3(v_00_u03b1_1398_, v_name_1399_, v_bi_boxed_1412_, v_type_1401_, v_k_1402_, v_kind_boxed_1413_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec_ref(v___y_1404_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__0(lean_object* v_a_1415_, lean_object* v_x_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1425_, 0, v_a_1415_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__0___boxed(lean_object* v_a_1426_, lean_object* v_x_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Lean_Elab_Do_elabDoFor___lam__0(v_a_1426_, v_x_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec_ref(v_x_1427_);
return v_res_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__1(lean_object* v_x_1437_, lean_object* v___f_1438_, lean_object* v___x_1439_, lean_object* v_x_1440_, lean_object* v_x_1441_){
_start:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1442_ = l_Lean_TSyntax_getId(v_x_1437_);
v___x_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
lean_ctor_set(v___x_1443_, 1, v___f_1438_);
v___x_1444_ = lean_mk_empty_array_with_capacity(v___x_1439_);
v___x_1445_ = lean_array_push(v___x_1444_, v___x_1443_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__1___boxed(lean_object* v_x_1446_, lean_object* v___f_1447_, lean_object* v___x_1448_, lean_object* v_x_1449_, lean_object* v_x_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_Elab_Do_elabDoFor___lam__1(v_x_1446_, v___f_1447_, v___x_1448_, v_x_1449_, v_x_1450_);
lean_dec(v_x_1450_);
lean_dec(v_x_1449_);
lean_dec(v___x_1448_);
lean_dec(v_x_1446_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__3(lean_object* v_a_1452_, lean_object* v___x_1453_, uint8_t v___x_1454_, lean_object* v_r_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v_k_1464_; lean_object* v___x_1465_; 
v_k_1464_ = lean_ctor_get(v_a_1452_, 1);
lean_inc_ref(v_k_1464_);
lean_dec_ref(v_a_1452_);
lean_inc(v___y_1462_);
lean_inc_ref(v___y_1461_);
lean_inc(v___y_1460_);
lean_inc_ref(v___y_1459_);
lean_inc(v___y_1458_);
lean_inc_ref(v___y_1457_);
lean_inc_ref(v___y_1456_);
lean_inc_ref(v_r_1455_);
v___x_1465_ = lean_apply_9(v_k_1464_, v_r_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, lean_box(0));
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; uint8_t v___x_1470_; lean_object* v___x_1471_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
lean_inc(v_a_1466_);
lean_dec_ref(v___x_1465_);
v___x_1467_ = lean_mk_empty_array_with_capacity(v___x_1453_);
v___x_1468_ = lean_array_push(v___x_1467_, v_r_1455_);
v___x_1469_ = 0;
v___x_1470_ = 1;
v___x_1471_ = l_Lean_Meta_mkLambdaFVars(v___x_1468_, v_a_1466_, v___x_1469_, v___x_1454_, v___x_1469_, v___x_1454_, v___x_1470_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
lean_dec_ref(v___x_1468_);
return v___x_1471_;
}
else
{
lean_dec_ref(v_r_1455_);
return v___x_1465_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___boxed(lean_object* v_a_1472_, lean_object* v___x_1473_, lean_object* v___x_1474_, lean_object* v_r_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
uint8_t v___x_77870__boxed_1484_; lean_object* v_res_1485_; 
v___x_77870__boxed_1484_ = lean_unbox(v___x_1474_);
v_res_1485_ = l_Lean_Elab_Do_elabDoFor___lam__3(v_a_1472_, v___x_1473_, v___x_77870__boxed_1484_, v_r_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___x_1473_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1(lean_object* v___x_1486_, lean_object* v_as_1487_, size_t v_sz_1488_, size_t v_i_1489_, lean_object* v_b_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
uint8_t v___x_1498_; 
v___x_1498_ = lean_usize_dec_lt(v_i_1489_, v_sz_1488_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; 
lean_dec_ref(v___x_1486_);
v___x_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1499_, 0, v_b_1490_);
return v___x_1499_;
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v_a_1500_ = lean_array_uget_borrowed(v_as_1487_, v_i_1489_);
v___x_1501_ = l_Lean_TSyntax_getId(v_a_1500_);
v___x_1502_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_1501_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; uint8_t v___x_1507_; lean_object* v___x_1508_; 
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_a_1503_);
lean_dec_ref(v___x_1502_);
lean_inc(v_a_1503_);
v___x_1504_ = l_Lean_LocalDecl_toExpr(v_a_1503_);
v___x_1505_ = lean_box(0);
v___x_1506_ = lean_box(0);
v___x_1507_ = 0;
lean_inc_ref(v___x_1504_);
lean_inc(v_a_1500_);
v___x_1508_ = l_Lean_Elab_Term_addTermInfo_x27(v_a_1500_, v___x_1504_, v___x_1505_, v___x_1505_, v___x_1506_, v___x_1507_, v___x_1507_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v_u_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
lean_dec_ref(v___x_1508_);
v_u_1509_ = lean_ctor_get(v___x_1486_, 1);
lean_inc(v_u_1509_);
v___x_1510_ = l_Lean_Level_succ___override(v_u_1509_);
v___x_1511_ = l_Lean_mkSort(v___x_1510_);
v___x_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
v___x_1513_ = l_Lean_LocalDecl_type(v_a_1503_);
lean_dec(v_a_1503_);
v___x_1514_ = l_Lean_Elab_Term_ensureHasType(v___x_1512_, v___x_1513_, v___x_1505_, v___x_1505_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v___x_1515_; size_t v___x_1516_; size_t v___x_1517_; 
lean_dec_ref(v___x_1514_);
v___x_1515_ = lean_array_push(v_b_1490_, v___x_1504_);
v___x_1516_ = ((size_t)1ULL);
v___x_1517_ = lean_usize_add(v_i_1489_, v___x_1516_);
v_i_1489_ = v___x_1517_;
v_b_1490_ = v___x_1515_;
goto _start;
}
else
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
lean_dec_ref(v___x_1504_);
lean_dec_ref(v_b_1490_);
lean_dec_ref(v___x_1486_);
v_a_1519_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1521_ = v___x_1514_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1514_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1519_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
else
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
lean_dec_ref(v___x_1504_);
lean_dec(v_a_1503_);
lean_dec_ref(v_b_1490_);
lean_dec_ref(v___x_1486_);
v_a_1527_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v___x_1508_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1508_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1527_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
else
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
lean_dec_ref(v_b_1490_);
lean_dec_ref(v___x_1486_);
v_a_1535_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1537_ = v___x_1502_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1502_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1___boxed(lean_object* v___x_1543_, lean_object* v_as_1544_, lean_object* v_sz_1545_, lean_object* v_i_1546_, lean_object* v_b_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
size_t v_sz_boxed_1555_; size_t v_i_boxed_1556_; lean_object* v_res_1557_; 
v_sz_boxed_1555_ = lean_unbox_usize(v_sz_1545_);
lean_dec(v_sz_1545_);
v_i_boxed_1556_ = lean_unbox_usize(v_i_1546_);
lean_dec(v_i_1546_);
v_res_1557_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1(v___x_1543_, v_as_1544_, v_sz_boxed_1555_, v_i_boxed_1556_, v_b_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec_ref(v_as_1544_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(lean_object* v_msgData_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v___x_1564_; lean_object* v_env_1565_; lean_object* v___x_1566_; lean_object* v_mctx_1567_; lean_object* v_lctx_1568_; lean_object* v_options_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1564_ = lean_st_ref_get(v___y_1562_);
v_env_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc_ref(v_env_1565_);
lean_dec(v___x_1564_);
v___x_1566_ = lean_st_ref_get(v___y_1560_);
v_mctx_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc_ref(v_mctx_1567_);
lean_dec(v___x_1566_);
v_lctx_1568_ = lean_ctor_get(v___y_1559_, 2);
v_options_1569_ = lean_ctor_get(v___y_1561_, 2);
lean_inc_ref(v_options_1569_);
lean_inc_ref(v_lctx_1568_);
v___x_1570_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1570_, 0, v_env_1565_);
lean_ctor_set(v___x_1570_, 1, v_mctx_1567_);
lean_ctor_set(v___x_1570_, 2, v_lctx_1568_);
lean_ctor_set(v___x_1570_, 3, v_options_1569_);
v___x_1571_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
lean_ctor_set(v___x_1571_, 1, v_msgData_1558_);
v___x_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2___boxed(lean_object* v_msgData_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(v_msgData_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
return v_res_1579_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0(void){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = lean_box(1);
v___x_1581_ = l_Lean_MessageData_ofFormat(v___x_1580_);
return v___x_1581_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3(void){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__2));
v___x_1586_ = l_Lean_MessageData_ofFormat(v___x_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6(lean_object* v_x_1587_, lean_object* v_x_1588_){
_start:
{
if (lean_obj_tag(v_x_1588_) == 0)
{
return v_x_1587_;
}
else
{
lean_object* v_head_1589_; lean_object* v_tail_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1612_; 
v_head_1589_ = lean_ctor_get(v_x_1588_, 0);
v_tail_1590_ = lean_ctor_get(v_x_1588_, 1);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_x_1588_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1592_ = v_x_1588_;
v_isShared_1593_ = v_isSharedCheck_1612_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_tail_1590_);
lean_inc(v_head_1589_);
lean_dec(v_x_1588_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1612_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v_before_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1610_; 
v_before_1594_ = lean_ctor_get(v_head_1589_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v_head_1589_);
if (v_isSharedCheck_1610_ == 0)
{
lean_object* v_unused_1611_; 
v_unused_1611_ = lean_ctor_get(v_head_1589_, 1);
lean_dec(v_unused_1611_);
v___x_1596_ = v_head_1589_;
v_isShared_1597_ = v_isSharedCheck_1610_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_before_1594_);
lean_dec(v_head_1589_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1610_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1598_; lean_object* v___x_1600_; 
v___x_1598_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0);
if (v_isShared_1597_ == 0)
{
lean_ctor_set_tag(v___x_1596_, 7);
lean_ctor_set(v___x_1596_, 1, v___x_1598_);
lean_ctor_set(v___x_1596_, 0, v_x_1587_);
v___x_1600_ = v___x_1596_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_x_1587_);
lean_ctor_set(v_reuseFailAlloc_1609_, 1, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
lean_object* v___x_1601_; lean_object* v___x_1603_; 
v___x_1601_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3);
if (v_isShared_1593_ == 0)
{
lean_ctor_set_tag(v___x_1592_, 7);
lean_ctor_set(v___x_1592_, 1, v___x_1601_);
lean_ctor_set(v___x_1592_, 0, v___x_1600_);
v___x_1603_ = v___x_1592_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1600_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v___x_1601_);
v___x_1603_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1604_ = l_Lean_MessageData_ofSyntax(v_before_1594_);
v___x_1605_ = l_Lean_indentD(v___x_1604_);
v___x_1606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1603_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
v_x_1587_ = v___x_1606_;
v_x_1588_ = v_tail_1590_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5(lean_object* v_opts_1613_, lean_object* v_opt_1614_){
_start:
{
lean_object* v_name_1615_; lean_object* v_defValue_1616_; lean_object* v_map_1617_; lean_object* v___x_1618_; 
v_name_1615_ = lean_ctor_get(v_opt_1614_, 0);
v_defValue_1616_ = lean_ctor_get(v_opt_1614_, 1);
v_map_1617_ = lean_ctor_get(v_opts_1613_, 0);
v___x_1618_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1617_, v_name_1615_);
if (lean_obj_tag(v___x_1618_) == 0)
{
uint8_t v___x_1619_; 
v___x_1619_ = lean_unbox(v_defValue_1616_);
return v___x_1619_;
}
else
{
lean_object* v_val_1620_; 
v_val_1620_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_val_1620_);
lean_dec_ref(v___x_1618_);
if (lean_obj_tag(v_val_1620_) == 1)
{
uint8_t v_v_1621_; 
v_v_1621_ = lean_ctor_get_uint8(v_val_1620_, 0);
lean_dec_ref(v_val_1620_);
return v_v_1621_;
}
else
{
uint8_t v___x_1622_; 
lean_dec(v_val_1620_);
v___x_1622_ = lean_unbox(v_defValue_1616_);
return v___x_1622_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5___boxed(lean_object* v_opts_1623_, lean_object* v_opt_1624_){
_start:
{
uint8_t v_res_1625_; lean_object* v_r_1626_; 
v_res_1625_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5(v_opts_1623_, v_opt_1624_);
lean_dec_ref(v_opt_1624_);
lean_dec_ref(v_opts_1623_);
v_r_1626_ = lean_box(v_res_1625_);
return v_r_1626_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1630_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__1));
v___x_1631_ = l_Lean_MessageData_ofFormat(v___x_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(lean_object* v_msgData_1632_, lean_object* v_macroStack_1633_, lean_object* v___y_1634_){
_start:
{
lean_object* v_options_1636_; lean_object* v___x_1637_; uint8_t v___x_1638_; 
v_options_1636_ = lean_ctor_get(v___y_1634_, 2);
v___x_1637_ = l_Lean_Elab_pp_macroStack;
v___x_1638_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5(v_options_1636_, v___x_1637_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; 
lean_dec(v_macroStack_1633_);
v___x_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1639_, 0, v_msgData_1632_);
return v___x_1639_;
}
else
{
if (lean_obj_tag(v_macroStack_1633_) == 0)
{
lean_object* v___x_1640_; 
v___x_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1640_, 0, v_msgData_1632_);
return v___x_1640_;
}
else
{
lean_object* v_head_1641_; lean_object* v_after_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1657_; 
v_head_1641_ = lean_ctor_get(v_macroStack_1633_, 0);
lean_inc(v_head_1641_);
v_after_1642_ = lean_ctor_get(v_head_1641_, 1);
v_isSharedCheck_1657_ = !lean_is_exclusive(v_head_1641_);
if (v_isSharedCheck_1657_ == 0)
{
lean_object* v_unused_1658_; 
v_unused_1658_ = lean_ctor_get(v_head_1641_, 0);
lean_dec(v_unused_1658_);
v___x_1644_ = v_head_1641_;
v_isShared_1645_ = v_isSharedCheck_1657_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_after_1642_);
lean_dec(v_head_1641_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1657_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1646_; lean_object* v___x_1648_; 
v___x_1646_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0);
if (v_isShared_1645_ == 0)
{
lean_ctor_set_tag(v___x_1644_, 7);
lean_ctor_set(v___x_1644_, 1, v___x_1646_);
lean_ctor_set(v___x_1644_, 0, v_msgData_1632_);
v___x_1648_ = v___x_1644_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_msgData_1632_);
lean_ctor_set(v_reuseFailAlloc_1656_, 1, v___x_1646_);
v___x_1648_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v_msgData_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1649_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2);
v___x_1650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1648_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
v___x_1651_ = l_Lean_MessageData_ofSyntax(v_after_1642_);
v___x_1652_ = l_Lean_indentD(v___x_1651_);
v_msgData_1653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1653_, 0, v___x_1650_);
lean_ctor_set(v_msgData_1653_, 1, v___x_1652_);
v___x_1654_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6(v_msgData_1653_, v_macroStack_1633_);
v___x_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
return v___x_1655_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___boxed(lean_object* v_msgData_1659_, lean_object* v_macroStack_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(v_msgData_1659_, v_macroStack_1660_, v___y_1661_);
lean_dec_ref(v___y_1661_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(lean_object* v_msg_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v_ref_1672_; lean_object* v___x_1673_; lean_object* v_a_1674_; lean_object* v_macroStack_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1686_; 
v_ref_1672_ = lean_ctor_get(v___y_1669_, 5);
v___x_1673_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(v_msg_1664_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_a_1674_);
lean_dec_ref(v___x_1673_);
v_macroStack_1675_ = lean_ctor_get(v___y_1665_, 1);
lean_inc(v_macroStack_1675_);
lean_dec_ref(v___y_1665_);
lean_inc(v_macroStack_1675_);
v___x_1676_ = l_Lean_Elab_getBetterRef(v_ref_1672_, v_macroStack_1675_);
v___x_1677_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(v_a_1674_, v_macroStack_1675_, v___y_1669_);
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1680_ = v___x_1677_;
v_isShared_1681_ = v_isSharedCheck_1686_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1677_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1686_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1682_; lean_object* v___x_1684_; 
v___x_1682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1676_);
lean_ctor_set(v___x_1682_, 1, v_a_1678_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set_tag(v___x_1680_, 1);
lean_ctor_set(v___x_1680_, 0, v___x_1682_);
v___x_1684_ = v___x_1680_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1682_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg___boxed(lean_object* v_msg_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v_msg_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
return v_res_1695_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1701_ = lean_box(0);
v___x_1702_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__2___closed__2));
v___x_1703_ = l_Lean_mkConst(v___x_1702_, v___x_1701_);
return v___x_1703_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__2___closed__5(void){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1705_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__2___closed__4));
v___x_1706_ = l_Lean_stringToMessageData(v___x_1705_);
return v___x_1706_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__2___closed__7(void){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1708_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__2___closed__6));
v___x_1709_ = l_Lean_stringToMessageData(v___x_1708_);
return v___x_1709_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__2___closed__10(void){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__2___closed__9));
v___x_1714_ = l_Lean_MessageData_ofFormat(v___x_1713_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__2(lean_object* v___y_1715_, lean_object* v_monadInfo_1716_, uint8_t v_returnsEarly_1717_, lean_object* v___x_1718_, lean_object* v_a_1719_, uint8_t v___x_1720_, lean_object* v_e_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v_defs_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___x_1753_; lean_object* v_returnVar_1755_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1788_; lean_object* v___y_1789_; 
v___x_1753_ = lean_mk_empty_array_with_capacity(v___x_1718_);
if (lean_obj_tag(v_e_1721_) == 0)
{
if (v___x_1720_ == 0)
{
goto v___jp_1802_;
}
else
{
goto v___jp_1763_;
}
}
else
{
goto v___jp_1802_;
}
v___jp_1729_:
{
size_t v_sz_1737_; size_t v___x_1738_; lean_object* v___x_1739_; 
v_sz_1737_ = lean_array_size(v___y_1715_);
v___x_1738_ = ((size_t)0ULL);
v___x_1739_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1(v_monadInfo_1716_, v___y_1715_, v_sz_1737_, v___x_1738_, v_defs_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
if (lean_obj_tag(v___x_1739_) == 0)
{
if (v_returnsEarly_1717_ == 0)
{
return v___x_1739_;
}
else
{
lean_object* v_a_1740_; lean_object* v___x_1741_; uint8_t v___x_1742_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1740_);
v___x_1741_ = lean_array_get_size(v___y_1715_);
v___x_1742_ = lean_nat_dec_eq(v___x_1741_, v___x_1718_);
if (v___x_1742_ == 0)
{
lean_dec(v_a_1740_);
return v___x_1739_;
}
else
{
lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1751_; 
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1751_ == 0)
{
lean_object* v_unused_1752_; 
v_unused_1752_ = lean_ctor_get(v___x_1739_, 0);
lean_dec(v_unused_1752_);
v___x_1744_ = v___x_1739_;
v_isShared_1745_ = v_isSharedCheck_1751_;
goto v_resetjp_1743_;
}
else
{
lean_dec(v___x_1739_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1751_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1749_; 
v___x_1746_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__2___closed__3, &l_Lean_Elab_Do_elabDoFor___lam__2___closed__3_once, _init_l_Lean_Elab_Do_elabDoFor___lam__2___closed__3);
v___x_1747_ = lean_array_push(v_a_1740_, v___x_1746_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 0, v___x_1747_);
v___x_1749_ = v___x_1744_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1747_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
}
else
{
return v___x_1739_;
}
}
v___jp_1754_:
{
lean_object* v___x_1762_; 
v___x_1762_ = lean_array_push(v___x_1753_, v_returnVar_1755_);
v_defs_1730_ = v___x_1762_;
v___y_1731_ = v___y_1756_;
v___y_1732_ = v___y_1757_;
v___y_1733_ = v___y_1758_;
v___y_1734_ = v___y_1759_;
v___y_1735_ = v___y_1760_;
v___y_1736_ = v___y_1761_;
goto v___jp_1729_;
}
v___jp_1763_:
{
if (v_returnsEarly_1717_ == 0)
{
lean_dec(v_e_1721_);
lean_dec_ref(v_a_1719_);
v_defs_1730_ = v___x_1753_;
v___y_1731_ = v___y_1722_;
v___y_1732_ = v___y_1723_;
v___y_1733_ = v___y_1724_;
v___y_1734_ = v___y_1725_;
v___y_1735_ = v___y_1726_;
v___y_1736_ = v___y_1727_;
goto v___jp_1729_;
}
else
{
if (lean_obj_tag(v_e_1721_) == 0)
{
lean_object* v_resultType_1764_; lean_object* v___x_1765_; 
v_resultType_1764_ = lean_ctor_get(v_a_1719_, 0);
lean_inc_ref(v_resultType_1764_);
lean_dec_ref(v_a_1719_);
v___x_1765_ = l_Lean_Meta_mkNone(v_resultType_1764_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_a_1766_);
lean_dec_ref(v___x_1765_);
v_returnVar_1755_ = v_a_1766_;
v___y_1756_ = v___y_1722_;
v___y_1757_ = v___y_1723_;
v___y_1758_ = v___y_1724_;
v___y_1759_ = v___y_1725_;
v___y_1760_ = v___y_1726_;
v___y_1761_ = v___y_1727_;
goto v___jp_1754_;
}
else
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
lean_dec_ref(v___x_1753_);
lean_dec_ref(v_monadInfo_1716_);
v_a_1767_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___x_1765_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1765_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
else
{
lean_object* v_val_1775_; lean_object* v_resultType_1776_; lean_object* v___x_1777_; 
v_val_1775_ = lean_ctor_get(v_e_1721_, 0);
lean_inc(v_val_1775_);
lean_dec_ref(v_e_1721_);
v_resultType_1776_ = lean_ctor_get(v_a_1719_, 0);
lean_inc_ref(v_resultType_1776_);
lean_dec_ref(v_a_1719_);
v___x_1777_ = l_Lean_Meta_mkSome(v_resultType_1776_, v_val_1775_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
lean_inc(v_a_1778_);
lean_dec_ref(v___x_1777_);
v_returnVar_1755_ = v_a_1778_;
v___y_1756_ = v___y_1722_;
v___y_1757_ = v___y_1723_;
v___y_1758_ = v___y_1724_;
v___y_1759_ = v___y_1725_;
v___y_1760_ = v___y_1726_;
v___y_1761_ = v___y_1727_;
goto v___jp_1754_;
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_dec_ref(v___x_1753_);
lean_dec_ref(v_monadInfo_1716_);
v_a_1779_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1777_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1777_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
}
}
v___jp_1787_:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1801_; 
v___x_1790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___y_1788_);
lean_ctor_set(v___x_1790_, 1, v___y_1789_);
v___x_1791_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__2___closed__5, &l_Lean_Elab_Do_elabDoFor___lam__2___closed__5_once, _init_l_Lean_Elab_Do_elabDoFor___lam__2___closed__5);
v___x_1792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1790_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
lean_inc_ref(v___y_1722_);
v___x_1793_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v___x_1792_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1796_ = v___x_1793_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1793_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
v___jp_1802_:
{
if (v_returnsEarly_1717_ == 0)
{
lean_object* v___x_1803_; 
lean_dec_ref(v___x_1753_);
lean_dec_ref(v_a_1719_);
lean_dec_ref(v_monadInfo_1716_);
v___x_1803_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__2___closed__7, &l_Lean_Elab_Do_elabDoFor___lam__2___closed__7_once, _init_l_Lean_Elab_Do_elabDoFor___lam__2___closed__7);
if (lean_obj_tag(v_e_1721_) == 0)
{
lean_object* v___x_1804_; 
v___x_1804_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__2___closed__10, &l_Lean_Elab_Do_elabDoFor___lam__2___closed__10_once, _init_l_Lean_Elab_Do_elabDoFor___lam__2___closed__10);
v___y_1788_ = v___x_1803_;
v___y_1789_ = v___x_1804_;
goto v___jp_1787_;
}
else
{
lean_object* v_val_1805_; lean_object* v___x_1806_; 
v_val_1805_ = lean_ctor_get(v_e_1721_, 0);
lean_inc(v_val_1805_);
lean_dec_ref(v_e_1721_);
v___x_1806_ = l_Lean_MessageData_ofExpr(v_val_1805_);
v___y_1788_ = v___x_1803_;
v___y_1789_ = v___x_1806_;
goto v___jp_1787_;
}
}
else
{
goto v___jp_1763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__2___boxed(lean_object* v___y_1807_, lean_object* v_monadInfo_1808_, lean_object* v_returnsEarly_1809_, lean_object* v___x_1810_, lean_object* v_a_1811_, lean_object* v___x_1812_, lean_object* v_e_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
uint8_t v_returnsEarly_boxed_1821_; uint8_t v___x_78286__boxed_1822_; lean_object* v_res_1823_; 
v_returnsEarly_boxed_1821_ = lean_unbox(v_returnsEarly_1809_);
v___x_78286__boxed_1822_ = lean_unbox(v___x_1812_);
v_res_1823_ = l_Lean_Elab_Do_elabDoFor___lam__2(v___y_1807_, v_monadInfo_1808_, v_returnsEarly_boxed_1821_, v___x_1810_, v_a_1811_, v___x_78286__boxed_1822_, v_e_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___x_1810_);
lean_dec_ref(v___y_1807_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__4(lean_object* v___f_1825_, lean_object* v_u_1826_, lean_object* v___x_1827_, lean_object* v___x_1828_, lean_object* v_snd_1829_, lean_object* v___x_1830_, lean_object* v_e_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1840_, 0, v_e_1831_);
lean_inc(v___y_1838_);
lean_inc_ref(v___y_1837_);
lean_inc(v___y_1836_);
lean_inc_ref(v___y_1835_);
lean_inc(v___y_1834_);
lean_inc_ref(v___y_1833_);
v___x_1841_ = lean_apply_8(v___f_1825_, v___x_1840_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, lean_box(0));
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1843_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_a_1842_);
lean_dec_ref(v___x_1841_);
v___x_1843_ = l_Lean_Meta_mkProdMkN(v_a_1842_, v_u_1826_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v_fst_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1844_);
lean_dec_ref(v___x_1843_);
v_fst_1845_ = lean_ctor_get(v_a_1844_, 0);
lean_inc(v_fst_1845_);
lean_dec(v_a_1844_);
v___x_1846_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__4___closed__0));
v___x_1847_ = l_Lean_Name_mkStr2(v___x_1827_, v___x_1846_);
v___x_1848_ = l_Lean_mkConst(v___x_1847_, v___x_1828_);
v___x_1849_ = l_Lean_mkAppB(v___x_1848_, v_snd_1829_, v_fst_1845_);
lean_inc_ref(v___y_1832_);
v___x_1850_ = l_Lean_Elab_Do_mkPureApp(v___x_1830_, v___x_1849_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
return v___x_1850_;
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
lean_dec_ref(v___x_1830_);
lean_dec_ref(v_snd_1829_);
lean_dec(v___x_1828_);
lean_dec_ref(v___x_1827_);
v_a_1851_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1843_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1843_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
lean_dec_ref(v___x_1830_);
lean_dec_ref(v_snd_1829_);
lean_dec(v___x_1828_);
lean_dec_ref(v___x_1827_);
lean_dec(v_u_1826_);
v_a_1859_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1841_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1841_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___boxed(lean_object* v___f_1867_, lean_object* v_u_1868_, lean_object* v___x_1869_, lean_object* v___x_1870_, lean_object* v_snd_1871_, lean_object* v___x_1872_, lean_object* v_e_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_Elab_Do_elabDoFor___lam__4(v___f_1867_, v_u_1868_, v___x_1869_, v___x_1870_, v_snd_1871_, v___x_1872_, v_e_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec_ref(v___y_1874_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__5(lean_object* v___f_1884_, lean_object* v___x_1885_, lean_object* v_u_1886_, lean_object* v___x_1887_, lean_object* v___x_1888_, lean_object* v_snd_1889_, lean_object* v___x_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v___x_1899_; 
lean_inc(v___y_1897_);
lean_inc_ref(v___y_1896_);
lean_inc(v___y_1895_);
lean_inc_ref(v___y_1894_);
lean_inc(v___y_1893_);
lean_inc_ref(v___y_1892_);
v___x_1899_ = lean_apply_8(v___f_1884_, v___x_1885_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, lean_box(0));
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v___x_1901_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
lean_inc(v_a_1900_);
lean_dec_ref(v___x_1899_);
v___x_1901_ = l_Lean_Meta_mkProdMkN(v_a_1900_, v_u_1886_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v_fst_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_a_1902_);
lean_dec_ref(v___x_1901_);
v_fst_1903_ = lean_ctor_get(v_a_1902_, 0);
lean_inc(v_fst_1903_);
lean_dec(v_a_1902_);
v___x_1904_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__5___closed__0));
v___x_1905_ = l_Lean_Name_mkStr2(v___x_1887_, v___x_1904_);
v___x_1906_ = l_Lean_mkConst(v___x_1905_, v___x_1888_);
v___x_1907_ = l_Lean_mkAppB(v___x_1906_, v_snd_1889_, v_fst_1903_);
lean_inc_ref(v___y_1891_);
v___x_1908_ = l_Lean_Elab_Do_mkPureApp(v___x_1890_, v___x_1907_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
return v___x_1908_;
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
lean_dec_ref(v___x_1890_);
lean_dec_ref(v_snd_1889_);
lean_dec(v___x_1888_);
lean_dec_ref(v___x_1887_);
v_a_1909_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1901_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1901_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_dec_ref(v___x_1890_);
lean_dec_ref(v_snd_1889_);
lean_dec(v___x_1888_);
lean_dec_ref(v___x_1887_);
lean_dec(v_u_1886_);
v_a_1917_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1899_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1899_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__5___boxed(lean_object* v___f_1925_, lean_object* v___x_1926_, lean_object* v_u_1927_, lean_object* v___x_1928_, lean_object* v___x_1929_, lean_object* v_snd_1930_, lean_object* v___x_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l_Lean_Elab_Do_elabDoFor___lam__5(v___f_1925_, v___x_1926_, v_u_1927_, v___x_1928_, v___x_1929_, v_snd_1930_, v___x_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec_ref(v___y_1932_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__6(lean_object* v___f_1941_, lean_object* v___x_1942_, lean_object* v_u_1943_, lean_object* v___x_1944_, lean_object* v___x_1945_, lean_object* v_snd_1946_, lean_object* v___x_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v___x_1956_; 
lean_inc(v___y_1954_);
lean_inc_ref(v___y_1953_);
lean_inc(v___y_1952_);
lean_inc_ref(v___y_1951_);
lean_inc(v___y_1950_);
lean_inc_ref(v___y_1949_);
v___x_1956_ = lean_apply_8(v___f_1941_, v___x_1942_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, lean_box(0));
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; lean_object* v___x_1958_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_a_1957_);
lean_dec_ref(v___x_1956_);
v___x_1958_ = l_Lean_Meta_mkProdMkN(v_a_1957_, v_u_1943_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; lean_object* v_fst_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_a_1959_);
lean_dec_ref(v___x_1958_);
v_fst_1960_ = lean_ctor_get(v_a_1959_, 0);
lean_inc(v_fst_1960_);
lean_dec(v_a_1959_);
v___x_1961_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__4___closed__0));
v___x_1962_ = l_Lean_Name_mkStr2(v___x_1944_, v___x_1961_);
v___x_1963_ = l_Lean_mkConst(v___x_1962_, v___x_1945_);
v___x_1964_ = l_Lean_mkAppB(v___x_1963_, v_snd_1946_, v_fst_1960_);
lean_inc_ref(v___y_1948_);
v___x_1965_ = l_Lean_Elab_Do_mkPureApp(v___x_1947_, v___x_1964_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
return v___x_1965_;
}
else
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
lean_dec_ref(v___x_1947_);
lean_dec_ref(v_snd_1946_);
lean_dec(v___x_1945_);
lean_dec_ref(v___x_1944_);
v_a_1966_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1968_ = v___x_1958_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1958_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1971_; 
if (v_isShared_1969_ == 0)
{
v___x_1971_ = v___x_1968_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
lean_dec_ref(v___x_1947_);
lean_dec_ref(v_snd_1946_);
lean_dec(v___x_1945_);
lean_dec_ref(v___x_1944_);
lean_dec(v_u_1943_);
v_a_1974_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1956_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1956_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1974_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__6___boxed(lean_object* v___f_1982_, lean_object* v___x_1983_, lean_object* v_u_1984_, lean_object* v___x_1985_, lean_object* v___x_1986_, lean_object* v_snd_1987_, lean_object* v___x_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Lean_Elab_Do_elabDoFor___lam__6(v___f_1982_, v___x_1983_, v_u_1984_, v___x_1985_, v___x_1986_, v_snd_1987_, v___x_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec_ref(v___y_1989_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__7(lean_object* v___x_1998_, lean_object* v___f_1999_, lean_object* v___f_2000_, lean_object* v___x_2001_, lean_object* v___x_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_){
_start:
{
lean_object* v_monadInfo_2011_; lean_object* v_mutVars_2012_; lean_object* v_mutVarDefs_2013_; lean_object* v_contInfo_2014_; uint8_t v_deadCode_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2023_; 
v_monadInfo_2011_ = lean_ctor_get(v___y_2003_, 0);
v_mutVars_2012_ = lean_ctor_get(v___y_2003_, 1);
v_mutVarDefs_2013_ = lean_ctor_get(v___y_2003_, 2);
v_contInfo_2014_ = lean_ctor_get(v___y_2003_, 4);
v_deadCode_2015_ = lean_ctor_get_uint8(v___y_2003_, sizeof(void*)*5);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___y_2003_);
if (v_isSharedCheck_2023_ == 0)
{
lean_object* v_unused_2024_; 
v_unused_2024_ = lean_ctor_get(v___y_2003_, 3);
lean_dec(v_unused_2024_);
v___x_2017_ = v___y_2003_;
v_isShared_2018_ = v_isSharedCheck_2023_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_contInfo_2014_);
lean_inc(v_mutVarDefs_2013_);
lean_inc(v_mutVars_2012_);
lean_inc(v_monadInfo_2011_);
lean_dec(v___y_2003_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2023_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 3, v___x_1998_);
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_monadInfo_2011_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_mutVars_2012_);
lean_ctor_set(v_reuseFailAlloc_2022_, 2, v_mutVarDefs_2013_);
lean_ctor_set(v_reuseFailAlloc_2022_, 3, v___x_1998_);
lean_ctor_set(v_reuseFailAlloc_2022_, 4, v_contInfo_2014_);
lean_ctor_set_uint8(v_reuseFailAlloc_2022_, sizeof(void*)*5, v_deadCode_2015_);
v___x_2020_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_2021_; 
v___x_2021_ = l_Lean_Elab_Do_enterLoopBody___redArg(v___f_1999_, v___f_2000_, v___x_2001_, v___x_2002_, v___x_2020_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
lean_dec_ref(v___x_2020_);
return v___x_2021_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__7___boxed(lean_object* v___x_2025_, lean_object* v___f_2026_, lean_object* v___f_2027_, lean_object* v___x_2028_, lean_object* v___x_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l_Lean_Elab_Do_elabDoFor___lam__7(v___x_2025_, v___f_2026_, v___f_2027_, v___x_2028_, v___x_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__8(lean_object* v_a_2042_, lean_object* v_u_2043_, lean_object* v_snd_2044_, lean_object* v___f_2045_, lean_object* v___x_2046_, lean_object* v_resultName_2047_, lean_object* v_resultType_2048_, lean_object* v_body_2049_, uint8_t v___x_2050_, lean_object* v___y_2051_, lean_object* v_xh_2052_, lean_object* v_loopS_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
lean_object* v_resultType_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2090_; 
v_resultType_2062_ = lean_ctor_get(v_a_2042_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v_a_2042_);
if (v_isSharedCheck_2090_ == 0)
{
lean_object* v_unused_2091_; 
v_unused_2091_ = lean_ctor_get(v_a_2042_, 1);
lean_dec(v_unused_2091_);
v___x_2064_ = v_a_2042_;
v_isShared_2065_ = v_isSharedCheck_2090_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_resultType_2062_);
lean_dec(v_a_2042_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2090_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___f_2073_; lean_object* v___f_2074_; lean_object* v___f_2075_; lean_object* v___x_2077_; 
v___x_2066_ = l_Lean_Expr_fvarId_x21(v_loopS_2053_);
v___x_2067_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__8___closed__0));
v___x_2068_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__8___closed__1));
v___x_2069_ = lean_box(0);
lean_inc(v_u_2043_);
v___x_2070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2070_, 0, v_u_2043_);
lean_ctor_set(v___x_2070_, 1, v___x_2069_);
lean_inc_ref(v___x_2070_);
v___x_2071_ = l_Lean_mkConst(v___x_2068_, v___x_2070_);
lean_inc_ref(v_snd_2044_);
v___x_2072_ = l_Lean_Expr_app___override(v___x_2071_, v_snd_2044_);
lean_inc_ref(v___x_2072_);
lean_inc_ref(v_snd_2044_);
lean_inc_ref(v___x_2070_);
lean_inc(v_u_2043_);
lean_inc_ref(v___f_2045_);
v___f_2073_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__4___boxed), 15, 6);
lean_closure_set(v___f_2073_, 0, v___f_2045_);
lean_closure_set(v___f_2073_, 1, v_u_2043_);
lean_closure_set(v___f_2073_, 2, v___x_2067_);
lean_closure_set(v___f_2073_, 3, v___x_2070_);
lean_closure_set(v___f_2073_, 4, v_snd_2044_);
lean_closure_set(v___f_2073_, 5, v___x_2072_);
lean_inc_ref(v___x_2072_);
lean_inc_ref(v_snd_2044_);
lean_inc_ref(v___x_2070_);
lean_inc(v_u_2043_);
lean_inc(v___x_2046_);
lean_inc_ref(v___f_2045_);
v___f_2074_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__5___boxed), 15, 7);
lean_closure_set(v___f_2074_, 0, v___f_2045_);
lean_closure_set(v___f_2074_, 1, v___x_2046_);
lean_closure_set(v___f_2074_, 2, v_u_2043_);
lean_closure_set(v___f_2074_, 3, v___x_2067_);
lean_closure_set(v___f_2074_, 4, v___x_2070_);
lean_closure_set(v___f_2074_, 5, v_snd_2044_);
lean_closure_set(v___f_2074_, 6, v___x_2072_);
lean_inc_ref(v___x_2072_);
v___f_2075_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__6___boxed), 15, 7);
lean_closure_set(v___f_2075_, 0, v___f_2045_);
lean_closure_set(v___f_2075_, 1, v___x_2046_);
lean_closure_set(v___f_2075_, 2, v_u_2043_);
lean_closure_set(v___f_2075_, 3, v___x_2067_);
lean_closure_set(v___f_2075_, 4, v___x_2070_);
lean_closure_set(v___f_2075_, 5, v_snd_2044_);
lean_closure_set(v___f_2075_, 6, v___x_2072_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 1, v___f_2073_);
v___x_2077_ = v___x_2064_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_resultType_2062_);
lean_ctor_set(v_reuseFailAlloc_2089_, 1, v___f_2073_);
v___x_2077_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
uint8_t v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___f_2082_; lean_object* v___x_2083_; 
v___x_2078_ = 1;
lean_inc_ref(v___f_2074_);
v___x_2079_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2079_, 0, v_resultName_2047_);
lean_ctor_set(v___x_2079_, 1, v_resultType_2048_);
lean_ctor_set(v___x_2079_, 2, v___f_2074_);
lean_ctor_set_uint8(v___x_2079_, sizeof(void*)*3, v___x_2078_);
v___x_2080_ = lean_box(v___x_2050_);
v___x_2081_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoSeq___boxed), 11, 3);
lean_closure_set(v___x_2081_, 0, v_body_2049_);
lean_closure_set(v___x_2081_, 1, v___x_2079_);
lean_closure_set(v___x_2081_, 2, v___x_2080_);
v___f_2082_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__7___boxed), 13, 5);
lean_closure_set(v___f_2082_, 0, v___x_2072_);
lean_closure_set(v___f_2082_, 1, v___f_2075_);
lean_closure_set(v___f_2082_, 2, v___f_2074_);
lean_closure_set(v___f_2082_, 3, v___x_2077_);
lean_closure_set(v___f_2082_, 4, v___x_2081_);
v___x_2083_ = l_Lean_Elab_Do_bindMutVarsFromTuple(v___y_2051_, v___x_2066_, v___f_2082_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v_a_2084_; lean_object* v___x_2085_; uint8_t v___x_2086_; uint8_t v___x_2087_; lean_object* v___x_2088_; 
v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_a_2084_);
lean_dec_ref(v___x_2083_);
v___x_2085_ = lean_array_push(v_xh_2052_, v_loopS_2053_);
v___x_2086_ = 0;
v___x_2087_ = 1;
v___x_2088_ = l_Lean_Meta_mkLambdaFVars(v___x_2085_, v_a_2084_, v___x_2086_, v___x_2050_, v___x_2086_, v___x_2050_, v___x_2087_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
lean_dec_ref(v___x_2085_);
return v___x_2088_;
}
else
{
lean_dec_ref(v_loopS_2053_);
lean_dec_ref(v_xh_2052_);
return v___x_2083_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__8___boxed(lean_object** _args){
lean_object* v_a_2092_ = _args[0];
lean_object* v_u_2093_ = _args[1];
lean_object* v_snd_2094_ = _args[2];
lean_object* v___f_2095_ = _args[3];
lean_object* v___x_2096_ = _args[4];
lean_object* v_resultName_2097_ = _args[5];
lean_object* v_resultType_2098_ = _args[6];
lean_object* v_body_2099_ = _args[7];
lean_object* v___x_2100_ = _args[8];
lean_object* v___y_2101_ = _args[9];
lean_object* v_xh_2102_ = _args[10];
lean_object* v_loopS_2103_ = _args[11];
lean_object* v___y_2104_ = _args[12];
lean_object* v___y_2105_ = _args[13];
lean_object* v___y_2106_ = _args[14];
lean_object* v___y_2107_ = _args[15];
lean_object* v___y_2108_ = _args[16];
lean_object* v___y_2109_ = _args[17];
lean_object* v___y_2110_ = _args[18];
lean_object* v___y_2111_ = _args[19];
_start:
{
uint8_t v___x_78842__boxed_2112_; lean_object* v_res_2113_; 
v___x_78842__boxed_2112_ = lean_unbox(v___x_2100_);
v_res_2113_ = l_Lean_Elab_Do_elabDoFor___lam__8(v_a_2092_, v_u_2093_, v_snd_2094_, v___f_2095_, v___x_2096_, v_resultName_2097_, v_resultType_2098_, v_body_2099_, v___x_78842__boxed_2112_, v___y_2101_, v_xh_2102_, v_loopS_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec_ref(v___y_2104_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9(lean_object* v_a_2114_, lean_object* v_u_2115_, lean_object* v_snd_2116_, lean_object* v___f_2117_, lean_object* v___x_2118_, lean_object* v_resultName_2119_, lean_object* v_resultType_2120_, lean_object* v_body_2121_, uint8_t v___x_2122_, lean_object* v___y_2123_, lean_object* v_a_2124_, lean_object* v_xh_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v___x_2134_; lean_object* v___f_2135_; uint8_t v___x_2136_; uint8_t v___x_2137_; lean_object* v___x_2138_; 
v___x_2134_ = lean_box(v___x_2122_);
lean_inc_ref(v_snd_2116_);
v___f_2135_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__8___boxed), 20, 11);
lean_closure_set(v___f_2135_, 0, v_a_2114_);
lean_closure_set(v___f_2135_, 1, v_u_2115_);
lean_closure_set(v___f_2135_, 2, v_snd_2116_);
lean_closure_set(v___f_2135_, 3, v___f_2117_);
lean_closure_set(v___f_2135_, 4, v___x_2118_);
lean_closure_set(v___f_2135_, 5, v_resultName_2119_);
lean_closure_set(v___f_2135_, 6, v_resultType_2120_);
lean_closure_set(v___f_2135_, 7, v_body_2121_);
lean_closure_set(v___f_2135_, 8, v___x_2134_);
lean_closure_set(v___f_2135_, 9, v___y_2123_);
lean_closure_set(v___f_2135_, 10, v_xh_2125_);
v___x_2136_ = 0;
v___x_2137_ = 1;
v___x_2138_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_a_2124_, v___x_2136_, v_snd_2116_, v___f_2135_, v___x_2137_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9___boxed(lean_object** _args){
lean_object* v_a_2139_ = _args[0];
lean_object* v_u_2140_ = _args[1];
lean_object* v_snd_2141_ = _args[2];
lean_object* v___f_2142_ = _args[3];
lean_object* v___x_2143_ = _args[4];
lean_object* v_resultName_2144_ = _args[5];
lean_object* v_resultType_2145_ = _args[6];
lean_object* v_body_2146_ = _args[7];
lean_object* v___x_2147_ = _args[8];
lean_object* v___y_2148_ = _args[9];
lean_object* v_a_2149_ = _args[10];
lean_object* v_xh_2150_ = _args[11];
lean_object* v___y_2151_ = _args[12];
lean_object* v___y_2152_ = _args[13];
lean_object* v___y_2153_ = _args[14];
lean_object* v___y_2154_ = _args[15];
lean_object* v___y_2155_ = _args[16];
lean_object* v___y_2156_ = _args[17];
lean_object* v___y_2157_ = _args[18];
lean_object* v___y_2158_ = _args[19];
_start:
{
uint8_t v___x_78946__boxed_2159_; lean_object* v_res_2160_; 
v___x_78946__boxed_2159_ = lean_unbox(v___x_2147_);
v_res_2160_ = l_Lean_Elab_Do_elabDoFor___lam__9(v_a_2139_, v_u_2140_, v_snd_2141_, v___f_2142_, v___x_2143_, v_resultName_2144_, v_resultType_2145_, v_body_2146_, v___x_78946__boxed_2159_, v___y_2148_, v_a_2149_, v_xh_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec_ref(v___y_2151_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(lean_object* v_name_2161_, lean_object* v_type_2162_, lean_object* v_k_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
uint8_t v___x_2172_; uint8_t v___x_2173_; lean_object* v___x_2174_; 
v___x_2172_ = 0;
v___x_2173_ = 0;
v___x_2174_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_name_2161_, v___x_2172_, v_type_2162_, v_k_2163_, v___x_2173_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg___boxed(lean_object* v_name_2175_, lean_object* v_type_2176_, lean_object* v_k_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(v_name_2175_, v_type_2176_, v_k_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec_ref(v___y_2178_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__10(uint8_t v_returnsEarly_2204_, lean_object* v_dec_2205_, lean_object* v_a_2206_, lean_object* v_doBlockResultType_2207_, lean_object* v_a_2208_, lean_object* v_v_2209_, lean_object* v_u_2210_, lean_object* v___f_2211_, lean_object* v___y_2212_, lean_object* v___x_2213_, lean_object* v___x_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
lean_object* v_ret_2224_; lean_object* v___y_2225_; lean_object* v___y_2226_; lean_object* v___y_2227_; lean_object* v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; 
if (v_returnsEarly_2204_ == 0)
{
lean_object* v___x_2278_; 
lean_dec_ref(v___f_2211_);
lean_dec(v_u_2210_);
lean_dec(v_v_2209_);
lean_dec_ref(v_a_2208_);
lean_dec_ref(v_doBlockResultType_2207_);
lean_dec(v_a_2206_);
v___x_2278_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_dec_2205_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
return v___x_2278_;
}
else
{
lean_object* v___x_2279_; 
v___x_2279_ = l_Lean_Meta_getFVarFromUserName(v_a_2206_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; lean_object* v___x_2281_; uint8_t v___x_2282_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_a_2280_);
lean_dec_ref(v___x_2279_);
v___x_2281_ = lean_array_get_size(v___y_2212_);
v___x_2282_ = lean_nat_dec_eq(v___x_2281_, v___x_2213_);
if (v___x_2282_ == 0)
{
v_ret_2224_ = v_a_2280_;
v___y_2225_ = v___y_2215_;
v___y_2226_ = v___y_2216_;
v___y_2227_ = v___y_2217_;
v___y_2228_ = v___y_2218_;
v___y_2229_ = v___y_2219_;
v___y_2230_ = v___y_2220_;
v___y_2231_ = v___y_2221_;
goto v___jp_2223_;
}
else
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2283_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__10___closed__9));
v___x_2284_ = lean_mk_empty_array_with_capacity(v___x_2214_);
v___x_2285_ = lean_array_push(v___x_2284_, v_a_2280_);
v___x_2286_ = l_Lean_Meta_mkAppM(v___x_2283_, v___x_2285_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_a_2287_; 
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_a_2287_);
lean_dec_ref(v___x_2286_);
v_ret_2224_ = v_a_2287_;
v___y_2225_ = v___y_2215_;
v___y_2226_ = v___y_2216_;
v___y_2227_ = v___y_2217_;
v___y_2228_ = v___y_2218_;
v___y_2229_ = v___y_2219_;
v___y_2230_ = v___y_2220_;
v___y_2231_ = v___y_2221_;
goto v___jp_2223_;
}
else
{
lean_dec_ref(v___f_2211_);
lean_dec(v_u_2210_);
lean_dec(v_v_2209_);
lean_dec_ref(v_a_2208_);
lean_dec_ref(v_doBlockResultType_2207_);
lean_dec_ref(v_dec_2205_);
return v___x_2286_;
}
}
}
else
{
lean_dec_ref(v___f_2211_);
lean_dec(v_u_2210_);
lean_dec(v_v_2209_);
lean_dec_ref(v_a_2208_);
lean_dec_ref(v_doBlockResultType_2207_);
lean_dec_ref(v_dec_2205_);
return v___x_2279_;
}
}
v___jp_2223_:
{
lean_object* v___x_2232_; 
lean_inc(v___y_2231_);
lean_inc_ref(v___y_2230_);
lean_inc(v___y_2229_);
lean_inc_ref(v___y_2228_);
lean_inc_ref(v_ret_2224_);
v___x_2232_ = lean_infer_type(v_ret_2224_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; lean_object* v___x_2234_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2233_);
lean_dec_ref(v___x_2232_);
lean_inc_ref(v___y_2225_);
v___x_2234_ = l_Lean_Elab_Do_mkMonadicType___redArg(v_doBlockResultType_2207_, v___y_2225_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; lean_object* v___x_2236_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_a_2235_);
lean_dec_ref(v___x_2234_);
v___x_2236_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_dec_2205_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_a_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_a_2237_);
lean_dec_ref(v___x_2236_);
v___x_2238_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__10___closed__1));
v___x_2239_ = l_Lean_Core_mkFreshUserName(v___x_2238_, v___y_2230_, v___y_2231_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; lean_object* v_resultType_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2268_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_a_2240_);
lean_dec_ref(v___x_2239_);
v_resultType_2241_ = lean_ctor_get(v_a_2208_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v_a_2208_);
if (v_isSharedCheck_2268_ == 0)
{
lean_object* v_unused_2269_; 
v_unused_2269_ = lean_ctor_get(v_a_2208_, 1);
lean_dec(v_unused_2269_);
v___x_2243_ = v_a_2208_;
v_isShared_2244_ = v_isSharedCheck_2268_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_resultType_2241_);
lean_dec(v_a_2208_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2268_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; uint8_t v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2252_; 
v___x_2245_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__10___closed__2));
v___x_2246_ = 0;
v___x_2247_ = l_Lean_mkLambda(v___x_2245_, v___x_2246_, v_a_2233_, v_a_2235_);
v___x_2248_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__10___closed__6));
v___x_2249_ = l_Lean_Level_succ___override(v_v_2209_);
v___x_2250_ = lean_box(0);
if (v_isShared_2244_ == 0)
{
lean_ctor_set_tag(v___x_2243_, 1);
lean_ctor_set(v___x_2243_, 1, v___x_2250_);
lean_ctor_set(v___x_2243_, 0, v___x_2249_);
v___x_2252_ = v___x_2243_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___x_2249_);
lean_ctor_set(v_reuseFailAlloc_2267_, 1, v___x_2250_);
v___x_2252_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2253_, 0, v_u_2210_);
lean_ctor_set(v___x_2253_, 1, v___x_2252_);
v___x_2254_ = l_Lean_mkConst(v___x_2248_, v___x_2253_);
lean_inc_ref(v_resultType_2241_);
v___x_2255_ = l_Lean_mkApp3(v___x_2254_, v_resultType_2241_, v___x_2247_, v_ret_2224_);
v___x_2256_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(v_a_2240_, v_resultType_2241_, v___f_2211_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2266_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2259_ = v___x_2256_;
v_isShared_2260_ = v_isSharedCheck_2266_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2256_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2266_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2264_; 
v___x_2261_ = l_Lean_mkSimpleThunk(v_a_2237_);
v___x_2262_ = l_Lean_mkAppB(v___x_2255_, v_a_2257_, v___x_2261_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 0, v___x_2262_);
v___x_2264_ = v___x_2259_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2262_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
else
{
lean_dec_ref(v___x_2255_);
lean_dec(v_a_2237_);
return v___x_2256_;
}
}
}
}
else
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2277_; 
lean_dec(v_a_2237_);
lean_dec(v_a_2235_);
lean_dec(v_a_2233_);
lean_dec_ref(v_ret_2224_);
lean_dec_ref(v___f_2211_);
lean_dec(v_u_2210_);
lean_dec(v_v_2209_);
lean_dec_ref(v_a_2208_);
v_a_2270_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2272_ = v___x_2239_;
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2239_);
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
else
{
lean_dec(v_a_2235_);
lean_dec(v_a_2233_);
lean_dec_ref(v_ret_2224_);
lean_dec_ref(v___f_2211_);
lean_dec(v_u_2210_);
lean_dec(v_v_2209_);
lean_dec_ref(v_a_2208_);
return v___x_2236_;
}
}
else
{
lean_dec(v_a_2233_);
lean_dec_ref(v_ret_2224_);
lean_dec_ref(v___f_2211_);
lean_dec(v_u_2210_);
lean_dec(v_v_2209_);
lean_dec_ref(v_a_2208_);
lean_dec_ref(v_dec_2205_);
return v___x_2234_;
}
}
else
{
lean_dec_ref(v_ret_2224_);
lean_dec_ref(v___f_2211_);
lean_dec(v_u_2210_);
lean_dec(v_v_2209_);
lean_dec_ref(v_a_2208_);
lean_dec_ref(v_doBlockResultType_2207_);
lean_dec_ref(v_dec_2205_);
return v___x_2232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___boxed(lean_object** _args){
lean_object* v_returnsEarly_2288_ = _args[0];
lean_object* v_dec_2289_ = _args[1];
lean_object* v_a_2290_ = _args[2];
lean_object* v_doBlockResultType_2291_ = _args[3];
lean_object* v_a_2292_ = _args[4];
lean_object* v_v_2293_ = _args[5];
lean_object* v_u_2294_ = _args[6];
lean_object* v___f_2295_ = _args[7];
lean_object* v___y_2296_ = _args[8];
lean_object* v___x_2297_ = _args[9];
lean_object* v___x_2298_ = _args[10];
lean_object* v___y_2299_ = _args[11];
lean_object* v___y_2300_ = _args[12];
lean_object* v___y_2301_ = _args[13];
lean_object* v___y_2302_ = _args[14];
lean_object* v___y_2303_ = _args[15];
lean_object* v___y_2304_ = _args[16];
lean_object* v___y_2305_ = _args[17];
lean_object* v___y_2306_ = _args[18];
_start:
{
uint8_t v_returnsEarly_boxed_2307_; lean_object* v_res_2308_; 
v_returnsEarly_boxed_2307_ = lean_unbox(v_returnsEarly_2288_);
v_res_2308_ = l_Lean_Elab_Do_elabDoFor___lam__10(v_returnsEarly_boxed_2307_, v_dec_2289_, v_a_2290_, v_doBlockResultType_2291_, v_a_2292_, v_v_2293_, v_u_2294_, v___f_2295_, v___y_2296_, v___x_2297_, v___x_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___x_2298_);
lean_dec(v___x_2297_);
lean_dec_ref(v___y_2296_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__11(lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___x_2311_, uint8_t v___x_2312_, lean_object* v_postS_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2322_ = l_Lean_Expr_fvarId_x21(v_postS_2313_);
v___x_2323_ = l_Lean_Elab_Do_bindMutVarsFromTuple(v___y_2309_, v___x_2322_, v___y_2310_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; uint8_t v___x_2327_; uint8_t v___x_2328_; lean_object* v___x_2329_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2324_);
lean_dec_ref(v___x_2323_);
v___x_2325_ = lean_mk_empty_array_with_capacity(v___x_2311_);
v___x_2326_ = lean_array_push(v___x_2325_, v_postS_2313_);
v___x_2327_ = 0;
v___x_2328_ = 1;
v___x_2329_ = l_Lean_Meta_mkLambdaFVars(v___x_2326_, v_a_2324_, v___x_2327_, v___x_2312_, v___x_2327_, v___x_2312_, v___x_2328_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
lean_dec_ref(v___x_2326_);
return v___x_2329_;
}
else
{
lean_dec_ref(v_postS_2313_);
return v___x_2323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__11___boxed(lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___x_2332_, lean_object* v___x_2333_, lean_object* v_postS_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
uint8_t v___x_79256__boxed_2343_; lean_object* v_res_2344_; 
v___x_79256__boxed_2343_ = lean_unbox(v___x_2333_);
v_res_2344_ = l_Lean_Elab_Do_elabDoFor___lam__11(v___y_2330_, v___y_2331_, v___x_2332_, v___x_79256__boxed_2343_, v_postS_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
lean_dec(v___y_2339_);
lean_dec_ref(v___y_2338_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
lean_dec_ref(v___y_2335_);
lean_dec(v___x_2332_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__12(lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v___x_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_val_2355_, lean_object* v_a_2356_, lean_object* v_x_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2366_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__12___closed__2));
v___x_2367_ = lean_box(0);
v___x_2368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2368_, 0, v_a_2350_);
lean_ctor_set(v___x_2368_, 1, v___x_2367_);
v___x_2369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2369_, 0, v_a_2351_);
lean_ctor_set(v___x_2369_, 1, v___x_2368_);
v___x_2370_ = l_Lean_mkConst(v___x_2366_, v___x_2369_);
v___x_2371_ = l_Lean_instInhabitedExpr;
v___x_2372_ = lean_array_get_borrowed(v___x_2371_, v_x_2357_, v___x_2352_);
lean_inc(v___x_2372_);
v___x_2373_ = l_Lean_mkApp5(v___x_2370_, v_a_2353_, v_a_2354_, v_val_2355_, v_a_2356_, v___x_2372_);
v___x_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__12___boxed(lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v___x_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_val_2380_, lean_object* v_a_2381_, lean_object* v_x_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_Lean_Elab_Do_elabDoFor___lam__12(v_a_2375_, v_a_2376_, v___x_2377_, v_a_2378_, v_a_2379_, v_val_2380_, v_a_2381_, v_x_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec_ref(v_x_2382_);
lean_dec(v___x_2377_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___lam__0(lean_object* v___x_2392_, lean_object* v_a_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_77642__overap_2403_; lean_object* v___x_2404_; 
v___x_2402_ = l_Lean_instInhabitedExpr;
v___x_77642__overap_2403_ = l_instInhabitedOfMonad___redArg(v___x_2392_, v___x_2402_);
lean_inc(v___y_2400_);
lean_inc_ref(v___y_2399_);
lean_inc(v___y_2398_);
lean_inc_ref(v___y_2397_);
lean_inc(v___y_2396_);
lean_inc_ref(v___y_2395_);
lean_inc_ref(v___y_2394_);
v___x_2404_ = lean_apply_8(v___x_77642__overap_2403_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, lean_box(0));
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___lam__0___boxed(lean_object* v___x_2405_, lean_object* v_a_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___lam__0(v___x_2405_, v_a_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec_ref(v_a_2406_);
return v_res_2415_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_2416_; 
v___x_2416_ = l_instMonadEIO(lean_box(0));
return v___x_2416_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2417_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__0);
v___x_2418_ = l_StateRefT_x27_instMonad___redArg(v___x_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___lam__1___boxed(lean_object* v_acc_2425_, lean_object* v_declInfos_2426_, lean_object* v_k_2427_, lean_object* v_kind_2428_, lean_object* v_x_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
uint8_t v_kind_boxed_2438_; lean_object* v_res_2439_; 
v_kind_boxed_2438_ = lean_unbox(v_kind_2428_);
v_res_2439_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___lam__1(v_acc_2425_, v_declInfos_2426_, v_k_2427_, v_kind_boxed_2438_, v_x_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec_ref(v___y_2430_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg(lean_object* v_declInfos_2440_, lean_object* v_k_2441_, uint8_t v_kind_2442_, lean_object* v_acc_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v___x_2452_; lean_object* v_toApplicative_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2571_; 
v___x_2452_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__1);
v_toApplicative_2453_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2571_ == 0)
{
lean_object* v_unused_2572_; 
v_unused_2572_ = lean_ctor_get(v___x_2452_, 1);
lean_dec(v_unused_2572_);
v___x_2455_ = v___x_2452_;
v_isShared_2456_ = v_isSharedCheck_2571_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_toApplicative_2453_);
lean_dec(v___x_2452_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2571_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v_toFunctor_2457_; lean_object* v_toSeq_2458_; lean_object* v_toSeqLeft_2459_; lean_object* v_toSeqRight_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2569_; 
v_toFunctor_2457_ = lean_ctor_get(v_toApplicative_2453_, 0);
v_toSeq_2458_ = lean_ctor_get(v_toApplicative_2453_, 2);
v_toSeqLeft_2459_ = lean_ctor_get(v_toApplicative_2453_, 3);
v_toSeqRight_2460_ = lean_ctor_get(v_toApplicative_2453_, 4);
v_isSharedCheck_2569_ = !lean_is_exclusive(v_toApplicative_2453_);
if (v_isSharedCheck_2569_ == 0)
{
lean_object* v_unused_2570_; 
v_unused_2570_ = lean_ctor_get(v_toApplicative_2453_, 1);
lean_dec(v_unused_2570_);
v___x_2462_ = v_toApplicative_2453_;
v_isShared_2463_ = v_isSharedCheck_2569_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_toSeqRight_2460_);
lean_inc(v_toSeqLeft_2459_);
lean_inc(v_toSeq_2458_);
lean_inc(v_toFunctor_2457_);
lean_dec(v_toApplicative_2453_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2569_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___f_2464_; lean_object* v___f_2465_; lean_object* v___f_2466_; lean_object* v___f_2467_; lean_object* v___x_2468_; lean_object* v___f_2469_; lean_object* v___f_2470_; lean_object* v___f_2471_; lean_object* v___x_2473_; 
v___f_2464_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__2));
v___f_2465_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__3));
lean_inc_ref(v_toFunctor_2457_);
v___f_2466_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2466_, 0, v_toFunctor_2457_);
v___f_2467_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2467_, 0, v_toFunctor_2457_);
v___x_2468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2468_, 0, v___f_2466_);
lean_ctor_set(v___x_2468_, 1, v___f_2467_);
v___f_2469_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2469_, 0, v_toSeqRight_2460_);
v___f_2470_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2470_, 0, v_toSeqLeft_2459_);
v___f_2471_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2471_, 0, v_toSeq_2458_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 4, v___f_2469_);
lean_ctor_set(v___x_2462_, 3, v___f_2470_);
lean_ctor_set(v___x_2462_, 2, v___f_2471_);
lean_ctor_set(v___x_2462_, 1, v___f_2464_);
lean_ctor_set(v___x_2462_, 0, v___x_2468_);
v___x_2473_ = v___x_2462_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v___x_2468_);
lean_ctor_set(v_reuseFailAlloc_2568_, 1, v___f_2464_);
lean_ctor_set(v_reuseFailAlloc_2568_, 2, v___f_2471_);
lean_ctor_set(v_reuseFailAlloc_2568_, 3, v___f_2470_);
lean_ctor_set(v_reuseFailAlloc_2568_, 4, v___f_2469_);
v___x_2473_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
lean_object* v___x_2475_; 
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 1, v___f_2465_);
lean_ctor_set(v___x_2455_, 0, v___x_2473_);
v___x_2475_ = v___x_2455_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v___x_2473_);
lean_ctor_set(v_reuseFailAlloc_2567_, 1, v___f_2465_);
v___x_2475_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
lean_object* v___x_2476_; lean_object* v_toApplicative_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2565_; 
v___x_2476_ = l_StateRefT_x27_instMonad___redArg(v___x_2475_);
v_toApplicative_2477_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2565_ == 0)
{
lean_object* v_unused_2566_; 
v_unused_2566_ = lean_ctor_get(v___x_2476_, 1);
lean_dec(v_unused_2566_);
v___x_2479_ = v___x_2476_;
v_isShared_2480_ = v_isSharedCheck_2565_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_toApplicative_2477_);
lean_dec(v___x_2476_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2565_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v_toFunctor_2481_; lean_object* v_toSeq_2482_; lean_object* v_toSeqLeft_2483_; lean_object* v_toSeqRight_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2563_; 
v_toFunctor_2481_ = lean_ctor_get(v_toApplicative_2477_, 0);
v_toSeq_2482_ = lean_ctor_get(v_toApplicative_2477_, 2);
v_toSeqLeft_2483_ = lean_ctor_get(v_toApplicative_2477_, 3);
v_toSeqRight_2484_ = lean_ctor_get(v_toApplicative_2477_, 4);
v_isSharedCheck_2563_ = !lean_is_exclusive(v_toApplicative_2477_);
if (v_isSharedCheck_2563_ == 0)
{
lean_object* v_unused_2564_; 
v_unused_2564_ = lean_ctor_get(v_toApplicative_2477_, 1);
lean_dec(v_unused_2564_);
v___x_2486_ = v_toApplicative_2477_;
v_isShared_2487_ = v_isSharedCheck_2563_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_toSeqRight_2484_);
lean_inc(v_toSeqLeft_2483_);
lean_inc(v_toSeq_2482_);
lean_inc(v_toFunctor_2481_);
lean_dec(v_toApplicative_2477_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2563_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___f_2488_; lean_object* v___f_2489_; lean_object* v___f_2490_; lean_object* v___f_2491_; lean_object* v___x_2492_; lean_object* v___f_2493_; lean_object* v___f_2494_; lean_object* v___f_2495_; lean_object* v___x_2497_; 
v___f_2488_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__4));
v___f_2489_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__5));
lean_inc_ref(v_toFunctor_2481_);
v___f_2490_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2490_, 0, v_toFunctor_2481_);
v___f_2491_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2491_, 0, v_toFunctor_2481_);
v___x_2492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2492_, 0, v___f_2490_);
lean_ctor_set(v___x_2492_, 1, v___f_2491_);
v___f_2493_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2493_, 0, v_toSeqRight_2484_);
v___f_2494_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2494_, 0, v_toSeqLeft_2483_);
v___f_2495_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2495_, 0, v_toSeq_2482_);
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 4, v___f_2493_);
lean_ctor_set(v___x_2486_, 3, v___f_2494_);
lean_ctor_set(v___x_2486_, 2, v___f_2495_);
lean_ctor_set(v___x_2486_, 1, v___f_2488_);
lean_ctor_set(v___x_2486_, 0, v___x_2492_);
v___x_2497_ = v___x_2486_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2492_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v___f_2488_);
lean_ctor_set(v_reuseFailAlloc_2562_, 2, v___f_2495_);
lean_ctor_set(v_reuseFailAlloc_2562_, 3, v___f_2494_);
lean_ctor_set(v_reuseFailAlloc_2562_, 4, v___f_2493_);
v___x_2497_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
lean_object* v___x_2499_; 
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 1, v___f_2489_);
lean_ctor_set(v___x_2479_, 0, v___x_2497_);
v___x_2499_ = v___x_2479_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2497_);
lean_ctor_set(v_reuseFailAlloc_2561_, 1, v___f_2489_);
v___x_2499_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
lean_object* v___x_2500_; lean_object* v_toApplicative_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2559_; 
v___x_2500_ = l_StateRefT_x27_instMonad___redArg(v___x_2499_);
v_toApplicative_2501_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2559_ == 0)
{
lean_object* v_unused_2560_; 
v_unused_2560_ = lean_ctor_get(v___x_2500_, 1);
lean_dec(v_unused_2560_);
v___x_2503_ = v___x_2500_;
v_isShared_2504_ = v_isSharedCheck_2559_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_toApplicative_2501_);
lean_dec(v___x_2500_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2559_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v_toFunctor_2505_; lean_object* v_toSeq_2506_; lean_object* v_toSeqLeft_2507_; lean_object* v_toSeqRight_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2557_; 
v_toFunctor_2505_ = lean_ctor_get(v_toApplicative_2501_, 0);
v_toSeq_2506_ = lean_ctor_get(v_toApplicative_2501_, 2);
v_toSeqLeft_2507_ = lean_ctor_get(v_toApplicative_2501_, 3);
v_toSeqRight_2508_ = lean_ctor_get(v_toApplicative_2501_, 4);
v_isSharedCheck_2557_ = !lean_is_exclusive(v_toApplicative_2501_);
if (v_isSharedCheck_2557_ == 0)
{
lean_object* v_unused_2558_; 
v_unused_2558_ = lean_ctor_get(v_toApplicative_2501_, 1);
lean_dec(v_unused_2558_);
v___x_2510_ = v_toApplicative_2501_;
v_isShared_2511_ = v_isSharedCheck_2557_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_toSeqRight_2508_);
lean_inc(v_toSeqLeft_2507_);
lean_inc(v_toSeq_2506_);
lean_inc(v_toFunctor_2505_);
lean_dec(v_toApplicative_2501_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2557_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___f_2512_; lean_object* v___f_2513_; lean_object* v___f_2514_; lean_object* v___f_2515_; lean_object* v___x_2516_; lean_object* v___f_2517_; lean_object* v___f_2518_; lean_object* v___f_2519_; lean_object* v___x_2521_; 
v___f_2512_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__6));
v___f_2513_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___closed__7));
lean_inc_ref(v_toFunctor_2505_);
v___f_2514_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2514_, 0, v_toFunctor_2505_);
v___f_2515_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2515_, 0, v_toFunctor_2505_);
v___x_2516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___f_2514_);
lean_ctor_set(v___x_2516_, 1, v___f_2515_);
v___f_2517_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2517_, 0, v_toSeqRight_2508_);
v___f_2518_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2518_, 0, v_toSeqLeft_2507_);
v___f_2519_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2519_, 0, v_toSeq_2506_);
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 4, v___f_2517_);
lean_ctor_set(v___x_2510_, 3, v___f_2518_);
lean_ctor_set(v___x_2510_, 2, v___f_2519_);
lean_ctor_set(v___x_2510_, 1, v___f_2512_);
lean_ctor_set(v___x_2510_, 0, v___x_2516_);
v___x_2521_ = v___x_2510_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v___x_2516_);
lean_ctor_set(v_reuseFailAlloc_2556_, 1, v___f_2512_);
lean_ctor_set(v_reuseFailAlloc_2556_, 2, v___f_2519_);
lean_ctor_set(v_reuseFailAlloc_2556_, 3, v___f_2518_);
lean_ctor_set(v_reuseFailAlloc_2556_, 4, v___f_2517_);
v___x_2521_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
lean_object* v___x_2523_; 
if (v_isShared_2504_ == 0)
{
lean_ctor_set(v___x_2503_, 1, v___f_2513_);
lean_ctor_set(v___x_2503_, 0, v___x_2521_);
v___x_2523_ = v___x_2503_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v___x_2521_);
lean_ctor_set(v_reuseFailAlloc_2555_, 1, v___f_2513_);
v___x_2523_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; uint8_t v___x_2527_; 
v___x_2524_ = l_ReaderT_instMonad___redArg(v___x_2523_);
v___x_2525_ = lean_array_get_size(v_acc_2443_);
v___x_2526_ = lean_array_get_size(v_declInfos_2440_);
v___x_2527_ = lean_nat_dec_lt(v___x_2525_, v___x_2526_);
if (v___x_2527_ == 0)
{
lean_object* v___x_2528_; 
lean_dec_ref(v___x_2524_);
lean_dec_ref(v_declInfos_2440_);
lean_inc(v___y_2450_);
lean_inc_ref(v___y_2449_);
lean_inc(v___y_2448_);
lean_inc_ref(v___y_2447_);
lean_inc(v___y_2446_);
lean_inc_ref(v___y_2445_);
lean_inc_ref(v___y_2444_);
v___x_2528_ = lean_apply_9(v_k_2441_, v_acc_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, lean_box(0));
return v___x_2528_;
}
else
{
lean_object* v___f_2529_; lean_object* v___x_2530_; uint8_t v___x_2531_; lean_object* v___f_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v_snd_2537_; lean_object* v_fst_2538_; lean_object* v_fst_2539_; lean_object* v_snd_2540_; lean_object* v___x_2541_; 
v___f_2529_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2529_, 0, v___x_2524_);
v___x_2530_ = lean_box(0);
v___x_2531_ = 0;
v___f_2532_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2532_, 0, v___f_2529_);
v___x_2533_ = lean_box(v___x_2531_);
v___x_2534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2533_);
lean_ctor_set(v___x_2534_, 1, v___f_2532_);
v___x_2535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2530_);
lean_ctor_set(v___x_2535_, 1, v___x_2534_);
v___x_2536_ = lean_array_get_borrowed(v___x_2535_, v_declInfos_2440_, v___x_2525_);
v_snd_2537_ = lean_ctor_get(v___x_2536_, 1);
v_fst_2538_ = lean_ctor_get(v___x_2536_, 0);
lean_inc(v_fst_2538_);
v_fst_2539_ = lean_ctor_get(v_snd_2537_, 0);
lean_inc(v_fst_2539_);
v_snd_2540_ = lean_ctor_get(v_snd_2537_, 1);
lean_inc(v_snd_2540_);
lean_inc(v___y_2450_);
lean_inc_ref(v___y_2449_);
lean_inc(v___y_2448_);
lean_inc_ref(v___y_2447_);
lean_inc(v___y_2446_);
lean_inc_ref(v___y_2445_);
lean_inc_ref(v___y_2444_);
lean_inc_ref(v_acc_2443_);
v___x_2541_ = lean_apply_9(v_snd_2540_, v_acc_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, lean_box(0));
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v_a_2542_; lean_object* v___x_2543_; lean_object* v___f_2544_; uint8_t v___x_2545_; lean_object* v___x_2546_; 
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
lean_inc(v_a_2542_);
lean_dec_ref(v___x_2541_);
v___x_2543_ = lean_box(v_kind_2442_);
v___f_2544_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___lam__1___boxed), 13, 4);
lean_closure_set(v___f_2544_, 0, v_acc_2443_);
lean_closure_set(v___f_2544_, 1, v_declInfos_2440_);
lean_closure_set(v___f_2544_, 2, v_k_2441_);
lean_closure_set(v___f_2544_, 3, v___x_2543_);
v___x_2545_ = lean_unbox(v_fst_2539_);
lean_dec(v_fst_2539_);
v___x_2546_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_fst_2538_, v___x_2545_, v_a_2542_, v___f_2544_, v_kind_2442_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
return v___x_2546_;
}
else
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2554_; 
lean_dec(v_fst_2539_);
lean_dec(v_fst_2538_);
lean_dec_ref(v_acc_2443_);
lean_dec_ref(v_k_2441_);
lean_dec_ref(v_declInfos_2440_);
v_a_2547_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2549_ = v___x_2541_;
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___x_2541_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2552_; 
if (v_isShared_2550_ == 0)
{
v___x_2552_ = v___x_2549_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_a_2547_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___lam__1(lean_object* v_acc_2573_, lean_object* v_declInfos_2574_, lean_object* v_k_2575_, uint8_t v_kind_2576_, lean_object* v_x_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2586_ = lean_array_push(v_acc_2573_, v_x_2577_);
v___x_2587_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg(v_declInfos_2574_, v_k_2575_, v_kind_2576_, v___x_2586_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_declInfos_2588_, lean_object* v_k_2589_, lean_object* v_kind_2590_, lean_object* v_acc_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
uint8_t v_kind_boxed_2600_; lean_object* v_res_2601_; 
v_kind_boxed_2600_ = lean_unbox(v_kind_2590_);
v_res_2601_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg(v_declInfos_2588_, v_k_2589_, v_kind_boxed_2600_, v_acc_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec_ref(v___y_2592_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___redArg(lean_object* v_inst_2604_, lean_object* v_declInfos_2605_, lean_object* v_k_2606_, uint8_t v_kind_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2616_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___redArg___closed__0));
v___x_2617_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg(v_declInfos_2605_, v_k_2606_, v_kind_2607_, v___x_2616_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___redArg___boxed(lean_object* v_inst_2618_, lean_object* v_declInfos_2619_, lean_object* v_k_2620_, lean_object* v_kind_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
uint8_t v_kind_boxed_2630_; lean_object* v_res_2631_; 
v_kind_boxed_2630_ = lean_unbox(v_kind_2621_);
v_res_2631_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___redArg(v_inst_2618_, v_declInfos_2619_, v_k_2620_, v_kind_boxed_2630_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v_inst_2618_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(size_t v_sz_2632_, size_t v_i_2633_, lean_object* v_bs_2634_){
_start:
{
uint8_t v___x_2635_; 
v___x_2635_ = lean_usize_dec_lt(v_i_2633_, v_sz_2632_);
if (v___x_2635_ == 0)
{
return v_bs_2634_;
}
else
{
lean_object* v_v_2636_; lean_object* v_fst_2637_; lean_object* v_snd_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2654_; 
v_v_2636_ = lean_array_uget(v_bs_2634_, v_i_2633_);
v_fst_2637_ = lean_ctor_get(v_v_2636_, 0);
v_snd_2638_ = lean_ctor_get(v_v_2636_, 1);
v_isSharedCheck_2654_ = !lean_is_exclusive(v_v_2636_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2640_ = v_v_2636_;
v_isShared_2641_ = v_isSharedCheck_2654_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_snd_2638_);
lean_inc(v_fst_2637_);
lean_dec(v_v_2636_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2654_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2642_; lean_object* v_bs_x27_2643_; uint8_t v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2647_; 
v___x_2642_ = lean_unsigned_to_nat(0u);
v_bs_x27_2643_ = lean_array_uset(v_bs_2634_, v_i_2633_, v___x_2642_);
v___x_2644_ = 0;
v___x_2645_ = lean_box(v___x_2644_);
if (v_isShared_2641_ == 0)
{
lean_ctor_set(v___x_2640_, 0, v___x_2645_);
v___x_2647_ = v___x_2640_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2645_);
lean_ctor_set(v_reuseFailAlloc_2653_, 1, v_snd_2638_);
v___x_2647_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
lean_object* v___x_2648_; size_t v___x_2649_; size_t v___x_2650_; lean_object* v___x_2651_; 
v___x_2648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2648_, 0, v_fst_2637_);
lean_ctor_set(v___x_2648_, 1, v___x_2647_);
v___x_2649_ = ((size_t)1ULL);
v___x_2650_ = lean_usize_add(v_i_2633_, v___x_2649_);
v___x_2651_ = lean_array_uset(v_bs_x27_2643_, v_i_2633_, v___x_2648_);
v_i_2633_ = v___x_2650_;
v_bs_2634_ = v___x_2651_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6___boxed(lean_object* v_sz_2655_, lean_object* v_i_2656_, lean_object* v_bs_2657_){
_start:
{
size_t v_sz_boxed_2658_; size_t v_i_boxed_2659_; lean_object* v_res_2660_; 
v_sz_boxed_2658_ = lean_unbox_usize(v_sz_2655_);
lean_dec(v_sz_2655_);
v_i_boxed_2659_ = lean_unbox_usize(v_i_2656_);
lean_dec(v_i_2656_);
v_res_2660_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(v_sz_boxed_2658_, v_i_boxed_2659_, v_bs_2657_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4___redArg(lean_object* v_inst_2661_, lean_object* v_declInfos_2662_, lean_object* v_k_2663_, uint8_t v_kind_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
size_t v_sz_2673_; size_t v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v_sz_2673_ = lean_array_size(v_declInfos_2662_);
v___x_2674_ = ((size_t)0ULL);
v___x_2675_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(v_sz_2673_, v___x_2674_, v_declInfos_2662_);
v___x_2676_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___redArg(v_inst_2661_, v___x_2675_, v_k_2663_, v_kind_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4___redArg___boxed(lean_object* v_inst_2677_, lean_object* v_declInfos_2678_, lean_object* v_k_2679_, lean_object* v_kind_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_){
_start:
{
uint8_t v_kind_boxed_2689_; lean_object* v_res_2690_; 
v_kind_boxed_2689_ = lean_unbox(v_kind_2680_);
v_res_2690_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4___redArg(v_inst_2677_, v_declInfos_2678_, v_k_2679_, v_kind_boxed_2689_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v_inst_2677_);
return v_res_2690_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0(uint8_t v___y_2698_, uint8_t v_suppressElabErrors_2699_, lean_object* v_x_2700_){
_start:
{
if (lean_obj_tag(v_x_2700_) == 1)
{
lean_object* v_pre_2701_; 
v_pre_2701_ = lean_ctor_get(v_x_2700_, 0);
switch(lean_obj_tag(v_pre_2701_))
{
case 1:
{
lean_object* v_pre_2702_; 
v_pre_2702_ = lean_ctor_get(v_pre_2701_, 0);
switch(lean_obj_tag(v_pre_2702_))
{
case 0:
{
lean_object* v_str_2703_; lean_object* v_str_2704_; lean_object* v___x_2705_; uint8_t v___x_2706_; 
v_str_2703_ = lean_ctor_get(v_x_2700_, 1);
v_str_2704_ = lean_ctor_get(v_pre_2701_, 1);
v___x_2705_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65));
v___x_2706_ = lean_string_dec_eq(v_str_2704_, v___x_2705_);
if (v___x_2706_ == 0)
{
lean_object* v___x_2707_; uint8_t v___x_2708_; 
v___x_2707_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__0));
v___x_2708_ = lean_string_dec_eq(v_str_2704_, v___x_2707_);
if (v___x_2708_ == 0)
{
return v___y_2698_;
}
else
{
lean_object* v___x_2709_; uint8_t v___x_2710_; 
v___x_2709_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__1));
v___x_2710_ = lean_string_dec_eq(v_str_2703_, v___x_2709_);
if (v___x_2710_ == 0)
{
return v___y_2698_;
}
else
{
return v_suppressElabErrors_2699_;
}
}
}
else
{
lean_object* v___x_2711_; uint8_t v___x_2712_; 
v___x_2711_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__2));
v___x_2712_ = lean_string_dec_eq(v_str_2703_, v___x_2711_);
if (v___x_2712_ == 0)
{
return v___y_2698_;
}
else
{
return v_suppressElabErrors_2699_;
}
}
}
case 1:
{
lean_object* v_pre_2713_; 
v_pre_2713_ = lean_ctor_get(v_pre_2702_, 0);
if (lean_obj_tag(v_pre_2713_) == 0)
{
lean_object* v_str_2714_; lean_object* v_str_2715_; lean_object* v_str_2716_; lean_object* v___x_2717_; uint8_t v___x_2718_; 
v_str_2714_ = lean_ctor_get(v_x_2700_, 1);
v_str_2715_ = lean_ctor_get(v_pre_2701_, 1);
v_str_2716_ = lean_ctor_get(v_pre_2702_, 1);
v___x_2717_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__3));
v___x_2718_ = lean_string_dec_eq(v_str_2716_, v___x_2717_);
if (v___x_2718_ == 0)
{
return v___y_2698_;
}
else
{
lean_object* v___x_2719_; uint8_t v___x_2720_; 
v___x_2719_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__4));
v___x_2720_ = lean_string_dec_eq(v_str_2715_, v___x_2719_);
if (v___x_2720_ == 0)
{
return v___y_2698_;
}
else
{
lean_object* v___x_2721_; uint8_t v___x_2722_; 
v___x_2721_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__5));
v___x_2722_ = lean_string_dec_eq(v_str_2714_, v___x_2721_);
if (v___x_2722_ == 0)
{
return v___y_2698_;
}
else
{
return v_suppressElabErrors_2699_;
}
}
}
}
else
{
return v___y_2698_;
}
}
default: 
{
return v___y_2698_;
}
}
}
case 0:
{
lean_object* v_str_2723_; lean_object* v___x_2724_; uint8_t v___x_2725_; 
v_str_2723_ = lean_ctor_get(v_x_2700_, 1);
v___x_2724_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__6));
v___x_2725_ = lean_string_dec_eq(v_str_2723_, v___x_2724_);
if (v___x_2725_ == 0)
{
return v___y_2698_;
}
else
{
return v_suppressElabErrors_2699_;
}
}
default: 
{
return v___y_2698_;
}
}
}
else
{
return v___y_2698_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___boxed(lean_object* v___y_2726_, lean_object* v_suppressElabErrors_2727_, lean_object* v_x_2728_){
_start:
{
uint8_t v___y_79827__boxed_2729_; uint8_t v_suppressElabErrors_boxed_2730_; uint8_t v_res_2731_; lean_object* v_r_2732_; 
v___y_79827__boxed_2729_ = lean_unbox(v___y_2726_);
v_suppressElabErrors_boxed_2730_ = lean_unbox(v_suppressElabErrors_2727_);
v_res_2731_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0(v___y_79827__boxed_2729_, v_suppressElabErrors_boxed_2730_, v_x_2728_);
lean_dec(v_x_2728_);
v_r_2732_ = lean_box(v_res_2731_);
return v_r_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg(lean_object* v_ref_2733_, lean_object* v_msgData_2734_, uint8_t v_severity_2735_, uint8_t v_isSilent_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v___y_2743_; uint8_t v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; uint8_t v___y_2749_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2779_; uint8_t v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; uint8_t v___y_2784_; uint8_t v___y_2785_; lean_object* v___y_2786_; lean_object* v___y_2804_; lean_object* v___y_2805_; uint8_t v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; uint8_t v___y_2809_; uint8_t v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2815_; uint8_t v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; uint8_t v___y_2819_; lean_object* v___y_2820_; uint8_t v___y_2821_; uint8_t v___x_2826_; lean_object* v___y_2828_; uint8_t v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; uint8_t v___y_2833_; uint8_t v___y_2834_; uint8_t v___y_2836_; uint8_t v___x_2851_; 
v___x_2826_ = 2;
v___x_2851_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2735_, v___x_2826_);
if (v___x_2851_ == 0)
{
v___y_2836_ = v___x_2851_;
goto v___jp_2835_;
}
else
{
uint8_t v___x_2852_; 
lean_inc_ref(v_msgData_2734_);
v___x_2852_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2734_);
v___y_2836_ = v___x_2852_;
goto v___jp_2835_;
}
v___jp_2742_:
{
lean_object* v___x_2752_; lean_object* v_currNamespace_2753_; lean_object* v_openDecls_2754_; lean_object* v_env_2755_; lean_object* v_nextMacroScope_2756_; lean_object* v_ngen_2757_; lean_object* v_auxDeclNGen_2758_; lean_object* v_traceState_2759_; lean_object* v_cache_2760_; lean_object* v_messages_2761_; lean_object* v_infoState_2762_; lean_object* v_snapshotTasks_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2777_; 
v___x_2752_ = lean_st_ref_take(v___y_2751_);
v_currNamespace_2753_ = lean_ctor_get(v___y_2750_, 6);
v_openDecls_2754_ = lean_ctor_get(v___y_2750_, 7);
v_env_2755_ = lean_ctor_get(v___x_2752_, 0);
v_nextMacroScope_2756_ = lean_ctor_get(v___x_2752_, 1);
v_ngen_2757_ = lean_ctor_get(v___x_2752_, 2);
v_auxDeclNGen_2758_ = lean_ctor_get(v___x_2752_, 3);
v_traceState_2759_ = lean_ctor_get(v___x_2752_, 4);
v_cache_2760_ = lean_ctor_get(v___x_2752_, 5);
v_messages_2761_ = lean_ctor_get(v___x_2752_, 6);
v_infoState_2762_ = lean_ctor_get(v___x_2752_, 7);
v_snapshotTasks_2763_ = lean_ctor_get(v___x_2752_, 8);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2765_ = v___x_2752_;
v_isShared_2766_ = v_isSharedCheck_2777_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_snapshotTasks_2763_);
lean_inc(v_infoState_2762_);
lean_inc(v_messages_2761_);
lean_inc(v_cache_2760_);
lean_inc(v_traceState_2759_);
lean_inc(v_auxDeclNGen_2758_);
lean_inc(v_ngen_2757_);
lean_inc(v_nextMacroScope_2756_);
lean_inc(v_env_2755_);
lean_dec(v___x_2752_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2777_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2772_; 
lean_inc(v_openDecls_2754_);
lean_inc(v_currNamespace_2753_);
v___x_2767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2767_, 0, v_currNamespace_2753_);
lean_ctor_set(v___x_2767_, 1, v_openDecls_2754_);
v___x_2768_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2767_);
lean_ctor_set(v___x_2768_, 1, v___y_2748_);
lean_inc_ref(v___y_2743_);
v___x_2769_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2769_, 0, v___y_2743_);
lean_ctor_set(v___x_2769_, 1, v___y_2746_);
lean_ctor_set(v___x_2769_, 2, v___y_2747_);
lean_ctor_set(v___x_2769_, 3, v___y_2745_);
lean_ctor_set(v___x_2769_, 4, v___x_2768_);
lean_ctor_set_uint8(v___x_2769_, sizeof(void*)*5, v___y_2744_);
lean_ctor_set_uint8(v___x_2769_, sizeof(void*)*5 + 1, v___y_2749_);
lean_ctor_set_uint8(v___x_2769_, sizeof(void*)*5 + 2, v_isSilent_2736_);
v___x_2770_ = l_Lean_MessageLog_add(v___x_2769_, v_messages_2761_);
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 6, v___x_2770_);
v___x_2772_ = v___x_2765_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_env_2755_);
lean_ctor_set(v_reuseFailAlloc_2776_, 1, v_nextMacroScope_2756_);
lean_ctor_set(v_reuseFailAlloc_2776_, 2, v_ngen_2757_);
lean_ctor_set(v_reuseFailAlloc_2776_, 3, v_auxDeclNGen_2758_);
lean_ctor_set(v_reuseFailAlloc_2776_, 4, v_traceState_2759_);
lean_ctor_set(v_reuseFailAlloc_2776_, 5, v_cache_2760_);
lean_ctor_set(v_reuseFailAlloc_2776_, 6, v___x_2770_);
lean_ctor_set(v_reuseFailAlloc_2776_, 7, v_infoState_2762_);
lean_ctor_set(v_reuseFailAlloc_2776_, 8, v_snapshotTasks_2763_);
v___x_2772_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2773_ = lean_st_ref_set(v___y_2751_, v___x_2772_);
v___x_2774_ = lean_box(0);
v___x_2775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2774_);
return v___x_2775_;
}
}
}
v___jp_2778_:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2802_; 
v___x_2787_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2734_);
v___x_2788_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(v___x_2787_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2791_ = v___x_2788_;
v_isShared_2792_ = v_isSharedCheck_2802_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2788_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2802_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
lean_inc_ref(v___y_2782_);
v___x_2793_ = l_Lean_FileMap_toPosition(v___y_2782_, v___y_2783_);
lean_dec(v___y_2783_);
lean_inc_ref(v___y_2782_);
v___x_2794_ = l_Lean_FileMap_toPosition(v___y_2782_, v___y_2786_);
lean_dec(v___y_2786_);
v___x_2795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2794_);
v___x_2796_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__63));
if (v___y_2780_ == 0)
{
lean_del_object(v___x_2791_);
lean_dec_ref(v___y_2779_);
v___y_2743_ = v___y_2781_;
v___y_2744_ = v___y_2784_;
v___y_2745_ = v___x_2796_;
v___y_2746_ = v___x_2793_;
v___y_2747_ = v___x_2795_;
v___y_2748_ = v_a_2789_;
v___y_2749_ = v___y_2785_;
v___y_2750_ = v___y_2739_;
v___y_2751_ = v___y_2740_;
goto v___jp_2742_;
}
else
{
uint8_t v___x_2797_; 
lean_inc(v_a_2789_);
v___x_2797_ = l_Lean_MessageData_hasTag(v___y_2779_, v_a_2789_);
if (v___x_2797_ == 0)
{
lean_object* v___x_2798_; lean_object* v___x_2800_; 
lean_dec_ref(v___x_2795_);
lean_dec_ref(v___x_2793_);
lean_dec(v_a_2789_);
v___x_2798_ = lean_box(0);
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 0, v___x_2798_);
v___x_2800_ = v___x_2791_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2798_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
else
{
lean_del_object(v___x_2791_);
v___y_2743_ = v___y_2781_;
v___y_2744_ = v___y_2784_;
v___y_2745_ = v___x_2796_;
v___y_2746_ = v___x_2793_;
v___y_2747_ = v___x_2795_;
v___y_2748_ = v_a_2789_;
v___y_2749_ = v___y_2785_;
v___y_2750_ = v___y_2739_;
v___y_2751_ = v___y_2740_;
goto v___jp_2742_;
}
}
}
}
v___jp_2803_:
{
lean_object* v___x_2812_; 
v___x_2812_ = l_Lean_Syntax_getTailPos_x3f(v___y_2807_, v___y_2809_);
lean_dec(v___y_2807_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_inc(v___y_2811_);
v___y_2779_ = v___y_2804_;
v___y_2780_ = v___y_2806_;
v___y_2781_ = v___y_2805_;
v___y_2782_ = v___y_2808_;
v___y_2783_ = v___y_2811_;
v___y_2784_ = v___y_2809_;
v___y_2785_ = v___y_2810_;
v___y_2786_ = v___y_2811_;
goto v___jp_2778_;
}
else
{
lean_object* v_val_2813_; 
v_val_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_val_2813_);
lean_dec_ref(v___x_2812_);
v___y_2779_ = v___y_2804_;
v___y_2780_ = v___y_2806_;
v___y_2781_ = v___y_2805_;
v___y_2782_ = v___y_2808_;
v___y_2783_ = v___y_2811_;
v___y_2784_ = v___y_2809_;
v___y_2785_ = v___y_2810_;
v___y_2786_ = v_val_2813_;
goto v___jp_2778_;
}
}
v___jp_2814_:
{
lean_object* v_ref_2822_; lean_object* v___x_2823_; 
v_ref_2822_ = l_Lean_replaceRef(v_ref_2733_, v___y_2820_);
v___x_2823_ = l_Lean_Syntax_getPos_x3f(v_ref_2822_, v___y_2819_);
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v___x_2824_; 
v___x_2824_ = lean_unsigned_to_nat(0u);
v___y_2804_ = v___y_2815_;
v___y_2805_ = v___y_2817_;
v___y_2806_ = v___y_2816_;
v___y_2807_ = v_ref_2822_;
v___y_2808_ = v___y_2818_;
v___y_2809_ = v___y_2819_;
v___y_2810_ = v___y_2821_;
v___y_2811_ = v___x_2824_;
goto v___jp_2803_;
}
else
{
lean_object* v_val_2825_; 
v_val_2825_ = lean_ctor_get(v___x_2823_, 0);
lean_inc(v_val_2825_);
lean_dec_ref(v___x_2823_);
v___y_2804_ = v___y_2815_;
v___y_2805_ = v___y_2817_;
v___y_2806_ = v___y_2816_;
v___y_2807_ = v_ref_2822_;
v___y_2808_ = v___y_2818_;
v___y_2809_ = v___y_2819_;
v___y_2810_ = v___y_2821_;
v___y_2811_ = v_val_2825_;
goto v___jp_2803_;
}
}
v___jp_2827_:
{
if (v___y_2834_ == 0)
{
v___y_2815_ = v___y_2831_;
v___y_2816_ = v___y_2829_;
v___y_2817_ = v___y_2828_;
v___y_2818_ = v___y_2830_;
v___y_2819_ = v___y_2833_;
v___y_2820_ = v___y_2832_;
v___y_2821_ = v_severity_2735_;
goto v___jp_2814_;
}
else
{
v___y_2815_ = v___y_2831_;
v___y_2816_ = v___y_2829_;
v___y_2817_ = v___y_2828_;
v___y_2818_ = v___y_2830_;
v___y_2819_ = v___y_2833_;
v___y_2820_ = v___y_2832_;
v___y_2821_ = v___x_2826_;
goto v___jp_2814_;
}
}
v___jp_2835_:
{
if (v___y_2836_ == 0)
{
lean_object* v_fileName_2837_; lean_object* v_fileMap_2838_; lean_object* v_options_2839_; lean_object* v_ref_2840_; uint8_t v_suppressElabErrors_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___f_2844_; uint8_t v___x_2845_; uint8_t v___x_2846_; 
v_fileName_2837_ = lean_ctor_get(v___y_2739_, 0);
v_fileMap_2838_ = lean_ctor_get(v___y_2739_, 1);
v_options_2839_ = lean_ctor_get(v___y_2739_, 2);
v_ref_2840_ = lean_ctor_get(v___y_2739_, 5);
v_suppressElabErrors_2841_ = lean_ctor_get_uint8(v___y_2739_, sizeof(void*)*14 + 1);
v___x_2842_ = lean_box(v___y_2836_);
v___x_2843_ = lean_box(v_suppressElabErrors_2841_);
v___f_2844_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2844_, 0, v___x_2842_);
lean_closure_set(v___f_2844_, 1, v___x_2843_);
v___x_2845_ = 1;
v___x_2846_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2735_, v___x_2845_);
if (v___x_2846_ == 0)
{
v___y_2828_ = v_fileName_2837_;
v___y_2829_ = v_suppressElabErrors_2841_;
v___y_2830_ = v_fileMap_2838_;
v___y_2831_ = v___f_2844_;
v___y_2832_ = v_ref_2840_;
v___y_2833_ = v___y_2836_;
v___y_2834_ = v___x_2846_;
goto v___jp_2827_;
}
else
{
lean_object* v___x_2847_; uint8_t v___x_2848_; 
v___x_2847_ = l_Lean_warningAsError;
v___x_2848_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5(v_options_2839_, v___x_2847_);
v___y_2828_ = v_fileName_2837_;
v___y_2829_ = v_suppressElabErrors_2841_;
v___y_2830_ = v_fileMap_2838_;
v___y_2831_ = v___f_2844_;
v___y_2832_ = v_ref_2840_;
v___y_2833_ = v___y_2836_;
v___y_2834_ = v___x_2848_;
goto v___jp_2827_;
}
}
else
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
lean_dec_ref(v_msgData_2734_);
v___x_2849_ = lean_box(0);
v___x_2850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2849_);
return v___x_2850_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___boxed(lean_object* v_ref_2853_, lean_object* v_msgData_2854_, lean_object* v_severity_2855_, lean_object* v_isSilent_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
uint8_t v_severity_boxed_2862_; uint8_t v_isSilent_boxed_2863_; lean_object* v_res_2864_; 
v_severity_boxed_2862_ = lean_unbox(v_severity_2855_);
v_isSilent_boxed_2863_ = lean_unbox(v_isSilent_2856_);
v_res_2864_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg(v_ref_2853_, v_msgData_2854_, v_severity_boxed_2862_, v_isSilent_boxed_2863_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
lean_dec(v___y_2858_);
lean_dec_ref(v___y_2857_);
lean_dec(v_ref_2853_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10(lean_object* v_msgData_2865_, uint8_t v_severity_2866_, uint8_t v_isSilent_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
lean_object* v_ref_2876_; lean_object* v___x_2877_; 
v_ref_2876_ = lean_ctor_get(v___y_2873_, 5);
v___x_2877_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg(v_ref_2876_, v_msgData_2865_, v_severity_2866_, v_isSilent_2867_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10___boxed(lean_object* v_msgData_2878_, lean_object* v_severity_2879_, lean_object* v_isSilent_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
uint8_t v_severity_boxed_2889_; uint8_t v_isSilent_boxed_2890_; lean_object* v_res_2891_; 
v_severity_boxed_2889_ = lean_unbox(v_severity_2879_);
v_isSilent_boxed_2890_ = lean_unbox(v_isSilent_2880_);
v_res_2891_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10(v_msgData_2878_, v_severity_boxed_2889_, v_isSilent_boxed_2890_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
lean_dec_ref(v___y_2881_);
return v_res_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6(lean_object* v_msgData_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_){
_start:
{
uint8_t v___x_2901_; uint8_t v___x_2902_; lean_object* v___x_2903_; 
v___x_2901_ = 2;
v___x_2902_ = 0;
v___x_2903_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10(v_msgData_2892_, v___x_2901_, v___x_2902_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6___boxed(lean_object* v_msgData_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6(v_msgData_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec_ref(v___y_2905_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__8(lean_object* v_a_2914_, lean_object* v_as_2915_, size_t v_i_2916_, size_t v_stop_2917_, lean_object* v_b_2918_){
_start:
{
lean_object* v___y_2920_; uint8_t v___x_2924_; 
v___x_2924_ = lean_usize_dec_eq(v_i_2916_, v_stop_2917_);
if (v___x_2924_ == 0)
{
lean_object* v_reassigns_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; uint8_t v___x_2928_; 
v_reassigns_2925_ = lean_ctor_get(v_a_2914_, 1);
v___x_2926_ = lean_array_uget_borrowed(v_as_2915_, v_i_2916_);
v___x_2927_ = l_Lean_TSyntax_getId(v___x_2926_);
v___x_2928_ = l_Lean_NameSet_contains(v_reassigns_2925_, v___x_2927_);
lean_dec(v___x_2927_);
if (v___x_2928_ == 0)
{
v___y_2920_ = v_b_2918_;
goto v___jp_2919_;
}
else
{
lean_object* v___x_2929_; 
lean_inc(v___x_2926_);
v___x_2929_ = lean_array_push(v_b_2918_, v___x_2926_);
v___y_2920_ = v___x_2929_;
goto v___jp_2919_;
}
}
else
{
return v_b_2918_;
}
v___jp_2919_:
{
size_t v___x_2921_; size_t v___x_2922_; 
v___x_2921_ = ((size_t)1ULL);
v___x_2922_ = lean_usize_add(v_i_2916_, v___x_2921_);
v_i_2916_ = v___x_2922_;
v_b_2918_ = v___y_2920_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__8___boxed(lean_object* v_a_2930_, lean_object* v_as_2931_, lean_object* v_i_2932_, lean_object* v_stop_2933_, lean_object* v_b_2934_){
_start:
{
size_t v_i_boxed_2935_; size_t v_stop_boxed_2936_; lean_object* v_res_2937_; 
v_i_boxed_2935_ = lean_unbox_usize(v_i_2932_);
lean_dec(v_i_2932_);
v_stop_boxed_2936_ = lean_unbox_usize(v_stop_2933_);
lean_dec(v_stop_2933_);
v_res_2937_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__8(v_a_2930_, v_as_2931_, v_i_boxed_2935_, v_stop_boxed_2936_, v_b_2934_);
lean_dec_ref(v_as_2931_);
lean_dec_ref(v_a_2930_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__7(size_t v_sz_2938_, size_t v_i_2939_, lean_object* v_bs_2940_){
_start:
{
uint8_t v___x_2941_; 
v___x_2941_ = lean_usize_dec_lt(v_i_2939_, v_sz_2938_);
if (v___x_2941_ == 0)
{
return v_bs_2940_;
}
else
{
lean_object* v_v_2942_; lean_object* v___x_2943_; lean_object* v_bs_x27_2944_; lean_object* v___x_2945_; size_t v___x_2946_; size_t v___x_2947_; lean_object* v___x_2948_; 
v_v_2942_ = lean_array_uget(v_bs_2940_, v_i_2939_);
v___x_2943_ = lean_unsigned_to_nat(0u);
v_bs_x27_2944_ = lean_array_uset(v_bs_2940_, v_i_2939_, v___x_2943_);
v___x_2945_ = l_Lean_TSyntax_getId(v_v_2942_);
lean_dec(v_v_2942_);
v___x_2946_ = ((size_t)1ULL);
v___x_2947_ = lean_usize_add(v_i_2939_, v___x_2946_);
v___x_2948_ = lean_array_uset(v_bs_x27_2944_, v_i_2939_, v___x_2945_);
v_i_2939_ = v___x_2947_;
v_bs_2940_ = v___x_2948_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__7___boxed(lean_object* v_sz_2950_, lean_object* v_i_2951_, lean_object* v_bs_2952_){
_start:
{
size_t v_sz_boxed_2953_; size_t v_i_boxed_2954_; lean_object* v_res_2955_; 
v_sz_boxed_2953_ = lean_unbox_usize(v_sz_2950_);
lean_dec(v_sz_2950_);
v_i_boxed_2954_ = lean_unbox_usize(v_i_2951_);
lean_dec(v_i_2951_);
v_res_2955_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__7(v_sz_boxed_2953_, v_i_boxed_2954_, v_bs_2952_);
return v_res_2955_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___closed__12(void){
_start:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2976_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__11));
v___x_2977_ = l_Lean_stringToMessageData(v___x_2976_);
return v___x_2977_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___closed__14(void){
_start:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2979_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__13));
v___x_2980_ = l_Lean_stringToMessageData(v___x_2979_);
return v___x_2980_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___closed__16(void){
_start:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2982_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__15));
v___x_2983_ = l_Lean_stringToMessageData(v___x_2982_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor(lean_object* v_stx_2993_, lean_object* v_dec_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_){
_start:
{
lean_object* v___x_3003_; uint8_t v___x_3004_; 
v___x_3003_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
lean_inc(v_stx_2993_);
v___x_3004_ = l_Lean_Syntax_isOfKind(v_stx_2993_, v___x_3003_);
if (v___x_3004_ == 0)
{
lean_object* v___x_3005_; 
lean_dec_ref(v_dec_2994_);
lean_dec(v_stx_2993_);
v___x_3005_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_3005_;
}
else
{
lean_object* v___x_3006_; lean_object* v___x_3007_; uint8_t v___x_3008_; 
v___x_3006_ = lean_unsigned_to_nat(1u);
v___x_3007_ = l_Lean_Syntax_getArg(v_stx_2993_, v___x_3006_);
lean_inc(v___x_3007_);
v___x_3008_ = l_Lean_Syntax_matchesNull(v___x_3007_, v___x_3006_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3009_; 
lean_dec(v___x_3007_);
lean_dec_ref(v_dec_2994_);
lean_dec(v_stx_2993_);
v___x_3009_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_3009_;
}
else
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; uint8_t v___x_3013_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; uint8_t v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; uint8_t v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v_fst_3072_; lean_object* v_snd_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; uint8_t v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; uint8_t v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; uint8_t v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; uint8_t v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3292_; lean_object* v___y_3293_; uint8_t v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; uint8_t v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___y_3311_; lean_object* v___y_3312_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v_h_x3f_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; 
v___x_3010_ = lean_unsigned_to_nat(0u);
v___x_3011_ = l_Lean_Syntax_getArg(v___x_3007_, v___x_3010_);
lean_dec(v___x_3007_);
v___x_3012_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
lean_inc(v___x_3011_);
v___x_3013_ = l_Lean_Syntax_isOfKind(v___x_3011_, v___x_3012_);
if (v___x_3013_ == 0)
{
lean_object* v___x_3459_; 
lean_dec(v___x_3011_);
lean_dec_ref(v_dec_2994_);
lean_dec(v_stx_2993_);
v___x_3459_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_3459_;
}
else
{
lean_object* v___x_3460_; uint8_t v___x_3461_; 
v___x_3460_ = l_Lean_Syntax_getArg(v___x_3011_, v___x_3010_);
v___x_3461_ = l_Lean_Syntax_isNone(v___x_3460_);
if (v___x_3461_ == 0)
{
lean_object* v___x_3462_; uint8_t v___x_3463_; 
v___x_3462_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3460_);
v___x_3463_ = l_Lean_Syntax_matchesNull(v___x_3460_, v___x_3462_);
if (v___x_3463_ == 0)
{
lean_object* v___x_3464_; 
lean_dec(v___x_3460_);
lean_dec(v___x_3011_);
lean_dec_ref(v_dec_2994_);
lean_dec(v_stx_2993_);
v___x_3464_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_3464_;
}
else
{
lean_object* v_h_x3f_3465_; lean_object* v___x_3466_; 
v_h_x3f_3465_ = l_Lean_Syntax_getArg(v___x_3460_, v___x_3010_);
lean_dec(v___x_3460_);
v___x_3466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3466_, 0, v_h_x3f_3465_);
v_h_x3f_3337_ = v___x_3466_;
v___y_3338_ = v_a_2995_;
v___y_3339_ = v_a_2996_;
v___y_3340_ = v_a_2997_;
v___y_3341_ = v_a_2998_;
v___y_3342_ = v_a_2999_;
v___y_3343_ = v_a_3000_;
v___y_3344_ = v_a_3001_;
goto v___jp_3336_;
}
}
else
{
lean_object* v___x_3467_; 
lean_dec(v___x_3460_);
v___x_3467_ = lean_box(0);
v_h_x3f_3337_ = v___x_3467_;
v___y_3338_ = v_a_2995_;
v___y_3339_ = v_a_2996_;
v___y_3340_ = v_a_2997_;
v___y_3341_ = v_a_2998_;
v___y_3342_ = v_a_2999_;
v___y_3343_ = v_a_3000_;
v___y_3344_ = v_a_3001_;
goto v___jp_3336_;
}
}
v___jp_3014_:
{
lean_object* v___x_3035_; uint8_t v___x_3036_; lean_object* v___x_3037_; 
v___x_3035_ = l_Lean_instInhabitedExpr;
v___x_3036_ = 0;
v___x_3037_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4___redArg(v___x_3035_, v___y_3034_, v___y_3019_, v___x_3036_, v___y_3031_, v___y_3030_, v___y_3028_, v___y_3033_, v___y_3027_, v___y_3032_, v___y_3025_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_object* v_a_3038_; lean_object* v_doBlockResultType_3039_; lean_object* v___x_3040_; lean_object* v___y_3041_; lean_object* v___x_3042_; lean_object* v___f_3043_; lean_object* v___x_3044_; 
v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
lean_inc(v_a_3038_);
lean_dec_ref(v___x_3037_);
v_doBlockResultType_3039_ = lean_ctor_get(v___y_3031_, 3);
lean_inc_ref(v_doBlockResultType_3039_);
v___x_3040_ = lean_box(v___y_3024_);
lean_inc_ref(v_doBlockResultType_3039_);
v___y_3041_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__10___boxed), 19, 11);
lean_closure_set(v___y_3041_, 0, v___x_3040_);
lean_closure_set(v___y_3041_, 1, v_dec_2994_);
lean_closure_set(v___y_3041_, 2, v___y_3022_);
lean_closure_set(v___y_3041_, 3, v_doBlockResultType_3039_);
lean_closure_set(v___y_3041_, 4, v___y_3017_);
lean_closure_set(v___y_3041_, 5, v___y_3016_);
lean_closure_set(v___y_3041_, 6, v___y_3020_);
lean_closure_set(v___y_3041_, 7, v___y_3023_);
lean_closure_set(v___y_3041_, 8, v___y_3015_);
lean_closure_set(v___y_3041_, 9, v___x_3010_);
lean_closure_set(v___y_3041_, 10, v___x_3006_);
v___x_3042_ = lean_box(v___x_3013_);
v___f_3043_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__11___boxed), 13, 4);
lean_closure_set(v___f_3043_, 0, v___y_3018_);
lean_closure_set(v___f_3043_, 1, v___y_3041_);
lean_closure_set(v___f_3043_, 2, v___x_3006_);
lean_closure_set(v___f_3043_, 3, v___x_3042_);
lean_inc_ref(v___y_3026_);
v___x_3044_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(v___y_3021_, v___y_3026_, v___f_3043_, v___y_3031_, v___y_3030_, v___y_3028_, v___y_3033_, v___y_3027_, v___y_3032_, v___y_3025_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
lean_inc(v_a_3045_);
lean_dec_ref(v___x_3044_);
v___x_3046_ = l_Lean_Expr_app___override(v___y_3029_, v_a_3038_);
v___x_3047_ = l_Lean_Elab_Do_mkBindApp(v___y_3026_, v_doBlockResultType_3039_, v___x_3046_, v_a_3045_, v___y_3031_, v___y_3030_, v___y_3028_, v___y_3033_, v___y_3027_, v___y_3032_, v___y_3025_);
return v___x_3047_;
}
else
{
lean_dec_ref(v_doBlockResultType_3039_);
lean_dec(v_a_3038_);
lean_dec_ref(v___y_3031_);
lean_dec_ref(v___y_3029_);
lean_dec_ref(v___y_3026_);
return v___x_3044_;
}
}
else
{
lean_dec_ref(v___y_3031_);
lean_dec_ref(v___y_3029_);
lean_dec_ref(v___y_3026_);
lean_dec_ref(v___y_3023_);
lean_dec(v___y_3022_);
lean_dec(v___y_3021_);
lean_dec(v___y_3020_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec_ref(v_dec_2994_);
return v___x_3037_;
}
}
v___jp_3048_:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3081_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17));
v___x_3082_ = l_Lean_Core_mkFreshUserName(v___x_3081_, v___y_3079_, v___y_3080_);
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_object* v_a_3083_; lean_object* v___x_3084_; lean_object* v___f_3085_; 
v_a_3083_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_a_3083_);
lean_dec_ref(v___x_3082_);
v___x_3084_ = lean_box(v___x_3013_);
lean_inc(v_a_3083_);
lean_inc(v___y_3064_);
lean_inc_ref(v___y_3052_);
lean_inc(v___y_3051_);
lean_inc_ref(v___y_3061_);
v___f_3085_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__9___boxed), 20, 11);
lean_closure_set(v___f_3085_, 0, v___y_3061_);
lean_closure_set(v___f_3085_, 1, v___y_3051_);
lean_closure_set(v___f_3085_, 2, v___y_3052_);
lean_closure_set(v___f_3085_, 3, v___y_3067_);
lean_closure_set(v___f_3085_, 4, v___y_3062_);
lean_closure_set(v___f_3085_, 5, v___y_3053_);
lean_closure_set(v___f_3085_, 6, v___y_3065_);
lean_closure_set(v___f_3085_, 7, v___y_3055_);
lean_closure_set(v___f_3085_, 8, v___x_3084_);
lean_closure_set(v___f_3085_, 9, v___y_3064_);
lean_closure_set(v___f_3085_, 10, v_a_3083_);
if (lean_obj_tag(v___y_3068_) == 1)
{
if (lean_obj_tag(v_snd_3073_) == 1)
{
lean_object* v_val_3086_; lean_object* v_val_3087_; lean_object* v___f_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
lean_dec_ref(v___y_3069_);
v_val_3086_ = lean_ctor_get(v___y_3068_, 0);
lean_inc(v_val_3086_);
lean_dec_ref(v___y_3068_);
v_val_3087_ = lean_ctor_get(v_snd_3073_, 0);
lean_inc(v_val_3087_);
lean_dec_ref(v_snd_3073_);
v___f_3088_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__12___boxed), 16, 7);
lean_closure_set(v___f_3088_, 0, v___y_3060_);
lean_closure_set(v___f_3088_, 1, v___y_3057_);
lean_closure_set(v___f_3088_, 2, v___x_3010_);
lean_closure_set(v___f_3088_, 3, v___y_3049_);
lean_closure_set(v___f_3088_, 4, v___y_3054_);
lean_closure_set(v___f_3088_, 5, v_val_3087_);
lean_closure_set(v___f_3088_, 6, v___y_3056_);
v___x_3089_ = l_Lean_TSyntax_getId(v___y_3070_);
lean_dec(v___y_3070_);
v___x_3090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3089_);
lean_ctor_set(v___x_3090_, 1, v___y_3071_);
v___x_3091_ = l_Lean_TSyntax_getId(v_val_3086_);
lean_dec(v_val_3086_);
v___x_3092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3091_);
lean_ctor_set(v___x_3092_, 1, v___f_3088_);
v___x_3093_ = lean_unsigned_to_nat(2u);
v___x_3094_ = lean_mk_empty_array_with_capacity(v___x_3093_);
v___x_3095_ = lean_array_push(v___x_3094_, v___x_3090_);
v___x_3096_ = lean_array_push(v___x_3095_, v___x_3092_);
lean_inc_ref(v___y_3074_);
v___y_3015_ = v___y_3063_;
v___y_3016_ = v___y_3050_;
v___y_3017_ = v___y_3061_;
v___y_3018_ = v___y_3064_;
v___y_3019_ = v___f_3085_;
v___y_3020_ = v___y_3051_;
v___y_3021_ = v_a_3083_;
v___y_3022_ = v___y_3066_;
v___y_3023_ = v___y_3059_;
v___y_3024_ = v___y_3058_;
v___y_3025_ = v___y_3080_;
v___y_3026_ = v___y_3052_;
v___y_3027_ = v___y_3078_;
v___y_3028_ = v___y_3076_;
v___y_3029_ = v_fst_3072_;
v___y_3030_ = v___y_3075_;
v___y_3031_ = v___y_3074_;
v___y_3032_ = v___y_3079_;
v___y_3033_ = v___y_3077_;
v___y_3034_ = v___x_3096_;
goto v___jp_3014_;
}
else
{
lean_object* v___x_3097_; 
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec(v___y_3060_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec_ref(v___y_3054_);
lean_dec_ref(v___y_3049_);
v___x_3097_ = lean_apply_2(v___y_3069_, v___y_3068_, v_snd_3073_);
lean_inc_ref(v___y_3074_);
v___y_3015_ = v___y_3063_;
v___y_3016_ = v___y_3050_;
v___y_3017_ = v___y_3061_;
v___y_3018_ = v___y_3064_;
v___y_3019_ = v___f_3085_;
v___y_3020_ = v___y_3051_;
v___y_3021_ = v_a_3083_;
v___y_3022_ = v___y_3066_;
v___y_3023_ = v___y_3059_;
v___y_3024_ = v___y_3058_;
v___y_3025_ = v___y_3080_;
v___y_3026_ = v___y_3052_;
v___y_3027_ = v___y_3078_;
v___y_3028_ = v___y_3076_;
v___y_3029_ = v_fst_3072_;
v___y_3030_ = v___y_3075_;
v___y_3031_ = v___y_3074_;
v___y_3032_ = v___y_3079_;
v___y_3033_ = v___y_3077_;
v___y_3034_ = v___x_3097_;
goto v___jp_3014_;
}
}
else
{
lean_object* v___x_3098_; 
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec(v___y_3060_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec_ref(v___y_3054_);
lean_dec_ref(v___y_3049_);
v___x_3098_ = lean_apply_2(v___y_3069_, v___y_3068_, v_snd_3073_);
lean_inc_ref(v___y_3074_);
v___y_3015_ = v___y_3063_;
v___y_3016_ = v___y_3050_;
v___y_3017_ = v___y_3061_;
v___y_3018_ = v___y_3064_;
v___y_3019_ = v___f_3085_;
v___y_3020_ = v___y_3051_;
v___y_3021_ = v_a_3083_;
v___y_3022_ = v___y_3066_;
v___y_3023_ = v___y_3059_;
v___y_3024_ = v___y_3058_;
v___y_3025_ = v___y_3080_;
v___y_3026_ = v___y_3052_;
v___y_3027_ = v___y_3078_;
v___y_3028_ = v___y_3076_;
v___y_3029_ = v_fst_3072_;
v___y_3030_ = v___y_3075_;
v___y_3031_ = v___y_3074_;
v___y_3032_ = v___y_3079_;
v___y_3033_ = v___y_3077_;
v___y_3034_ = v___x_3098_;
goto v___jp_3014_;
}
}
else
{
lean_object* v_a_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3106_; 
lean_dec(v_snd_3073_);
lean_dec_ref(v_fst_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec(v___y_3055_);
lean_dec_ref(v___y_3054_);
lean_dec(v___y_3053_);
lean_dec_ref(v___y_3052_);
lean_dec(v___y_3051_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
lean_dec_ref(v_dec_2994_);
v_a_3099_ = lean_ctor_get(v___x_3082_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3101_ = v___x_3082_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_a_3099_);
lean_dec(v___x_3082_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3104_; 
if (v_isShared_3102_ == 0)
{
v___x_3104_ = v___x_3101_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_a_3099_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
}
v___jp_3107_:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3142_ = lean_box(0);
lean_inc(v___y_3141_);
lean_inc_ref(v___y_3140_);
lean_inc(v___y_3139_);
lean_inc_ref(v___y_3138_);
lean_inc(v___y_3137_);
lean_inc_ref(v___y_3136_);
v___x_3143_ = lean_apply_8(v___y_3134_, v___x_3142_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, lean_box(0));
if (lean_obj_tag(v___x_3143_) == 0)
{
lean_object* v_a_3144_; lean_object* v_m_3145_; lean_object* v_u_3146_; lean_object* v_v_3147_; lean_object* v___x_3148_; 
v_a_3144_ = lean_ctor_get(v___x_3143_, 0);
lean_inc(v_a_3144_);
lean_dec_ref(v___x_3143_);
v_m_3145_ = lean_ctor_get(v___y_3125_, 0);
lean_inc_ref(v_m_3145_);
v_u_3146_ = lean_ctor_get(v___y_3125_, 1);
lean_inc(v_u_3146_);
v_v_3147_ = lean_ctor_get(v___y_3125_, 2);
lean_inc(v_v_3147_);
lean_dec_ref(v___y_3125_);
lean_inc(v_u_3146_);
v___x_3148_ = l_Lean_Meta_mkProdMkN(v_a_3144_, v_u_3146_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_);
if (lean_obj_tag(v___x_3148_) == 0)
{
lean_object* v_a_3149_; 
v_a_3149_ = lean_ctor_get(v___x_3148_, 0);
lean_inc(v_a_3149_);
lean_dec_ref(v___x_3148_);
if (lean_obj_tag(v___y_3127_) == 0)
{
lean_object* v_fst_3150_; lean_object* v_snd_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3170_; 
v_fst_3150_ = lean_ctor_get(v_a_3149_, 0);
v_snd_3151_ = lean_ctor_get(v_a_3149_, 1);
v_isSharedCheck_3170_ = !lean_is_exclusive(v_a_3149_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3153_ = v_a_3149_;
v_isShared_3154_ = v_isSharedCheck_3170_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_snd_3151_);
lean_inc(v_fst_3150_);
lean_dec(v_a_3149_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3170_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3158_; 
v___x_3155_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__1));
v___x_3156_ = lean_box(0);
lean_inc(v_v_3147_);
if (v_isShared_3154_ == 0)
{
lean_ctor_set_tag(v___x_3153_, 1);
lean_ctor_set(v___x_3153_, 1, v___x_3156_);
lean_ctor_set(v___x_3153_, 0, v_v_3147_);
v___x_3158_ = v___x_3153_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_v_3147_);
lean_ctor_set(v_reuseFailAlloc_3169_, 1, v___x_3156_);
v___x_3158_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
lean_inc(v_u_3146_);
v___x_3159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3159_, 0, v_u_3146_);
lean_ctor_set(v___x_3159_, 1, v___x_3158_);
v___x_3160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3160_, 0, v___y_3133_);
lean_ctor_set(v___x_3160_, 1, v___x_3159_);
v___x_3161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3161_, 0, v___y_3124_);
lean_ctor_set(v___x_3161_, 1, v___x_3160_);
lean_inc_ref(v___x_3161_);
v___x_3162_ = l_Lean_mkConst(v___x_3155_, v___x_3161_);
lean_inc_ref(v___y_3123_);
lean_inc_ref(v___y_3128_);
lean_inc_ref(v_m_3145_);
v___x_3163_ = l_Lean_mkApp3(v___x_3162_, v_m_3145_, v___y_3128_, v___y_3123_);
v___x_3164_ = l_Lean_Elab_Term_mkInstMVar(v___x_3163_, v___x_3142_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_a_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; 
v_a_3165_ = lean_ctor_get(v___x_3164_, 0);
lean_inc(v_a_3165_);
lean_dec_ref(v___x_3164_);
v___x_3166_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__3));
v___x_3167_ = l_Lean_mkConst(v___x_3166_, v___x_3161_);
lean_inc(v_snd_3151_);
v___x_3168_ = l_Lean_mkApp7(v___x_3167_, v_m_3145_, v___y_3128_, v___y_3123_, v_a_3165_, v_snd_3151_, v___y_3132_, v_fst_3150_);
v___y_3049_ = v___y_3108_;
v___y_3050_ = v_v_3147_;
v___y_3051_ = v_u_3146_;
v___y_3052_ = v_snd_3151_;
v___y_3053_ = v___y_3109_;
v___y_3054_ = v___y_3110_;
v___y_3055_ = v___y_3111_;
v___y_3056_ = v___y_3112_;
v___y_3057_ = v___y_3113_;
v___y_3058_ = v___y_3114_;
v___y_3059_ = v___y_3115_;
v___y_3060_ = v___y_3116_;
v___y_3061_ = v___y_3117_;
v___y_3062_ = v___x_3142_;
v___y_3063_ = v___y_3118_;
v___y_3064_ = v___y_3119_;
v___y_3065_ = v___y_3120_;
v___y_3066_ = v___y_3121_;
v___y_3067_ = v___y_3122_;
v___y_3068_ = v___y_3127_;
v___y_3069_ = v___y_3129_;
v___y_3070_ = v___y_3130_;
v___y_3071_ = v___y_3131_;
v_fst_3072_ = v___x_3168_;
v_snd_3073_ = v___x_3142_;
v___y_3074_ = v___y_3135_;
v___y_3075_ = v___y_3136_;
v___y_3076_ = v___y_3137_;
v___y_3077_ = v___y_3138_;
v___y_3078_ = v___y_3139_;
v___y_3079_ = v___y_3140_;
v___y_3080_ = v___y_3141_;
goto v___jp_3048_;
}
else
{
lean_dec_ref(v___x_3161_);
lean_dec(v_snd_3151_);
lean_dec(v_fst_3150_);
lean_dec(v_v_3147_);
lean_dec(v_u_3146_);
lean_dec_ref(v_m_3145_);
lean_dec_ref(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec_ref(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec_ref(v_dec_2994_);
return v___x_3164_;
}
}
}
}
else
{
lean_object* v_fst_3171_; lean_object* v_snd_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3207_; 
v_fst_3171_ = lean_ctor_get(v_a_3149_, 0);
v_snd_3172_ = lean_ctor_get(v_a_3149_, 1);
v_isSharedCheck_3207_ = !lean_is_exclusive(v_a_3149_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3174_ = v_a_3149_;
v_isShared_3175_ = v_isSharedCheck_3207_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_snd_3172_);
lean_inc(v_fst_3171_);
lean_dec(v_a_3149_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3207_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3179_; 
v___x_3176_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__4));
v___x_3177_ = lean_box(0);
lean_inc(v___y_3124_);
if (v_isShared_3175_ == 0)
{
lean_ctor_set_tag(v___x_3174_, 1);
lean_ctor_set(v___x_3174_, 1, v___x_3177_);
lean_ctor_set(v___x_3174_, 0, v___y_3124_);
v___x_3179_ = v___x_3174_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___y_3124_);
lean_ctor_set(v_reuseFailAlloc_3206_, 1, v___x_3177_);
v___x_3179_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
lean_inc(v___y_3133_);
v___x_3180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3180_, 0, v___y_3133_);
lean_ctor_set(v___x_3180_, 1, v___x_3179_);
v___x_3181_ = l_Lean_mkConst(v___x_3176_, v___x_3180_);
lean_inc_ref(v___y_3128_);
lean_inc_ref(v___y_3123_);
v___x_3182_ = l_Lean_mkAppB(v___x_3181_, v___y_3123_, v___y_3128_);
v___x_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3182_);
v___x_3184_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__6));
v___x_3185_ = l_Lean_Meta_mkFreshExprMVar(v___x_3183_, v___y_3126_, v___x_3184_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_object* v_a_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v_a_3186_ = lean_ctor_get(v___x_3185_, 0);
lean_inc(v_a_3186_);
lean_dec_ref(v___x_3185_);
v___x_3187_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__8));
lean_inc(v_v_3147_);
v___x_3188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3188_, 0, v_v_3147_);
lean_ctor_set(v___x_3188_, 1, v___x_3177_);
lean_inc(v_u_3146_);
v___x_3189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3189_, 0, v_u_3146_);
lean_ctor_set(v___x_3189_, 1, v___x_3188_);
v___x_3190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3190_, 0, v___y_3133_);
lean_ctor_set(v___x_3190_, 1, v___x_3189_);
v___x_3191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3191_, 0, v___y_3124_);
lean_ctor_set(v___x_3191_, 1, v___x_3190_);
lean_inc_ref(v___x_3191_);
v___x_3192_ = l_Lean_mkConst(v___x_3187_, v___x_3191_);
lean_inc(v_a_3186_);
lean_inc_ref(v___y_3123_);
lean_inc_ref(v___y_3128_);
lean_inc_ref(v_m_3145_);
v___x_3193_ = l_Lean_mkApp4(v___x_3192_, v_m_3145_, v___y_3128_, v___y_3123_, v_a_3186_);
v___x_3194_ = l_Lean_Elab_Term_mkInstMVar(v___x_3193_, v___x_3142_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_);
if (lean_obj_tag(v___x_3194_) == 0)
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3205_; 
v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3197_ = v___x_3194_;
v_isShared_3198_ = v_isSharedCheck_3205_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3194_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3205_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3203_; 
v___x_3199_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__10));
v___x_3200_ = l_Lean_mkConst(v___x_3199_, v___x_3191_);
lean_inc(v_snd_3172_);
lean_inc(v_a_3186_);
v___x_3201_ = l_Lean_mkApp8(v___x_3200_, v_m_3145_, v___y_3128_, v___y_3123_, v_a_3186_, v_a_3195_, v_snd_3172_, v___y_3132_, v_fst_3171_);
if (v_isShared_3198_ == 0)
{
lean_ctor_set_tag(v___x_3197_, 1);
lean_ctor_set(v___x_3197_, 0, v_a_3186_);
v___x_3203_ = v___x_3197_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3186_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
v___y_3049_ = v___y_3108_;
v___y_3050_ = v_v_3147_;
v___y_3051_ = v_u_3146_;
v___y_3052_ = v_snd_3172_;
v___y_3053_ = v___y_3109_;
v___y_3054_ = v___y_3110_;
v___y_3055_ = v___y_3111_;
v___y_3056_ = v___y_3112_;
v___y_3057_ = v___y_3113_;
v___y_3058_ = v___y_3114_;
v___y_3059_ = v___y_3115_;
v___y_3060_ = v___y_3116_;
v___y_3061_ = v___y_3117_;
v___y_3062_ = v___x_3142_;
v___y_3063_ = v___y_3118_;
v___y_3064_ = v___y_3119_;
v___y_3065_ = v___y_3120_;
v___y_3066_ = v___y_3121_;
v___y_3067_ = v___y_3122_;
v___y_3068_ = v___y_3127_;
v___y_3069_ = v___y_3129_;
v___y_3070_ = v___y_3130_;
v___y_3071_ = v___y_3131_;
v_fst_3072_ = v___x_3201_;
v_snd_3073_ = v___x_3203_;
v___y_3074_ = v___y_3135_;
v___y_3075_ = v___y_3136_;
v___y_3076_ = v___y_3137_;
v___y_3077_ = v___y_3138_;
v___y_3078_ = v___y_3139_;
v___y_3079_ = v___y_3140_;
v___y_3080_ = v___y_3141_;
goto v___jp_3048_;
}
}
}
else
{
lean_dec_ref(v___x_3191_);
lean_dec(v_a_3186_);
lean_dec(v_snd_3172_);
lean_dec(v_fst_3171_);
lean_dec_ref(v___y_3127_);
lean_dec(v_v_3147_);
lean_dec(v_u_3146_);
lean_dec_ref(v_m_3145_);
lean_dec_ref(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec_ref(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec_ref(v_dec_2994_);
return v___x_3194_;
}
}
else
{
lean_dec(v_snd_3172_);
lean_dec_ref(v___y_3127_);
lean_dec(v_fst_3171_);
lean_dec(v_v_3147_);
lean_dec(v_u_3146_);
lean_dec_ref(v_m_3145_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec_ref(v_dec_2994_);
return v___x_3185_;
}
}
}
}
}
else
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3215_; 
lean_dec(v_v_3147_);
lean_dec(v_u_3146_);
lean_dec_ref(v_m_3145_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec(v___y_3127_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec_ref(v_dec_2994_);
v_a_3208_ = lean_ctor_get(v___x_3148_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3148_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3210_ = v___x_3148_;
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3148_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3213_; 
if (v_isShared_3211_ == 0)
{
v___x_3213_ = v___x_3210_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_a_3208_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
else
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3125_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec_ref(v_dec_2994_);
v_a_3216_ = lean_ctor_get(v___x_3143_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3143_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___x_3143_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3143_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3221_; 
if (v_isShared_3219_ == 0)
{
v___x_3221_ = v___x_3218_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
}
v___jp_3224_:
{
lean_object* v___x_3256_; 
v___x_3256_ = l_Lean_Elab_Do_mkPUnit___redArg(v___y_3245_);
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v_a_3257_; lean_object* v_resultName_3258_; lean_object* v_resultType_3259_; lean_object* v___x_3260_; 
v_a_3257_ = lean_ctor_get(v___x_3256_, 0);
lean_inc(v_a_3257_);
lean_dec_ref(v___x_3256_);
v_resultName_3258_ = lean_ctor_get(v_dec_2994_, 0);
v_resultType_3259_ = lean_ctor_get(v_dec_2994_, 1);
lean_inc_ref(v_resultType_3259_);
v___x_3260_ = l_Lean_Meta_isExprDefEq(v_resultType_3259_, v_a_3257_, v___y_3250_, v___y_3252_, v___y_3237_, v___y_3240_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v_a_3261_; uint8_t v___x_3262_; 
v_a_3261_ = lean_ctor_get(v___x_3260_, 0);
lean_inc(v_a_3261_);
lean_dec_ref(v___x_3260_);
v___x_3262_ = lean_unbox(v_a_3261_);
lean_dec(v_a_3261_);
if (v___x_3262_ == 0)
{
lean_object* v___x_3263_; 
v___x_3263_ = l_Lean_Elab_Do_mkPUnit___redArg(v___y_3245_);
if (lean_obj_tag(v___x_3263_) == 0)
{
lean_object* v_a_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
v_a_3264_ = lean_ctor_get(v___x_3263_, 0);
lean_inc(v_a_3264_);
lean_dec_ref(v___x_3263_);
v___x_3265_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___closed__12, &l_Lean_Elab_Do_elabDoFor___closed__12_once, _init_l_Lean_Elab_Do_elabDoFor___closed__12);
v___x_3266_ = l_Lean_MessageData_ofExpr(v_a_3264_);
v___x_3267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3265_);
lean_ctor_set(v___x_3267_, 1, v___x_3266_);
v___x_3268_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___closed__14, &l_Lean_Elab_Do_elabDoFor___closed__14_once, _init_l_Lean_Elab_Do_elabDoFor___closed__14);
v___x_3269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3267_);
lean_ctor_set(v___x_3269_, 1, v___x_3268_);
lean_inc_ref(v_resultType_3259_);
v___x_3270_ = l_Lean_MessageData_ofExpr(v_resultType_3259_);
v___x_3271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3271_, 0, v___x_3269_);
lean_ctor_set(v___x_3271_, 1, v___x_3270_);
v___x_3272_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___closed__16, &l_Lean_Elab_Do_elabDoFor___closed__16_once, _init_l_Lean_Elab_Do_elabDoFor___closed__16);
v___x_3273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3273_, 0, v___x_3271_);
lean_ctor_set(v___x_3273_, 1, v___x_3272_);
v___x_3274_ = l_Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6(v___x_3273_, v___y_3245_, v___y_3248_, v___y_3251_, v___y_3250_, v___y_3252_, v___y_3237_, v___y_3240_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_dec_ref(v___x_3274_);
lean_inc_ref(v___y_3239_);
lean_inc_ref(v___y_3234_);
lean_inc_ref(v_resultType_3259_);
lean_inc(v_resultName_3258_);
v___y_3108_ = v___y_3228_;
v___y_3109_ = v_resultName_3258_;
v___y_3110_ = v___y_3229_;
v___y_3111_ = v___y_3231_;
v___y_3112_ = v___y_3233_;
v___y_3113_ = v___y_3232_;
v___y_3114_ = v___y_3236_;
v___y_3115_ = v___y_3235_;
v___y_3116_ = v___y_3227_;
v___y_3117_ = v___y_3226_;
v___y_3118_ = v___y_3225_;
v___y_3119_ = v___y_3255_;
v___y_3120_ = v_resultType_3259_;
v___y_3121_ = v___y_3230_;
v___y_3122_ = v___y_3234_;
v___y_3123_ = v___y_3238_;
v___y_3124_ = v___y_3249_;
v___y_3125_ = v___y_3239_;
v___y_3126_ = v___y_3241_;
v___y_3127_ = v___y_3242_;
v___y_3128_ = v___y_3243_;
v___y_3129_ = v___y_3253_;
v___y_3130_ = v___y_3254_;
v___y_3131_ = v___y_3244_;
v___y_3132_ = v___y_3246_;
v___y_3133_ = v___y_3247_;
v___y_3134_ = v___y_3234_;
v___y_3135_ = v___y_3245_;
v___y_3136_ = v___y_3248_;
v___y_3137_ = v___y_3251_;
v___y_3138_ = v___y_3250_;
v___y_3139_ = v___y_3252_;
v___y_3140_ = v___y_3237_;
v___y_3141_ = v___y_3240_;
goto v___jp_3107_;
}
else
{
lean_object* v_a_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3282_; 
lean_dec(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3249_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec_ref(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3238_);
lean_dec_ref(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec_ref(v_dec_2994_);
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3277_ = v___x_3274_;
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_a_3275_);
lean_dec(v___x_3274_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3280_; 
if (v_isShared_3278_ == 0)
{
v___x_3280_ = v___x_3277_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_a_3275_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
return v___x_3280_;
}
}
}
}
else
{
lean_dec(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3249_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec_ref(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3238_);
lean_dec_ref(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec_ref(v_dec_2994_);
return v___x_3263_;
}
}
else
{
lean_inc_ref(v___y_3239_);
lean_inc_ref(v___y_3234_);
lean_inc_ref(v_resultType_3259_);
lean_inc(v_resultName_3258_);
v___y_3108_ = v___y_3228_;
v___y_3109_ = v_resultName_3258_;
v___y_3110_ = v___y_3229_;
v___y_3111_ = v___y_3231_;
v___y_3112_ = v___y_3233_;
v___y_3113_ = v___y_3232_;
v___y_3114_ = v___y_3236_;
v___y_3115_ = v___y_3235_;
v___y_3116_ = v___y_3227_;
v___y_3117_ = v___y_3226_;
v___y_3118_ = v___y_3225_;
v___y_3119_ = v___y_3255_;
v___y_3120_ = v_resultType_3259_;
v___y_3121_ = v___y_3230_;
v___y_3122_ = v___y_3234_;
v___y_3123_ = v___y_3238_;
v___y_3124_ = v___y_3249_;
v___y_3125_ = v___y_3239_;
v___y_3126_ = v___y_3241_;
v___y_3127_ = v___y_3242_;
v___y_3128_ = v___y_3243_;
v___y_3129_ = v___y_3253_;
v___y_3130_ = v___y_3254_;
v___y_3131_ = v___y_3244_;
v___y_3132_ = v___y_3246_;
v___y_3133_ = v___y_3247_;
v___y_3134_ = v___y_3234_;
v___y_3135_ = v___y_3245_;
v___y_3136_ = v___y_3248_;
v___y_3137_ = v___y_3251_;
v___y_3138_ = v___y_3250_;
v___y_3139_ = v___y_3252_;
v___y_3140_ = v___y_3237_;
v___y_3141_ = v___y_3240_;
goto v___jp_3107_;
}
}
else
{
lean_object* v_a_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3290_; 
lean_dec(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3249_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec_ref(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3238_);
lean_dec_ref(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec_ref(v_dec_2994_);
v_a_3283_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3285_ = v___x_3260_;
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_a_3283_);
lean_dec(v___x_3260_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3288_; 
if (v_isShared_3286_ == 0)
{
v___x_3288_ = v___x_3285_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_a_3283_);
v___x_3288_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
return v___x_3288_;
}
}
}
}
else
{
lean_dec(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3249_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec_ref(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3238_);
lean_dec_ref(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec_ref(v_dec_2994_);
return v___x_3256_;
}
}
v___jp_3291_:
{
uint8_t v_returnsEarly_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___f_3326_; 
v_returnsEarly_3323_ = lean_ctor_get_uint8(v___y_3321_, sizeof(void*)*2 + 2);
lean_dec_ref(v___y_3321_);
v___x_3324_ = lean_box(v_returnsEarly_3323_);
v___x_3325_ = lean_box(v___y_3294_);
lean_inc_ref(v___y_3301_);
lean_inc_ref(v___y_3292_);
lean_inc_ref(v___y_3322_);
v___f_3326_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__2___boxed), 14, 6);
lean_closure_set(v___f_3326_, 0, v___y_3322_);
lean_closure_set(v___f_3326_, 1, v___y_3292_);
lean_closure_set(v___f_3326_, 2, v___x_3324_);
lean_closure_set(v___f_3326_, 3, v___x_3010_);
lean_closure_set(v___f_3326_, 4, v___y_3301_);
lean_closure_set(v___f_3326_, 5, v___x_3325_);
if (v_returnsEarly_3323_ == 0)
{
size_t v_sz_3327_; size_t v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
lean_dec(v___y_3320_);
v_sz_3327_ = lean_array_size(v___y_3322_);
v___x_3328_ = ((size_t)0ULL);
lean_inc_ref(v___y_3322_);
v___x_3329_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__7(v_sz_3327_, v___x_3328_, v___y_3322_);
v___x_3330_ = lean_array_to_list(v___x_3329_);
v___y_3225_ = v___y_3322_;
v___y_3226_ = v___y_3301_;
v___y_3227_ = v___y_3302_;
v___y_3228_ = v___y_3293_;
v___y_3229_ = v___y_3295_;
v___y_3230_ = v___y_3304_;
v___y_3231_ = v___y_3296_;
v___y_3232_ = v___y_3298_;
v___y_3233_ = v___y_3299_;
v___y_3234_ = v___f_3326_;
v___y_3235_ = v___y_3300_;
v___y_3236_ = v_returnsEarly_3323_;
v___y_3237_ = v___y_3305_;
v___y_3238_ = v___y_3306_;
v___y_3239_ = v___y_3292_;
v___y_3240_ = v___y_3307_;
v___y_3241_ = v___y_3308_;
v___y_3242_ = v___y_3309_;
v___y_3243_ = v___y_3310_;
v___y_3244_ = v___y_3297_;
v___y_3245_ = v___y_3311_;
v___y_3246_ = v___y_3312_;
v___y_3247_ = v___y_3313_;
v___y_3248_ = v___y_3314_;
v___y_3249_ = v___y_3315_;
v___y_3250_ = v___y_3316_;
v___y_3251_ = v___y_3318_;
v___y_3252_ = v___y_3317_;
v___y_3253_ = v___y_3303_;
v___y_3254_ = v___y_3319_;
v___y_3255_ = v___x_3330_;
goto v___jp_3224_;
}
else
{
size_t v_sz_3331_; size_t v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v_sz_3331_ = lean_array_size(v___y_3322_);
v___x_3332_ = ((size_t)0ULL);
lean_inc_ref(v___y_3322_);
v___x_3333_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__7(v_sz_3331_, v___x_3332_, v___y_3322_);
v___x_3334_ = lean_array_to_list(v___x_3333_);
v___x_3335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3335_, 0, v___y_3320_);
lean_ctor_set(v___x_3335_, 1, v___x_3334_);
v___y_3225_ = v___y_3322_;
v___y_3226_ = v___y_3301_;
v___y_3227_ = v___y_3302_;
v___y_3228_ = v___y_3293_;
v___y_3229_ = v___y_3295_;
v___y_3230_ = v___y_3304_;
v___y_3231_ = v___y_3296_;
v___y_3232_ = v___y_3298_;
v___y_3233_ = v___y_3299_;
v___y_3234_ = v___f_3326_;
v___y_3235_ = v___y_3300_;
v___y_3236_ = v_returnsEarly_3323_;
v___y_3237_ = v___y_3305_;
v___y_3238_ = v___y_3306_;
v___y_3239_ = v___y_3292_;
v___y_3240_ = v___y_3307_;
v___y_3241_ = v___y_3308_;
v___y_3242_ = v___y_3309_;
v___y_3243_ = v___y_3310_;
v___y_3244_ = v___y_3297_;
v___y_3245_ = v___y_3311_;
v___y_3246_ = v___y_3312_;
v___y_3247_ = v___y_3313_;
v___y_3248_ = v___y_3314_;
v___y_3249_ = v___y_3315_;
v___y_3250_ = v___y_3316_;
v___y_3251_ = v___y_3318_;
v___y_3252_ = v___y_3317_;
v___y_3253_ = v___y_3303_;
v___y_3254_ = v___y_3319_;
v___y_3255_ = v___x_3335_;
goto v___jp_3224_;
}
}
v___jp_3336_:
{
lean_object* v_x_3345_; lean_object* v___x_3346_; uint8_t v___x_3347_; 
v_x_3345_ = l_Lean_Syntax_getArg(v___x_3011_, v___x_3006_);
v___x_3346_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__16));
lean_inc(v_x_3345_);
v___x_3347_ = l_Lean_Syntax_isOfKind(v_x_3345_, v___x_3346_);
if (v___x_3347_ == 0)
{
lean_object* v___x_3348_; 
lean_dec(v_x_3345_);
lean_dec(v_h_x3f_3337_);
lean_dec(v___x_3011_);
lean_dec_ref(v_dec_2994_);
lean_dec(v_stx_2993_);
v___x_3348_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_3348_;
}
else
{
lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3349_ = lean_mk_empty_array_with_capacity(v___x_3006_);
lean_inc(v_x_3345_);
v___x_3350_ = lean_array_push(v___x_3349_, v_x_3345_);
v___x_3351_ = l_Lean_Elab_Do_checkMutVarsForShadowing(v___x_3350_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
lean_dec_ref(v___x_3350_);
if (lean_obj_tag(v___x_3351_) == 0)
{
lean_object* v___x_3352_; 
lean_dec_ref(v___x_3351_);
v___x_3352_ = l_Lean_Meta_mkFreshLevelMVar(v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v_a_3353_; lean_object* v___x_3354_; 
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
lean_inc(v_a_3353_);
lean_dec_ref(v___x_3352_);
v___x_3354_ = l_Lean_Meta_mkFreshLevelMVar(v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_object* v_a_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; uint8_t v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
v_a_3355_ = lean_ctor_get(v___x_3354_, 0);
lean_inc(v_a_3355_);
lean_dec_ref(v___x_3354_);
lean_inc(v_a_3353_);
v___x_3356_ = l_Lean_Level_succ___override(v_a_3353_);
v___x_3357_ = l_Lean_mkSort(v___x_3356_);
v___x_3358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3357_);
v___x_3359_ = 0;
v___x_3360_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__18));
v___x_3361_ = l_Lean_Meta_mkFreshExprMVar(v___x_3358_, v___x_3359_, v___x_3360_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3434_; 
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3364_ = v___x_3361_;
v_isShared_3365_ = v_isSharedCheck_3434_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3361_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3434_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3369_; 
lean_inc(v_a_3355_);
v___x_3366_ = l_Lean_Level_succ___override(v_a_3355_);
v___x_3367_ = l_Lean_mkSort(v___x_3366_);
if (v_isShared_3365_ == 0)
{
lean_ctor_set_tag(v___x_3364_, 1);
lean_ctor_set(v___x_3364_, 0, v___x_3367_);
v___x_3369_ = v___x_3364_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v___x_3367_);
v___x_3369_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
lean_object* v___x_3370_; lean_object* v___x_3371_; 
v___x_3370_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__20));
v___x_3371_ = l_Lean_Meta_mkFreshExprMVar(v___x_3369_, v___x_3359_, v___x_3370_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v_a_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3432_; 
v_a_3372_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3432_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3374_ = v___x_3371_;
v_isShared_3375_ = v_isSharedCheck_3432_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_a_3372_);
lean_dec(v___x_3371_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3432_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3379_; 
v___x_3376_ = lean_unsigned_to_nat(3u);
v___x_3377_ = l_Lean_Syntax_getArg(v___x_3011_, v___x_3376_);
lean_dec(v___x_3011_);
lean_inc(v_a_3372_);
if (v_isShared_3375_ == 0)
{
lean_ctor_set_tag(v___x_3374_, 1);
v___x_3379_ = v___x_3374_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_a_3372_);
v___x_3379_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
lean_object* v___x_3380_; lean_object* v___x_3381_; 
v___x_3380_ = lean_box(0);
v___x_3381_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_3377_, v___x_3379_, v___x_3013_, v___x_3013_, v___x_3380_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_a_3382_; lean_object* v_body_3383_; lean_object* v___x_3384_; 
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
lean_inc(v_a_3382_);
lean_dec_ref(v___x_3381_);
v_body_3383_ = l_Lean_Syntax_getArg(v_stx_2993_, v___x_3376_);
lean_dec(v_stx_2993_);
lean_inc(v_body_3383_);
v___x_3384_ = l_Lean_Elab_Do_inferControlInfoSeq(v_body_3383_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_a_3385_; lean_object* v___x_3386_; 
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
lean_inc(v_a_3385_);
lean_dec_ref(v___x_3384_);
v___x_3386_ = l_Lean_Elab_Do_getReturnCont___redArg(v___y_3338_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_a_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
lean_inc(v_a_3387_);
lean_dec_ref(v___x_3386_);
v___x_3388_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__22));
v___x_3389_ = l_Lean_Core_mkFreshUserName(v___x_3388_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3389_) == 0)
{
lean_object* v_a_3390_; lean_object* v_monadInfo_3391_; lean_object* v_mutVars_3392_; lean_object* v___f_3393_; lean_object* v___f_3394_; lean_object* v___x_3395_; lean_object* v___f_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; uint8_t v___x_3399_; 
v_a_3390_ = lean_ctor_get(v___x_3389_, 0);
lean_inc(v_a_3390_);
lean_dec_ref(v___x_3389_);
v_monadInfo_3391_ = lean_ctor_get(v___y_3338_, 0);
v_mutVars_3392_ = lean_ctor_get(v___y_3338_, 1);
lean_inc(v_a_3362_);
v___f_3393_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__0___boxed), 10, 1);
lean_closure_set(v___f_3393_, 0, v_a_3362_);
lean_inc_ref(v___f_3393_);
lean_inc(v_x_3345_);
v___f_3394_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__1___boxed), 5, 3);
lean_closure_set(v___f_3394_, 0, v_x_3345_);
lean_closure_set(v___f_3394_, 1, v___f_3393_);
lean_closure_set(v___f_3394_, 2, v___x_3006_);
v___x_3395_ = lean_box(v___x_3013_);
lean_inc(v_a_3387_);
v___f_3396_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__3___boxed), 12, 3);
lean_closure_set(v___f_3396_, 0, v_a_3387_);
lean_closure_set(v___f_3396_, 1, v___x_3006_);
lean_closure_set(v___f_3396_, 2, v___x_3395_);
v___x_3397_ = lean_array_get_size(v_mutVars_3392_);
v___x_3398_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_3399_ = lean_nat_dec_lt(v___x_3010_, v___x_3397_);
if (v___x_3399_ == 0)
{
lean_inc(v_a_3390_);
lean_inc(v_a_3355_);
lean_inc(v_a_3382_);
lean_inc(v_a_3353_);
lean_inc(v_a_3372_);
lean_inc(v_a_3362_);
v___y_3292_ = v_monadInfo_3391_;
v___y_3293_ = v_a_3362_;
v___y_3294_ = v___x_3347_;
v___y_3295_ = v_a_3372_;
v___y_3296_ = v_body_3383_;
v___y_3297_ = v___f_3393_;
v___y_3298_ = v_a_3353_;
v___y_3299_ = v_a_3382_;
v___y_3300_ = v___f_3396_;
v___y_3301_ = v_a_3387_;
v___y_3302_ = v_a_3355_;
v___y_3303_ = v___f_3394_;
v___y_3304_ = v_a_3390_;
v___y_3305_ = v___y_3343_;
v___y_3306_ = v_a_3362_;
v___y_3307_ = v___y_3344_;
v___y_3308_ = v___x_3359_;
v___y_3309_ = v_h_x3f_3337_;
v___y_3310_ = v_a_3372_;
v___y_3311_ = v___y_3338_;
v___y_3312_ = v_a_3382_;
v___y_3313_ = v_a_3353_;
v___y_3314_ = v___y_3339_;
v___y_3315_ = v_a_3355_;
v___y_3316_ = v___y_3341_;
v___y_3317_ = v___y_3342_;
v___y_3318_ = v___y_3340_;
v___y_3319_ = v_x_3345_;
v___y_3320_ = v_a_3390_;
v___y_3321_ = v_a_3385_;
v___y_3322_ = v___x_3398_;
goto v___jp_3291_;
}
else
{
uint8_t v___x_3400_; 
v___x_3400_ = lean_nat_dec_le(v___x_3397_, v___x_3397_);
if (v___x_3400_ == 0)
{
if (v___x_3399_ == 0)
{
lean_inc(v_a_3390_);
lean_inc(v_a_3355_);
lean_inc(v_a_3382_);
lean_inc(v_a_3353_);
lean_inc(v_a_3372_);
lean_inc(v_a_3362_);
v___y_3292_ = v_monadInfo_3391_;
v___y_3293_ = v_a_3362_;
v___y_3294_ = v___x_3347_;
v___y_3295_ = v_a_3372_;
v___y_3296_ = v_body_3383_;
v___y_3297_ = v___f_3393_;
v___y_3298_ = v_a_3353_;
v___y_3299_ = v_a_3382_;
v___y_3300_ = v___f_3396_;
v___y_3301_ = v_a_3387_;
v___y_3302_ = v_a_3355_;
v___y_3303_ = v___f_3394_;
v___y_3304_ = v_a_3390_;
v___y_3305_ = v___y_3343_;
v___y_3306_ = v_a_3362_;
v___y_3307_ = v___y_3344_;
v___y_3308_ = v___x_3359_;
v___y_3309_ = v_h_x3f_3337_;
v___y_3310_ = v_a_3372_;
v___y_3311_ = v___y_3338_;
v___y_3312_ = v_a_3382_;
v___y_3313_ = v_a_3353_;
v___y_3314_ = v___y_3339_;
v___y_3315_ = v_a_3355_;
v___y_3316_ = v___y_3341_;
v___y_3317_ = v___y_3342_;
v___y_3318_ = v___y_3340_;
v___y_3319_ = v_x_3345_;
v___y_3320_ = v_a_3390_;
v___y_3321_ = v_a_3385_;
v___y_3322_ = v___x_3398_;
goto v___jp_3291_;
}
else
{
size_t v___x_3401_; size_t v___x_3402_; lean_object* v___x_3403_; 
v___x_3401_ = ((size_t)0ULL);
v___x_3402_ = lean_usize_of_nat(v___x_3397_);
v___x_3403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__8(v_a_3385_, v_mutVars_3392_, v___x_3401_, v___x_3402_, v___x_3398_);
lean_inc(v_a_3390_);
lean_inc(v_a_3355_);
lean_inc(v_a_3382_);
lean_inc(v_a_3353_);
lean_inc(v_a_3372_);
lean_inc(v_a_3362_);
v___y_3292_ = v_monadInfo_3391_;
v___y_3293_ = v_a_3362_;
v___y_3294_ = v___x_3347_;
v___y_3295_ = v_a_3372_;
v___y_3296_ = v_body_3383_;
v___y_3297_ = v___f_3393_;
v___y_3298_ = v_a_3353_;
v___y_3299_ = v_a_3382_;
v___y_3300_ = v___f_3396_;
v___y_3301_ = v_a_3387_;
v___y_3302_ = v_a_3355_;
v___y_3303_ = v___f_3394_;
v___y_3304_ = v_a_3390_;
v___y_3305_ = v___y_3343_;
v___y_3306_ = v_a_3362_;
v___y_3307_ = v___y_3344_;
v___y_3308_ = v___x_3359_;
v___y_3309_ = v_h_x3f_3337_;
v___y_3310_ = v_a_3372_;
v___y_3311_ = v___y_3338_;
v___y_3312_ = v_a_3382_;
v___y_3313_ = v_a_3353_;
v___y_3314_ = v___y_3339_;
v___y_3315_ = v_a_3355_;
v___y_3316_ = v___y_3341_;
v___y_3317_ = v___y_3342_;
v___y_3318_ = v___y_3340_;
v___y_3319_ = v_x_3345_;
v___y_3320_ = v_a_3390_;
v___y_3321_ = v_a_3385_;
v___y_3322_ = v___x_3403_;
goto v___jp_3291_;
}
}
else
{
size_t v___x_3404_; size_t v___x_3405_; lean_object* v___x_3406_; 
v___x_3404_ = ((size_t)0ULL);
v___x_3405_ = lean_usize_of_nat(v___x_3397_);
v___x_3406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__8(v_a_3385_, v_mutVars_3392_, v___x_3404_, v___x_3405_, v___x_3398_);
lean_inc(v_a_3390_);
lean_inc(v_a_3355_);
lean_inc(v_a_3382_);
lean_inc(v_a_3353_);
lean_inc(v_a_3372_);
lean_inc(v_a_3362_);
v___y_3292_ = v_monadInfo_3391_;
v___y_3293_ = v_a_3362_;
v___y_3294_ = v___x_3347_;
v___y_3295_ = v_a_3372_;
v___y_3296_ = v_body_3383_;
v___y_3297_ = v___f_3393_;
v___y_3298_ = v_a_3353_;
v___y_3299_ = v_a_3382_;
v___y_3300_ = v___f_3396_;
v___y_3301_ = v_a_3387_;
v___y_3302_ = v_a_3355_;
v___y_3303_ = v___f_3394_;
v___y_3304_ = v_a_3390_;
v___y_3305_ = v___y_3343_;
v___y_3306_ = v_a_3362_;
v___y_3307_ = v___y_3344_;
v___y_3308_ = v___x_3359_;
v___y_3309_ = v_h_x3f_3337_;
v___y_3310_ = v_a_3372_;
v___y_3311_ = v___y_3338_;
v___y_3312_ = v_a_3382_;
v___y_3313_ = v_a_3353_;
v___y_3314_ = v___y_3339_;
v___y_3315_ = v_a_3355_;
v___y_3316_ = v___y_3341_;
v___y_3317_ = v___y_3342_;
v___y_3318_ = v___y_3340_;
v___y_3319_ = v_x_3345_;
v___y_3320_ = v_a_3390_;
v___y_3321_ = v_a_3385_;
v___y_3322_ = v___x_3406_;
goto v___jp_3291_;
}
}
}
else
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3414_; 
lean_dec(v_a_3387_);
lean_dec(v_a_3385_);
lean_dec(v_body_3383_);
lean_dec(v_a_3382_);
lean_dec(v_a_3372_);
lean_dec(v_a_3362_);
lean_dec(v_a_3355_);
lean_dec(v_a_3353_);
lean_dec(v_x_3345_);
lean_dec(v_h_x3f_3337_);
lean_dec_ref(v_dec_2994_);
v_a_3407_ = lean_ctor_get(v___x_3389_, 0);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3409_ = v___x_3389_;
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3389_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3412_; 
if (v_isShared_3410_ == 0)
{
v___x_3412_ = v___x_3409_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_a_3407_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
}
}
else
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3422_; 
lean_dec(v_a_3385_);
lean_dec(v_body_3383_);
lean_dec(v_a_3382_);
lean_dec(v_a_3372_);
lean_dec(v_a_3362_);
lean_dec(v_a_3355_);
lean_dec(v_a_3353_);
lean_dec(v_x_3345_);
lean_dec(v_h_x3f_3337_);
lean_dec_ref(v_dec_2994_);
v_a_3415_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3417_ = v___x_3386_;
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3386_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3420_; 
if (v_isShared_3418_ == 0)
{
v___x_3420_ = v___x_3417_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_a_3415_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
}
else
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3430_; 
lean_dec(v_body_3383_);
lean_dec(v_a_3382_);
lean_dec(v_a_3372_);
lean_dec(v_a_3362_);
lean_dec(v_a_3355_);
lean_dec(v_a_3353_);
lean_dec(v_x_3345_);
lean_dec(v_h_x3f_3337_);
lean_dec_ref(v_dec_2994_);
v_a_3423_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3425_ = v___x_3384_;
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3384_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3428_; 
if (v_isShared_3426_ == 0)
{
v___x_3428_ = v___x_3425_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_a_3423_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
}
}
else
{
lean_dec(v_a_3372_);
lean_dec(v_a_3362_);
lean_dec(v_a_3355_);
lean_dec(v_a_3353_);
lean_dec(v_x_3345_);
lean_dec(v_h_x3f_3337_);
lean_dec_ref(v_dec_2994_);
lean_dec(v_stx_2993_);
return v___x_3381_;
}
}
}
}
else
{
lean_dec(v_a_3362_);
lean_dec(v_a_3355_);
lean_dec(v_a_3353_);
lean_dec(v_x_3345_);
lean_dec(v_h_x3f_3337_);
lean_dec(v___x_3011_);
lean_dec_ref(v_dec_2994_);
lean_dec(v_stx_2993_);
return v___x_3371_;
}
}
}
}
else
{
lean_dec(v_a_3355_);
lean_dec(v_a_3353_);
lean_dec(v_x_3345_);
lean_dec(v_h_x3f_3337_);
lean_dec(v___x_3011_);
lean_dec_ref(v_dec_2994_);
lean_dec(v_stx_2993_);
return v___x_3361_;
}
}
else
{
lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3442_; 
lean_dec(v_a_3353_);
lean_dec(v_x_3345_);
lean_dec(v_h_x3f_3337_);
lean_dec(v___x_3011_);
lean_dec_ref(v_dec_2994_);
lean_dec(v_stx_2993_);
v_a_3435_ = lean_ctor_get(v___x_3354_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3354_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3437_ = v___x_3354_;
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v___x_3354_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3440_; 
if (v_isShared_3438_ == 0)
{
v___x_3440_ = v___x_3437_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_a_3435_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
}
else
{
lean_object* v_a_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3450_; 
lean_dec(v_x_3345_);
lean_dec(v_h_x3f_3337_);
lean_dec(v___x_3011_);
lean_dec_ref(v_dec_2994_);
lean_dec(v_stx_2993_);
v_a_3443_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3445_ = v___x_3352_;
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_a_3443_);
lean_dec(v___x_3352_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3448_; 
if (v_isShared_3446_ == 0)
{
v___x_3448_ = v___x_3445_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_a_3443_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
}
}
else
{
lean_object* v_a_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3458_; 
lean_dec(v_x_3345_);
lean_dec(v_h_x3f_3337_);
lean_dec(v___x_3011_);
lean_dec_ref(v_dec_2994_);
lean_dec(v_stx_2993_);
v_a_3451_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3453_ = v___x_3351_;
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_a_3451_);
lean_dec(v___x_3351_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3456_; 
if (v_isShared_3454_ == 0)
{
v___x_3456_ = v___x_3453_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_a_3451_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___boxed(lean_object* v_stx_3468_, lean_object* v_dec_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_){
_start:
{
lean_object* v_res_3478_; 
v_res_3478_ = l_Lean_Elab_Do_elabDoFor(v_stx_3468_, v_dec_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_);
lean_dec(v_a_3476_);
lean_dec_ref(v_a_3475_);
lean_dec(v_a_3474_);
lean_dec_ref(v_a_3473_);
lean_dec(v_a_3472_);
lean_dec_ref(v_a_3471_);
lean_dec_ref(v_a_3470_);
return v_res_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2(lean_object* v_00_u03b1_3479_, lean_object* v_msg_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_){
_start:
{
lean_object* v___x_3488_; 
lean_inc_ref(v___y_3481_);
v___x_3488_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v_msg_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_);
return v___x_3488_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___boxed(lean_object* v_00_u03b1_3489_, lean_object* v_msg_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_){
_start:
{
lean_object* v_res_3498_; 
v_res_3498_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2(v_00_u03b1_3489_, v_msg_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_);
lean_dec(v___y_3496_);
lean_dec_ref(v___y_3495_);
lean_dec(v___y_3494_);
lean_dec_ref(v___y_3493_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
return v_res_3498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(lean_object* v_00_u03b1_3499_, lean_object* v_inst_3500_, lean_object* v_declInfos_3501_, lean_object* v_k_3502_, uint8_t v_kind_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_){
_start:
{
lean_object* v___x_3512_; 
v___x_3512_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4___redArg(v_inst_3500_, v_declInfos_3501_, v_k_3502_, v_kind_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
return v___x_3512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4___boxed(lean_object* v_00_u03b1_3513_, lean_object* v_inst_3514_, lean_object* v_declInfos_3515_, lean_object* v_k_3516_, lean_object* v_kind_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_){
_start:
{
uint8_t v_kind_boxed_3526_; lean_object* v_res_3527_; 
v_kind_boxed_3526_ = lean_unbox(v_kind_3517_);
v_res_3527_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(v_00_u03b1_3513_, v_inst_3514_, v_declInfos_3515_, v_k_3516_, v_kind_boxed_3526_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_);
lean_dec(v___y_3524_);
lean_dec_ref(v___y_3523_);
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3521_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3519_);
lean_dec_ref(v___y_3518_);
lean_dec(v_inst_3514_);
return v_res_3527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5(lean_object* v_00_u03b1_3528_, lean_object* v_name_3529_, lean_object* v_type_3530_, lean_object* v_k_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_){
_start:
{
lean_object* v___x_3540_; 
v___x_3540_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(v_name_3529_, v_type_3530_, v_k_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___boxed(lean_object* v_00_u03b1_3541_, lean_object* v_name_3542_, lean_object* v_type_3543_, lean_object* v_k_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5(v_00_u03b1_3541_, v_name_3542_, v_type_3543_, v_k_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_);
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3550_);
lean_dec(v___y_3549_);
lean_dec_ref(v___y_3548_);
lean_dec(v___y_3547_);
lean_dec_ref(v___y_3546_);
lean_dec_ref(v___y_3545_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3(lean_object* v_msgData_3554_, lean_object* v_macroStack_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_){
_start:
{
lean_object* v___x_3563_; 
v___x_3563_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(v_msgData_3554_, v_macroStack_3555_, v___y_3560_);
return v___x_3563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___boxed(lean_object* v_msgData_3564_, lean_object* v_macroStack_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_){
_start:
{
lean_object* v_res_3573_; 
v_res_3573_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3(v_msgData_3564_, v_macroStack_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_);
lean_dec(v___y_3571_);
lean_dec_ref(v___y_3570_);
lean_dec(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
return v_res_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7(lean_object* v_00_u03b1_3574_, lean_object* v_inst_3575_, lean_object* v_declInfos_3576_, lean_object* v_k_3577_, uint8_t v_kind_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_){
_start:
{
lean_object* v___x_3587_; 
v___x_3587_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___redArg(v_inst_3575_, v_declInfos_3576_, v_k_3577_, v_kind_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___boxed(lean_object* v_00_u03b1_3588_, lean_object* v_inst_3589_, lean_object* v_declInfos_3590_, lean_object* v_k_3591_, lean_object* v_kind_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
uint8_t v_kind_boxed_3601_; lean_object* v_res_3602_; 
v_kind_boxed_3601_ = lean_unbox(v_kind_3592_);
v_res_3602_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7(v_00_u03b1_3588_, v_inst_3589_, v_declInfos_3590_, v_k_3591_, v_kind_boxed_3601_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec_ref(v___y_3593_);
lean_dec(v_inst_3589_);
return v_res_3602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(lean_object* v_00_u03b1_3603_, lean_object* v_declInfos_3604_, lean_object* v_k_3605_, uint8_t v_kind_3606_, lean_object* v_inst_3607_, lean_object* v_acc_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_){
_start:
{
lean_object* v___x_3617_; 
v___x_3617_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___redArg(v_declInfos_3604_, v_k_3605_, v_kind_3606_, v_acc_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b1_3618_, lean_object* v_declInfos_3619_, lean_object* v_k_3620_, lean_object* v_kind_3621_, lean_object* v_inst_3622_, lean_object* v_acc_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_){
_start:
{
uint8_t v_kind_boxed_3632_; lean_object* v_res_3633_; 
v_kind_boxed_3632_ = lean_unbox(v_kind_3621_);
v_res_3633_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(v_00_u03b1_3618_, v_declInfos_3619_, v_k_3620_, v_kind_boxed_3632_, v_inst_3622_, v_acc_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
lean_dec_ref(v___y_3624_);
lean_dec(v_inst_3622_);
return v_res_3633_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14(lean_object* v_ref_3634_, lean_object* v_msgData_3635_, uint8_t v_severity_3636_, uint8_t v_isSilent_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_){
_start:
{
lean_object* v___x_3646_; 
v___x_3646_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg(v_ref_3634_, v_msgData_3635_, v_severity_3636_, v_isSilent_3637_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___boxed(lean_object* v_ref_3647_, lean_object* v_msgData_3648_, lean_object* v_severity_3649_, lean_object* v_isSilent_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_){
_start:
{
uint8_t v_severity_boxed_3659_; uint8_t v_isSilent_boxed_3660_; lean_object* v_res_3661_; 
v_severity_boxed_3659_ = lean_unbox(v_severity_3649_);
v_isSilent_boxed_3660_ = lean_unbox(v_isSilent_3650_);
v_res_3661_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14(v_ref_3647_, v_msgData_3648_, v_severity_boxed_3659_, v_isSilent_boxed_3660_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_);
lean_dec(v___y_3657_);
lean_dec_ref(v___y_3656_);
lean_dec(v___y_3655_);
lean_dec_ref(v___y_3654_);
lean_dec(v___y_3653_);
lean_dec_ref(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v_ref_3647_);
return v_res_3661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1(){
_start:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; 
v___x_3669_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_3670_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
v___x_3671_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1));
v___x_3672_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___boxed), 10, 0);
v___x_3673_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3669_, v___x_3670_, v___x_3671_, v___x_3672_);
return v___x_3673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___boxed(lean_object* v_a_3674_){
_start:
{
lean_object* v_res_3675_; 
v_res_3675_ = l_Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1();
return v_res_3675_;
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
