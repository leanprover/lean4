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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__2 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__3 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__4 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__5 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__5_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__6 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__6_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__7 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___closed__0 = (const lean_object*)&l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc(v_quotContext_12_);
v___x_18_ = l_Lean_addMacroScope(v_quotContext_12_, v___x_13_, v_macroScope_6_);
v___x_19_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
lean_ctor_set(v___x_19_, 1, v___x_17_);
return v___x_19_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___boxed(lean_object* v___y_22_, lean_object* v___y_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1(v___y_22_, v___y_23_);
lean_dec_ref(v___y_22_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(lean_object* v_ref_25_, uint8_t v_canonical_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v___x_29_; lean_object* v_a_30_; lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_39_; 
v___x_29_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1(v___y_27_, v___y_28_);
v_a_30_ = lean_ctor_get(v___x_29_, 0);
v_a_31_ = lean_ctor_get(v___x_29_, 1);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_29_);
if (v_isSharedCheck_39_ == 0)
{
v___x_33_ = v___x_29_;
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_inc(v_a_30_);
lean_dec(v___x_29_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_39_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_35_; lean_object* v___x_37_; 
v___x_35_ = l_Lean_mkIdentFrom(v_ref_25_, v_a_30_, v_canonical_26_);
if (v_isShared_34_ == 0)
{
lean_ctor_set(v___x_33_, 0, v___x_35_);
v___x_37_ = v___x_33_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v___x_35_);
lean_ctor_set(v_reuseFailAlloc_38_, 1, v_a_31_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1___boxed(lean_object* v_ref_40_, lean_object* v_canonical_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
uint8_t v_canonical_boxed_44_; lean_object* v_res_45_; 
v_canonical_boxed_44_ = lean_unbox(v_canonical_41_);
v_res_45_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v_ref_40_, v_canonical_boxed_44_, v___y_42_, v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v_ref_40_);
return v_res_45_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__3));
v___x_51_ = l_String_toRawSubstring_x27(v___x_50_);
return v___x_51_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25(void){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Array_mkArray0(lean_box(0));
return v___x_83_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__32(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31));
v___x_91_ = l_String_toRawSubstring_x27(v___x_90_);
return v___x_91_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_110_ = l_String_toRawSubstring_x27(v___x_109_);
return v___x_110_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__52));
v___x_128_ = l_String_toRawSubstring_x27(v___x_127_);
return v___x_128_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__64(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__63));
v___x_148_ = l_String_toRawSubstring_x27(v___x_147_);
return v___x_148_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__68));
v___x_154_ = l_String_toRawSubstring_x27(v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(lean_object* v___x_163_, lean_object* v___x_164_, lean_object* v___x_165_, uint8_t v___x_166_, lean_object* v___x_167_, lean_object* v___x_168_, lean_object* v___x_169_, lean_object* v___f_170_, lean_object* v_fst_171_, lean_object* v___x_172_, lean_object* v_snd_173_, lean_object* v_x_174_, lean_object* v_h_x3f_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___y_181_; 
v___x_178_ = l_Lean_Syntax_getArg(v___x_163_, v___x_164_);
v___x_179_ = l_Lean_Syntax_getArg(v___x_163_, v___x_165_);
if (lean_obj_tag(v_h_x3f_175_) == 1)
{
lean_object* v_val_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v_val_396_ = lean_ctor_get(v_h_x3f_175_, 0);
v___x_397_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_398_ = l_Lean_Macro_throwErrorAt___redArg(v_val_396_, v___x_397_, v___y_176_, v___y_177_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; 
v_a_399_ = lean_ctor_get(v___x_398_, 1);
lean_inc(v_a_399_);
lean_dec_ref(v___x_398_);
v___y_181_ = v_a_399_;
goto v___jp_180_;
}
else
{
lean_object* v_a_400_; lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
lean_dec(v___x_179_);
lean_dec(v___x_178_);
lean_dec(v_snd_173_);
lean_dec_ref(v___x_172_);
lean_dec(v_fst_171_);
lean_dec_ref(v___f_170_);
lean_dec_ref(v___x_169_);
lean_dec_ref(v___x_168_);
lean_dec_ref(v___x_167_);
v_a_400_ = lean_ctor_get(v___x_398_, 0);
v_a_401_ = lean_ctor_get(v___x_398_, 1);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_398_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_inc(v_a_400_);
lean_dec(v___x_398_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_400_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_a_401_);
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
else
{
v___y_181_ = v___y_177_;
goto v___jp_180_;
}
v___jp_180_:
{
lean_object* v_quotContext_182_; lean_object* v_currMacroScope_183_; lean_object* v_ref_184_; lean_object* v_ref_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v_macroScope_207_; lean_object* v_traceMsgs_208_; lean_object* v_expandedMacroDecls_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_395_; 
v_quotContext_182_ = lean_ctor_get(v___y_176_, 1);
v_currMacroScope_183_ = lean_ctor_get(v___y_176_, 2);
v_ref_184_ = lean_ctor_get(v___y_176_, 5);
v_ref_185_ = l_Lean_replaceRef(v___x_179_, v_ref_184_);
v___x_186_ = l_Lean_SourceInfo_fromRef(v_ref_185_, v___x_166_);
lean_dec(v_ref_185_);
v___x_187_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__0));
lean_inc_ref_n(v___x_169_, 3);
lean_inc_ref_n(v___x_168_, 3);
lean_inc_ref_n(v___x_167_, 3);
v___x_188_ = l_Lean_Name_mkStr4(v___x_167_, v___x_168_, v___x_169_, v___x_187_);
v___x_189_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__1));
v___x_190_ = l_Lean_Name_mkStr4(v___x_167_, v___x_168_, v___x_169_, v___x_189_);
v___x_191_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__2));
lean_inc_n(v___x_186_, 6);
v___x_192_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_186_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
v___x_193_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4);
v___x_194_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7));
lean_inc(v_currMacroScope_183_);
lean_inc(v_quotContext_182_);
v___x_195_ = l_Lean_addMacroScope(v_quotContext_182_, v___x_194_, v_currMacroScope_183_);
v___x_196_ = lean_box(0);
v___x_197_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__11));
v___x_198_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_198_, 0, v___x_186_);
lean_ctor_set(v___x_198_, 1, v___x_193_);
lean_ctor_set(v___x_198_, 2, v___x_195_);
lean_ctor_set(v___x_198_, 3, v___x_197_);
lean_inc(v___x_190_);
v___x_199_ = l_Lean_Syntax_node2(v___x_186_, v___x_190_, v___x_192_, v___x_198_);
v___x_200_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_201_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__14));
v___x_202_ = l_Lean_Name_mkStr4(v___x_167_, v___x_168_, v___x_169_, v___x_201_);
v___x_203_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15));
v___x_204_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_186_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
lean_inc(v___x_202_);
v___x_205_ = l_Lean_Syntax_node1(v___x_186_, v___x_202_, v___x_204_);
lean_inc(v___x_179_);
lean_inc_n(v___x_205_, 2);
v___x_206_ = l_Lean_Syntax_node4(v___x_186_, v___x_200_, v___x_205_, v___x_205_, v___x_205_, v___x_179_);
v_macroScope_207_ = lean_ctor_get(v___y_181_, 0);
v_traceMsgs_208_ = lean_ctor_get(v___y_181_, 1);
v_expandedMacroDecls_209_ = lean_ctor_get(v___y_181_, 2);
v_isSharedCheck_395_ = !lean_is_exclusive(v___y_181_);
if (v_isSharedCheck_395_ == 0)
{
v___x_211_ = v___y_181_;
v_isShared_212_ = v_isSharedCheck_395_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_expandedMacroDecls_209_);
lean_inc(v_traceMsgs_208_);
lean_inc(v_macroScope_207_);
lean_dec(v___y_181_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_395_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_213_; lean_object* v___x_215_; 
v___x_213_ = lean_nat_add(v_macroScope_207_, v___x_164_);
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 0, v___x_213_);
v___x_215_ = v___x_211_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_213_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_traceMsgs_208_);
lean_ctor_set(v_reuseFailAlloc_394_, 2, v_expandedMacroDecls_209_);
v___x_215_ = v_reuseFailAlloc_394_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
lean_object* v___x_216_; 
lean_inc_ref(v___f_170_);
lean_inc_ref(v___y_176_);
lean_inc(v_ref_184_);
v___x_216_ = lean_apply_3(v___f_170_, v_ref_184_, v___y_176_, v___x_215_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; lean_object* v_a_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc_n(v_a_217_, 8);
v_a_218_ = lean_ctor_get(v___x_216_, 1);
lean_inc(v_a_218_);
lean_dec_ref(v___x_216_);
lean_inc(v___x_188_);
v___x_219_ = l_Lean_Syntax_node2(v___x_186_, v___x_188_, v___x_199_, v___x_206_);
v___x_220_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17));
lean_inc(v_quotContext_182_);
v___x_221_ = l_Lean_addMacroScope(v_quotContext_182_, v___x_220_, v_macroScope_207_);
v___x_222_ = l_Lean_mkIdentFrom(v___x_179_, v___x_221_, v___x_166_);
lean_dec(v___x_179_);
v___x_223_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__18));
lean_inc_ref_n(v___x_169_, 5);
lean_inc_ref_n(v___x_168_, 5);
lean_inc_ref_n(v___x_167_, 5);
v___x_224_ = l_Lean_Name_mkStr4(v___x_167_, v___x_168_, v___x_169_, v___x_223_);
v___x_225_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__19));
v___x_226_ = l_Lean_Name_mkStr4(v___x_167_, v___x_168_, v___x_169_, v___x_225_);
v___x_227_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__20));
v___x_228_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_228_, 0, v_a_217_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
v___x_229_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__21));
v___x_230_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_230_, 0, v_a_217_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = l_Lean_Syntax_node1(v_a_217_, v___x_200_, v___x_230_);
v___x_232_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__22));
v___x_233_ = l_Lean_Name_mkStr4(v___x_167_, v___x_168_, v___x_169_, v___x_232_);
v___x_234_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23));
v___x_235_ = l_Lean_Name_mkStr4(v___x_167_, v___x_168_, v___x_169_, v___x_234_);
v___x_236_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__24));
v___x_237_ = l_Lean_Name_mkStr4(v___x_167_, v___x_168_, v___x_169_, v___x_236_);
lean_inc(v___x_222_);
lean_inc(v___x_237_);
v___x_238_ = l_Lean_Syntax_node1(v_a_217_, v___x_237_, v___x_222_);
v___x_239_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25);
v___x_240_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_240_, 0, v_a_217_);
lean_ctor_set(v___x_240_, 1, v___x_200_);
lean_ctor_set(v___x_240_, 2, v___x_239_);
v___x_241_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__26));
v___x_242_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_242_, 0, v_a_217_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
lean_inc_ref_n(v___x_240_, 2);
v___x_243_ = l_Lean_Syntax_node5(v_a_217_, v___x_235_, v___x_238_, v___x_240_, v___x_240_, v___x_242_, v___x_219_);
lean_inc_ref(v___y_176_);
lean_inc(v_ref_184_);
v___x_244_ = lean_apply_3(v___f_170_, v_ref_184_, v___y_176_, v_a_218_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_375_; 
v_a_245_ = lean_ctor_get(v___x_244_, 0);
v_a_246_ = lean_ctor_get(v___x_244_, 1);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_375_ == 0)
{
v___x_248_ = v___x_244_;
v_isShared_249_ = v_isSharedCheck_375_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_inc(v_a_245_);
lean_dec(v___x_244_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_375_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_373_; 
lean_inc_n(v_a_217_, 2);
v___x_250_ = l_Lean_Syntax_node1(v_a_217_, v___x_233_, v___x_243_);
v___x_251_ = l_Lean_Syntax_node3(v_a_217_, v___x_226_, v___x_228_, v___x_231_, v___x_250_);
lean_inc_n(v___x_224_, 4);
v___x_252_ = l_Lean_Syntax_node2(v_a_217_, v___x_224_, v___x_251_, v___x_240_);
v___x_253_ = lean_array_push(v_fst_171_, v___x_252_);
v___x_254_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__27));
lean_inc_ref_n(v___x_169_, 11);
lean_inc_ref_n(v___x_168_, 11);
lean_inc_ref_n(v___x_167_, 13);
v___x_255_ = l_Lean_Name_mkStr4(v___x_167_, v___x_168_, v___x_169_, v___x_254_);
v___x_256_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28));
v___x_257_ = l_Lean_Name_mkStr4(v___x_167_, v___x_168_, v___x_169_, v___x_256_);
v___x_258_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29));
lean_inc_n(v_a_245_, 54);
v___x_259_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_259_, 0, v_a_245_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
v___x_260_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_260_, 0, v_a_245_);
lean_ctor_set(v___x_260_, 1, v___x_200_);
lean_ctor_set(v___x_260_, 2, v___x_239_);
v___x_261_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
v___x_262_ = l_Lean_Name_mkStr4(v___x_167_, v___x_168_, v___x_169_, v___x_261_);
v___x_263_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_263_, 0, v_a_245_);
lean_ctor_set(v___x_263_, 1, v___x_191_);
v___x_264_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__32, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__32_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__32);
v___x_265_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__35));
lean_inc_n(v_currMacroScope_183_, 5);
lean_inc_n(v_quotContext_182_, 5);
v___x_266_ = l_Lean_addMacroScope(v_quotContext_182_, v___x_265_, v_currMacroScope_183_);
v___x_267_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__37));
v___x_268_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_268_, 0, v_a_245_);
lean_ctor_set(v___x_268_, 1, v___x_264_);
lean_ctor_set(v___x_268_, 2, v___x_266_);
lean_ctor_set(v___x_268_, 3, v___x_267_);
v___x_269_ = l_Lean_Syntax_node2(v_a_245_, v___x_190_, v___x_263_, v___x_268_);
v___x_270_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_270_, 0, v_a_245_);
lean_ctor_set(v___x_270_, 1, v___x_203_);
v___x_271_ = l_Lean_Syntax_node1(v_a_245_, v___x_202_, v___x_270_);
lean_inc(v___x_222_);
lean_inc_n(v___x_271_, 2);
v___x_272_ = l_Lean_Syntax_node4(v_a_245_, v___x_200_, v___x_271_, v___x_271_, v___x_271_, v___x_222_);
lean_inc(v___x_188_);
v___x_273_ = l_Lean_Syntax_node2(v_a_245_, v___x_188_, v___x_269_, v___x_272_);
lean_inc_ref_n(v___x_260_, 9);
v___x_274_ = l_Lean_Syntax_node2(v_a_245_, v___x_262_, v___x_260_, v___x_273_);
v___x_275_ = l_Lean_Syntax_node1(v_a_245_, v___x_200_, v___x_274_);
v___x_276_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38));
v___x_277_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_277_, 0, v_a_245_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
v___x_278_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_279_ = l_Lean_Name_mkStr4(v___x_167_, v___x_168_, v___x_169_, v___x_278_);
v___x_280_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40));
v___x_281_ = l_Lean_Name_mkStr4(v___x_167_, v___x_168_, v___x_169_, v___x_280_);
v___x_282_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41));
v___x_283_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_283_, 0, v_a_245_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
v___x_284_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43);
v___x_285_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44));
v___x_286_ = l_Lean_addMacroScope(v_quotContext_182_, v___x_285_, v_currMacroScope_183_);
v___x_287_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__48));
v___x_288_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_288_, 0, v_a_245_);
lean_ctor_set(v___x_288_, 1, v___x_284_);
lean_ctor_set(v___x_288_, 2, v___x_286_);
lean_ctor_set(v___x_288_, 3, v___x_287_);
v___x_289_ = l_Lean_Syntax_node1(v_a_245_, v___x_200_, v___x_288_);
v___x_290_ = l_Lean_Syntax_node1(v_a_245_, v___x_200_, v___x_289_);
v___x_291_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49));
v___x_292_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_292_, 0, v_a_245_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_294_ = l_Lean_Name_mkStr4(v___x_167_, v___x_168_, v___x_169_, v___x_293_);
v___x_295_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__51));
v___x_296_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_296_, 0, v_a_245_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = l_Lean_Syntax_node1(v_a_245_, v___x_294_, v___x_296_);
v___x_298_ = l_Lean_Syntax_node2(v_a_245_, v___x_224_, v___x_297_, v___x_260_);
v___x_299_ = l_Lean_Syntax_node1(v_a_245_, v___x_200_, v___x_298_);
lean_inc_n(v___x_255_, 2);
v___x_300_ = l_Lean_Syntax_node1(v_a_245_, v___x_255_, v___x_299_);
lean_inc_ref(v___x_292_);
lean_inc_ref(v___x_283_);
lean_inc(v___x_281_);
v___x_301_ = l_Lean_Syntax_node4(v_a_245_, v___x_281_, v___x_283_, v___x_290_, v___x_292_, v___x_300_);
v___x_302_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53);
v___x_303_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54));
v___x_304_ = l_Lean_addMacroScope(v_quotContext_182_, v___x_303_, v_currMacroScope_183_);
v___x_305_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__57));
v___x_306_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_306_, 0, v_a_245_);
lean_ctor_set(v___x_306_, 1, v___x_302_);
lean_ctor_set(v___x_306_, 2, v___x_304_);
lean_ctor_set(v___x_306_, 3, v___x_305_);
v___x_307_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__58));
v___x_308_ = l_Lean_Name_mkStr4(v___x_167_, v___x_168_, v___x_169_, v___x_307_);
v___x_309_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__59));
v___x_310_ = l_Lean_Name_mkStr4(v___x_167_, v___x_168_, v___x_169_, v___x_309_);
v___x_311_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__60));
v___x_312_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_312_, 0, v_a_245_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v___x_313_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__62));
v___x_314_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__64, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__64_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__64);
v___x_315_ = lean_box(0);
v___x_316_ = l_Lean_addMacroScope(v_quotContext_182_, v___x_315_, v_currMacroScope_183_);
v___x_317_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65));
v___x_318_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66));
v___x_319_ = l_Lean_Name_mkStr3(v___x_167_, v___x_317_, v___x_318_);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
v___x_321_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67));
v___x_322_ = l_Lean_Name_mkStr2(v___x_167_, v___x_321_);
v___x_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
v___x_324_ = l_Lean_Name_mkStr3(v___x_167_, v___x_168_, v___x_169_);
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
v___x_326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v___x_196_);
v___x_327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_323_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
v___x_328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_320_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_329_, 0, v_a_245_);
lean_ctor_set(v___x_329_, 1, v___x_314_);
lean_ctor_set(v___x_329_, 2, v___x_316_);
lean_ctor_set(v___x_329_, 3, v___x_328_);
v___x_330_ = l_Lean_Syntax_node1(v_a_245_, v___x_313_, v___x_329_);
v___x_331_ = l_Lean_Syntax_node2(v_a_245_, v___x_310_, v___x_312_, v___x_330_);
v___x_332_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_332_, 0, v_a_245_);
lean_ctor_set(v___x_332_, 1, v___x_172_);
v___x_333_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69);
v___x_334_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70));
v___x_335_ = l_Lean_addMacroScope(v_quotContext_182_, v___x_334_, v_currMacroScope_183_);
v___x_336_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_336_, 0, v_a_245_);
lean_ctor_set(v___x_336_, 1, v___x_333_);
lean_ctor_set(v___x_336_, 2, v___x_335_);
lean_ctor_set(v___x_336_, 3, v___x_196_);
lean_inc_ref(v___x_336_);
v___x_337_ = l_Lean_Syntax_node1(v_a_245_, v___x_200_, v___x_336_);
v___x_338_ = l_Lean_Syntax_node3(v_a_245_, v___x_200_, v___x_178_, v___x_332_, v___x_337_);
v___x_339_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__71));
v___x_340_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_340_, 0, v_a_245_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
v___x_341_ = l_Lean_Syntax_node3(v_a_245_, v___x_308_, v___x_331_, v___x_338_, v___x_340_);
v___x_342_ = l_Lean_Syntax_node1(v_a_245_, v___x_200_, v___x_341_);
v___x_343_ = l_Lean_Syntax_node2(v_a_245_, v___x_188_, v___x_306_, v___x_342_);
v___x_344_ = l_Lean_Syntax_node1(v_a_245_, v___x_200_, v___x_343_);
v___x_345_ = l_Lean_Syntax_node1(v_a_245_, v___x_200_, v___x_344_);
v___x_346_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__72));
v___x_347_ = l_Lean_Name_mkStr4(v___x_167_, v___x_168_, v___x_169_, v___x_346_);
v___x_348_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__73));
v___x_349_ = l_Lean_Name_mkStr4(v___x_167_, v___x_168_, v___x_169_, v___x_348_);
v___x_350_ = l_Lean_Syntax_node1(v_a_245_, v___x_237_, v___x_222_);
v___x_351_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_351_, 0, v_a_245_);
lean_ctor_set(v___x_351_, 1, v___x_241_);
v___x_352_ = l_Lean_Syntax_node5(v_a_245_, v___x_349_, v___x_350_, v___x_260_, v___x_260_, v___x_351_, v___x_336_);
v___x_353_ = l_Lean_Syntax_node1(v_a_245_, v___x_347_, v___x_352_);
v___x_354_ = l_Lean_Syntax_node2(v_a_245_, v___x_224_, v___x_353_, v___x_260_);
v___x_355_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__74));
v___x_356_ = l_Lean_Name_mkStr4(v___x_167_, v___x_168_, v___x_169_, v___x_355_);
v___x_357_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75));
v___x_358_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_358_, 0, v_a_245_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
v___x_359_ = l_Lean_Syntax_node2(v_a_245_, v___x_356_, v___x_358_, v_snd_173_);
v___x_360_ = l_Lean_Syntax_node2(v_a_245_, v___x_224_, v___x_359_, v___x_260_);
v___x_361_ = l_Lean_Syntax_node2(v_a_245_, v___x_200_, v___x_354_, v___x_360_);
v___x_362_ = l_Lean_Syntax_node1(v_a_245_, v___x_255_, v___x_361_);
v___x_363_ = l_Lean_Syntax_node4(v_a_245_, v___x_281_, v___x_283_, v___x_345_, v___x_292_, v___x_362_);
v___x_364_ = l_Lean_Syntax_node2(v_a_245_, v___x_200_, v___x_301_, v___x_363_);
v___x_365_ = l_Lean_Syntax_node1(v_a_245_, v___x_279_, v___x_364_);
v___x_366_ = l_Lean_Syntax_node7(v_a_245_, v___x_257_, v___x_259_, v___x_260_, v___x_260_, v___x_260_, v___x_275_, v___x_277_, v___x_365_);
v___x_367_ = l_Lean_Syntax_node2(v_a_245_, v___x_224_, v___x_366_, v___x_260_);
v___x_368_ = l_Lean_Syntax_node1(v_a_245_, v___x_200_, v___x_367_);
v___x_369_ = l_Lean_Syntax_node1(v_a_245_, v___x_255_, v___x_368_);
v___x_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_253_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
v___x_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 0, v___x_371_);
v___x_373_ = v___x_248_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_371_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_a_246_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
else
{
lean_object* v_a_376_; lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_384_; 
lean_dec(v___x_243_);
lean_dec_ref(v___x_240_);
lean_dec(v___x_237_);
lean_dec(v___x_233_);
lean_dec(v___x_231_);
lean_dec_ref(v___x_228_);
lean_dec(v___x_226_);
lean_dec(v___x_224_);
lean_dec(v___x_222_);
lean_dec(v_a_217_);
lean_dec(v___x_202_);
lean_dec(v___x_190_);
lean_dec(v___x_188_);
lean_dec(v___x_178_);
lean_dec(v_snd_173_);
lean_dec_ref(v___x_172_);
lean_dec(v_fst_171_);
lean_dec_ref(v___x_169_);
lean_dec_ref(v___x_168_);
lean_dec_ref(v___x_167_);
v_a_376_ = lean_ctor_get(v___x_244_, 0);
v_a_377_ = lean_ctor_get(v___x_244_, 1);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_384_ == 0)
{
v___x_379_ = v___x_244_;
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_inc(v_a_376_);
lean_dec(v___x_244_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_376_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_a_377_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
else
{
lean_object* v_a_385_; lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
lean_dec(v_macroScope_207_);
lean_dec(v___x_206_);
lean_dec(v___x_202_);
lean_dec(v___x_199_);
lean_dec(v___x_190_);
lean_dec(v___x_188_);
lean_dec(v___x_186_);
lean_dec(v___x_179_);
lean_dec(v___x_178_);
lean_dec(v_snd_173_);
lean_dec_ref(v___x_172_);
lean_dec(v_fst_171_);
lean_dec_ref(v___f_170_);
lean_dec_ref(v___x_169_);
lean_dec_ref(v___x_168_);
lean_dec_ref(v___x_167_);
v_a_385_ = lean_ctor_get(v___x_216_, 0);
v_a_386_ = lean_ctor_get(v___x_216_, 1);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___x_216_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_inc(v_a_385_);
lean_dec(v___x_216_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_385_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v_a_386_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___boxed(lean_object* v___x_409_, lean_object* v___x_410_, lean_object* v___x_411_, lean_object* v___x_412_, lean_object* v___x_413_, lean_object* v___x_414_, lean_object* v___x_415_, lean_object* v___f_416_, lean_object* v_fst_417_, lean_object* v___x_418_, lean_object* v_snd_419_, lean_object* v_x_420_, lean_object* v_h_x3f_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
uint8_t v___x_145185__boxed_424_; lean_object* v_res_425_; 
v___x_145185__boxed_424_ = lean_unbox(v___x_412_);
v_res_425_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(v___x_409_, v___x_410_, v___x_411_, v___x_145185__boxed_424_, v___x_413_, v___x_414_, v___x_415_, v___f_416_, v_fst_417_, v___x_418_, v_snd_419_, v_x_420_, v_h_x3f_421_, v___y_422_, v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v_h_x3f_421_);
lean_dec(v___x_411_);
lean_dec(v___x_410_);
lean_dec(v___x_409_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0(uint8_t v___x_426_, lean_object* v_____do__lift_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = l_Lean_SourceInfo_fromRef(v_____do__lift_427_, v___x_426_);
v___x_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
lean_ctor_set(v___x_431_, 1, v___y_429_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0___boxed(lean_object* v___x_432_, lean_object* v_____do__lift_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
uint8_t v___x_145784__boxed_436_; lean_object* v_res_437_; 
v___x_145784__boxed_436_ = lean_unbox(v___x_432_);
v_res_437_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0(v___x_145784__boxed_436_, v_____do__lift_433_, v___y_434_, v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v_____do__lift_433_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(uint8_t v___x_448_, lean_object* v_a_449_, lean_object* v_b_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v_array_453_; lean_object* v_start_454_; lean_object* v_stop_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_549_; 
v_array_453_ = lean_ctor_get(v_a_449_, 0);
v_start_454_ = lean_ctor_get(v_a_449_, 1);
v_stop_455_ = lean_ctor_get(v_a_449_, 2);
v_isSharedCheck_549_ = !lean_is_exclusive(v_a_449_);
if (v_isSharedCheck_549_ == 0)
{
v___x_457_ = v_a_449_;
v_isShared_458_ = v_isSharedCheck_549_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_stop_455_);
lean_inc(v_start_454_);
lean_inc(v_array_453_);
lean_dec(v_a_449_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_549_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
uint8_t v___x_459_; 
v___x_459_ = lean_nat_dec_lt(v_start_454_, v_stop_455_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; 
lean_del_object(v___x_457_);
lean_dec(v_stop_455_);
lean_dec(v_start_454_);
lean_dec_ref(v_array_453_);
v___x_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_460_, 0, v_b_450_);
lean_ctor_set(v___x_460_, 1, v___y_452_);
return v___x_460_;
}
else
{
lean_object* v_fst_461_; lean_object* v_snd_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_548_; 
v_fst_461_ = lean_ctor_get(v_b_450_, 0);
v_snd_462_ = lean_ctor_get(v_b_450_, 1);
v_isSharedCheck_548_ = !lean_is_exclusive(v_b_450_);
if (v_isSharedCheck_548_ == 0)
{
v___x_464_ = v_b_450_;
v_isShared_465_ = v_isSharedCheck_548_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_snd_462_);
lean_inc(v_fst_461_);
lean_dec(v_b_450_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_548_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_466_ = lean_unsigned_to_nat(1u);
v___x_467_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0));
v___x_468_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1));
v___x_469_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2));
v___x_470_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
v___x_471_ = lean_nat_add(v_start_454_, v___x_466_);
lean_inc_ref(v_array_453_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 1, v___x_471_);
v___x_473_ = v___x_457_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_array_453_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v___x_471_);
lean_ctor_set(v_reuseFailAlloc_547_, 2, v_stop_455_);
v___x_473_ = v_reuseFailAlloc_547_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
lean_object* v___y_475_; lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_499_ = lean_array_fget(v_array_453_, v_start_454_);
lean_dec(v_start_454_);
lean_dec_ref(v_array_453_);
lean_inc(v___x_499_);
v___x_500_ = l_Lean_Syntax_isOfKind(v___x_499_, v___x_470_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; 
lean_dec(v___x_499_);
v___x_501_ = l_Lean_Macro_throwUnsupported___redArg(v___y_452_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v___x_504_; 
v_a_502_ = lean_ctor_get(v___x_501_, 1);
lean_inc(v_a_502_);
lean_dec_ref(v___x_501_);
if (v_isShared_465_ == 0)
{
v___x_504_ = v___x_464_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_fst_461_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v_snd_462_);
v___x_504_ = v_reuseFailAlloc_506_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
v_a_449_ = v___x_473_;
v_b_450_ = v___x_504_;
v___y_452_ = v_a_502_;
goto _start;
}
}
else
{
lean_object* v_a_507_; lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
lean_dec_ref(v___x_473_);
lean_del_object(v___x_464_);
lean_dec(v_snd_462_);
lean_dec(v_fst_461_);
v_a_507_ = lean_ctor_get(v___x_501_, 0);
v_a_508_ = lean_ctor_get(v___x_501_, 1);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_501_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_inc(v_a_507_);
lean_dec(v___x_501_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_507_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_a_508_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
else
{
lean_object* v___x_516_; lean_object* v___f_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_516_ = lean_box(v___x_448_);
v___f_517_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_517_, 0, v___x_516_);
v___x_518_ = lean_unsigned_to_nat(3u);
v___x_519_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__5));
v___x_520_ = lean_unsigned_to_nat(0u);
v___x_521_ = l_Lean_Syntax_getArg(v___x_499_, v___x_520_);
v___x_522_ = l_Lean_Syntax_isNone(v___x_521_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_523_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_521_);
v___x_524_ = l_Lean_Syntax_matchesNull(v___x_521_, v___x_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; 
lean_dec(v___x_521_);
lean_dec_ref(v___f_517_);
lean_dec(v___x_499_);
v___x_525_ = l_Lean_Macro_throwUnsupported___redArg(v___y_452_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v___x_528_; 
v_a_526_ = lean_ctor_get(v___x_525_, 1);
lean_inc(v_a_526_);
lean_dec_ref(v___x_525_);
if (v_isShared_465_ == 0)
{
v___x_528_ = v___x_464_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_fst_461_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_snd_462_);
v___x_528_ = v_reuseFailAlloc_530_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
v_a_449_ = v___x_473_;
v_b_450_ = v___x_528_;
v___y_452_ = v_a_526_;
goto _start;
}
}
else
{
lean_object* v_a_531_; lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
lean_dec_ref(v___x_473_);
lean_del_object(v___x_464_);
lean_dec(v_snd_462_);
lean_dec(v_fst_461_);
v_a_531_ = lean_ctor_get(v___x_525_, 0);
v_a_532_ = lean_ctor_get(v___x_525_, 1);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_525_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_inc(v_a_531_);
lean_dec(v___x_525_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_531_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
else
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
lean_del_object(v___x_464_);
v___x_540_ = l_Lean_Syntax_getArg(v___x_521_, v___x_520_);
lean_dec(v___x_521_);
v___x_541_ = lean_box(0);
v___x_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_540_);
v___x_543_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(v___x_499_, v___x_466_, v___x_518_, v___x_448_, v___x_467_, v___x_468_, v___x_469_, v___f_517_, v_fst_461_, v___x_519_, v_snd_462_, v___x_541_, v___x_542_, v___y_451_, v___y_452_);
lean_dec_ref(v___x_542_);
lean_dec(v___x_499_);
v___y_475_ = v___x_543_;
goto v___jp_474_;
}
}
else
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
lean_dec(v___x_521_);
lean_del_object(v___x_464_);
v___x_544_ = lean_box(0);
v___x_545_ = lean_box(0);
v___x_546_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(v___x_499_, v___x_466_, v___x_518_, v___x_448_, v___x_467_, v___x_468_, v___x_469_, v___f_517_, v_fst_461_, v___x_519_, v_snd_462_, v___x_544_, v___x_545_, v___y_451_, v___y_452_);
lean_dec(v___x_499_);
v___y_475_ = v___x_546_;
goto v___jp_474_;
}
}
v___jp_474_:
{
if (lean_obj_tag(v___y_475_) == 0)
{
lean_object* v_a_476_; 
v_a_476_ = lean_ctor_get(v___y_475_, 0);
lean_inc(v_a_476_);
if (lean_obj_tag(v_a_476_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_485_; 
lean_dec_ref(v___x_473_);
v_a_477_ = lean_ctor_get(v___y_475_, 1);
v_isSharedCheck_485_ = !lean_is_exclusive(v___y_475_);
if (v_isSharedCheck_485_ == 0)
{
lean_object* v_unused_486_; 
v_unused_486_ = lean_ctor_get(v___y_475_, 0);
lean_dec(v_unused_486_);
v___x_479_ = v___y_475_;
v_isShared_480_ = v_isSharedCheck_485_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___y_475_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_485_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v_a_481_; lean_object* v___x_483_; 
v_a_481_ = lean_ctor_get(v_a_476_, 0);
lean_inc(v_a_481_);
lean_dec_ref(v_a_476_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v_a_481_);
v___x_483_ = v___x_479_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_a_481_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_a_477_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
else
{
lean_object* v_a_487_; lean_object* v_a_488_; 
v_a_487_ = lean_ctor_get(v___y_475_, 1);
lean_inc(v_a_487_);
lean_dec_ref(v___y_475_);
v_a_488_ = lean_ctor_get(v_a_476_, 0);
lean_inc(v_a_488_);
lean_dec_ref(v_a_476_);
v_a_449_ = v___x_473_;
v_b_450_ = v_a_488_;
v___y_452_ = v_a_487_;
goto _start;
}
}
else
{
lean_object* v_a_490_; lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_dec_ref(v___x_473_);
v_a_490_ = lean_ctor_get(v___y_475_, 0);
v_a_491_ = lean_ctor_get(v___y_475_, 1);
v_isSharedCheck_498_ = !lean_is_exclusive(v___y_475_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___y_475_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_inc(v_a_490_);
lean_dec(v___y_475_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_490_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___boxed(lean_object* v___x_550_, lean_object* v_a_551_, lean_object* v_b_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
uint8_t v___x_145820__boxed_555_; lean_object* v_res_556_; 
v___x_145820__boxed_555_ = lean_unbox(v___x_550_);
v_res_556_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_145820__boxed_555_, v_a_551_, v_b_552_, v___y_553_, v___y_554_);
lean_dec_ref(v___y_553_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor(lean_object* v_stx_613_, lean_object* v_a_614_, lean_object* v_a_615_){
_start:
{
lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_616_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
lean_inc(v_stx_613_);
v___x_617_ = l_Lean_Syntax_isOfKind(v_stx_613_, v___x_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; 
lean_dec(v_stx_613_);
v___x_618_ = l_Lean_Macro_throwUnsupported___redArg(v_a_615_);
return v___x_618_;
}
else
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_619_ = lean_unsigned_to_nat(0u);
v___x_620_ = lean_unsigned_to_nat(1u);
v___x_621_ = l_Lean_Syntax_getArg(v_stx_613_, v___x_620_);
lean_inc(v___x_621_);
v___x_622_ = l_Lean_Syntax_matchesNull(v___x_621_, v___x_620_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v_decls_655_; lean_object* v_decls_656_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v_x_661_; lean_object* v_body_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___x_700_; lean_object* v___x_701_; uint8_t v___x_702_; 
v___x_623_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
v_decls_655_ = l_Lean_Syntax_getArgs(v___x_621_);
lean_dec(v___x_621_);
v_decls_656_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_655_);
lean_dec_ref(v_decls_655_);
v___x_700_ = lean_box(0);
v___x_701_ = lean_array_get(v___x_700_, v_decls_656_, v___x_619_);
lean_inc(v___x_701_);
v___x_702_ = l_Lean_Syntax_isOfKind(v___x_701_, v___x_623_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; 
lean_dec(v___x_701_);
lean_dec_ref(v_decls_656_);
lean_dec(v_stx_613_);
v___x_703_ = l_Lean_Macro_throwUnsupported___redArg(v_a_615_);
return v___x_703_;
}
else
{
lean_object* v___x_704_; lean_object* v_body_705_; lean_object* v_h_x3f_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_704_ = lean_unsigned_to_nat(3u);
v_body_705_ = l_Lean_Syntax_getArg(v_stx_613_, v___x_704_);
lean_dec(v_stx_613_);
v___x_770_ = l_Lean_Syntax_getArg(v___x_701_, v___x_619_);
v___x_771_ = l_Lean_Syntax_isNone(v___x_770_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_772_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_770_);
v___x_773_ = l_Lean_Syntax_matchesNull(v___x_770_, v___x_772_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; 
lean_dec(v___x_770_);
lean_dec(v_body_705_);
lean_dec(v___x_701_);
lean_dec_ref(v_decls_656_);
v___x_774_ = l_Lean_Macro_throwUnsupported___redArg(v_a_615_);
return v___x_774_;
}
else
{
lean_object* v_h_x3f_775_; lean_object* v___x_776_; 
v_h_x3f_775_ = l_Lean_Syntax_getArg(v___x_770_, v___x_619_);
lean_dec(v___x_770_);
v___x_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_776_, 0, v_h_x3f_775_);
v_h_x3f_707_ = v___x_776_;
v___y_708_ = v_a_614_;
v___y_709_ = v_a_615_;
goto v___jp_706_;
}
}
else
{
lean_object* v___x_777_; 
lean_dec(v___x_770_);
v___x_777_ = lean_box(0);
v_h_x3f_707_ = v___x_777_;
v___y_708_ = v_a_614_;
v___y_709_ = v_a_615_;
goto v___jp_706_;
}
v___jp_706_:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v_doElems_712_; uint8_t v___x_713_; 
v___x_710_ = l_Lean_Syntax_getArg(v___x_701_, v___x_620_);
v___x_711_ = l_Lean_Syntax_getArg(v___x_701_, v___x_704_);
lean_dec(v___x_701_);
v_doElems_712_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_713_ = l_Lean_Syntax_isIdent(v___x_710_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_714_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_710_);
v___x_715_ = l_Lean_Syntax_isOfKind(v___x_710_, v___x_714_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; 
v___x_716_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_710_, v___x_715_, v___y_708_, v___y_709_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v_a_718_; lean_object* v_ref_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc_n(v_a_717_, 2);
v_a_718_ = lean_ctor_get(v___x_716_, 1);
lean_inc(v_a_718_);
lean_dec_ref(v___x_716_);
v_ref_719_ = lean_ctor_get(v___y_708_, 5);
v___x_720_ = l_Lean_SourceInfo_fromRef(v_ref_719_, v___x_715_);
v___x_721_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_722_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_723_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_724_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_725_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29));
lean_inc_n(v___x_720_, 15);
v___x_726_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_720_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
v___x_727_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25);
v___x_728_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_728_, 0, v___x_720_);
lean_ctor_set(v___x_728_, 1, v___x_722_);
lean_ctor_set(v___x_728_, 2, v___x_727_);
v___x_729_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_728_, 4);
v___x_730_ = l_Lean_Syntax_node2(v___x_720_, v___x_729_, v___x_728_, v_a_717_);
v___x_731_ = l_Lean_Syntax_node1(v___x_720_, v___x_722_, v___x_730_);
v___x_732_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38));
v___x_733_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_720_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___x_734_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_735_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_736_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41));
v___x_737_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_720_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
v___x_738_ = l_Lean_Syntax_node1(v___x_720_, v___x_722_, v___x_710_);
v___x_739_ = l_Lean_Syntax_node1(v___x_720_, v___x_722_, v___x_738_);
v___x_740_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49));
v___x_741_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_720_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = l_Lean_Syntax_node4(v___x_720_, v___x_735_, v___x_737_, v___x_739_, v___x_741_, v_body_705_);
v___x_743_ = l_Lean_Syntax_node1(v___x_720_, v___x_722_, v___x_742_);
v___x_744_ = l_Lean_Syntax_node1(v___x_720_, v___x_734_, v___x_743_);
v___x_745_ = l_Lean_Syntax_node7(v___x_720_, v___x_724_, v___x_726_, v___x_728_, v___x_728_, v___x_728_, v___x_731_, v___x_733_, v___x_744_);
v___x_746_ = l_Lean_Syntax_node2(v___x_720_, v___x_723_, v___x_745_, v___x_728_);
v___x_747_ = l_Lean_Syntax_node1(v___x_720_, v___x_722_, v___x_746_);
v___x_748_ = l_Lean_Syntax_node1(v___x_720_, v___x_721_, v___x_747_);
v___y_658_ = v_h_x3f_707_;
v___y_659_ = v___x_711_;
v___y_660_ = v_doElems_712_;
v_x_661_ = v_a_717_;
v_body_662_ = v___x_748_;
v___y_663_ = v___y_708_;
v___y_664_ = v_a_718_;
goto v___jp_657_;
}
else
{
lean_object* v_a_749_; lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
lean_dec(v___x_711_);
lean_dec(v___x_710_);
lean_dec(v_h_x3f_707_);
lean_dec(v_body_705_);
lean_dec_ref(v_decls_656_);
v_a_749_ = lean_ctor_get(v___x_716_, 0);
v_a_750_ = lean_ctor_get(v___x_716_, 1);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___x_716_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_inc(v_a_749_);
lean_dec(v___x_716_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_749_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_a_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
else
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_710_, v___x_713_, v___y_708_, v___y_709_);
lean_dec(v___x_710_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v_a_760_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_a_759_);
v_a_760_ = lean_ctor_get(v___x_758_, 1);
lean_inc(v_a_760_);
lean_dec_ref(v___x_758_);
v___y_658_ = v_h_x3f_707_;
v___y_659_ = v___x_711_;
v___y_660_ = v_doElems_712_;
v_x_661_ = v_a_759_;
v_body_662_ = v_body_705_;
v___y_663_ = v___y_708_;
v___y_664_ = v_a_760_;
goto v___jp_657_;
}
else
{
lean_object* v_a_761_; lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
lean_dec(v___x_711_);
lean_dec(v_h_x3f_707_);
lean_dec(v_body_705_);
lean_dec_ref(v_decls_656_);
v_a_761_ = lean_ctor_get(v___x_758_, 0);
v_a_762_ = lean_ctor_get(v___x_758_, 1);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_758_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_inc(v_a_761_);
lean_dec(v___x_758_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_761_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
}
else
{
v___y_658_ = v_h_x3f_707_;
v___y_659_ = v___x_711_;
v___y_660_ = v_doElems_712_;
v_x_661_ = v___x_710_;
v_body_662_ = v_body_705_;
v___y_663_ = v___y_708_;
v___y_664_ = v___y_709_;
goto v___jp_657_;
}
}
}
v___jp_624_:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
lean_inc_ref_n(v___y_632_, 3);
v___x_636_ = l_Array_append___redArg(v___y_632_, v___y_635_);
lean_dec_ref(v___y_635_);
lean_inc_n(v___y_630_, 4);
lean_inc_n(v___y_634_, 10);
v___x_637_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_637_, 0, v___y_634_);
lean_ctor_set(v___x_637_, 1, v___y_630_);
lean_ctor_set(v___x_637_, 2, v___x_636_);
v___x_638_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_639_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_639_, 0, v___y_634_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
v___x_640_ = l_Lean_Syntax_node4(v___y_634_, v___x_623_, v___x_637_, v___y_633_, v___x_639_, v___y_631_);
v___x_641_ = l_Lean_Syntax_node1(v___y_634_, v___y_630_, v___x_640_);
v___x_642_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75));
v___x_643_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_643_, 0, v___y_634_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
lean_inc_ref(v___x_643_);
v___x_644_ = l_Lean_Syntax_node4(v___y_634_, v___x_616_, v___y_628_, v___x_641_, v___x_643_, v___y_625_);
v___x_645_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_645_, 0, v___y_634_);
lean_ctor_set(v___x_645_, 1, v___y_630_);
lean_ctor_set(v___x_645_, 2, v___y_632_);
lean_inc(v___y_626_);
v___x_646_ = l_Lean_Syntax_node2(v___y_634_, v___y_626_, v___x_644_, v___x_645_);
v___x_647_ = lean_array_push(v___y_629_, v___x_646_);
v___x_648_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_649_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_650_ = l_Array_append___redArg(v___y_632_, v___x_647_);
lean_dec_ref(v___x_647_);
v___x_651_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_651_, 0, v___y_634_);
lean_ctor_set(v___x_651_, 1, v___y_630_);
lean_ctor_set(v___x_651_, 2, v___x_650_);
v___x_652_ = l_Lean_Syntax_node1(v___y_634_, v___x_649_, v___x_651_);
v___x_653_ = l_Lean_Syntax_node2(v___y_634_, v___x_648_, v___x_643_, v___x_652_);
v___x_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
lean_ctor_set(v___x_654_, 1, v___y_627_);
return v___x_654_;
}
v___jp_657_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_665_ = lean_array_get_size(v_decls_656_);
v___x_666_ = l_Array_toSubarray___redArg(v_decls_656_, v___x_620_, v___x_665_);
lean_inc_ref(v___y_660_);
v___x_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_667_, 0, v___y_660_);
lean_ctor_set(v___x_667_, 1, v_body_662_);
v___x_668_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_622_, v___x_666_, v___x_667_, v___y_663_, v___y_664_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v_a_670_; lean_object* v_fst_671_; lean_object* v_snd_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_690_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
v_a_670_ = lean_ctor_get(v___x_668_, 1);
lean_inc(v_a_670_);
lean_dec_ref(v___x_668_);
v_fst_671_ = lean_ctor_get(v_a_669_, 0);
v_snd_672_ = lean_ctor_get(v_a_669_, 1);
v_isSharedCheck_690_ = !lean_is_exclusive(v_a_669_);
if (v_isSharedCheck_690_ == 0)
{
v___x_674_ = v_a_669_;
v_isShared_675_ = v_isSharedCheck_690_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_snd_672_);
lean_inc(v_fst_671_);
lean_dec(v_a_669_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_690_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v_ref_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_681_; 
v_ref_676_ = lean_ctor_get(v___y_663_, 5);
v___x_677_ = l_Lean_SourceInfo_fromRef(v_ref_676_, v___x_622_);
v___x_678_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_679_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
lean_inc(v___x_677_);
if (v_isShared_675_ == 0)
{
lean_ctor_set_tag(v___x_674_, 2);
lean_ctor_set(v___x_674_, 1, v___x_679_);
lean_ctor_set(v___x_674_, 0, v___x_677_);
v___x_681_ = v___x_674_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_677_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v___x_679_);
v___x_681_ = v_reuseFailAlloc_689_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_683_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25);
if (lean_obj_tag(v___y_658_) == 1)
{
lean_object* v_val_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v_val_684_ = lean_ctor_get(v___y_658_, 0);
lean_inc(v_val_684_);
lean_dec_ref(v___y_658_);
v___x_685_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
lean_inc(v___x_677_);
v___x_686_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_677_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
v___x_687_ = l_Array_mkArray2___redArg(v_val_684_, v___x_686_);
v___y_625_ = v_snd_672_;
v___y_626_ = v___x_678_;
v___y_627_ = v_a_670_;
v___y_628_ = v___x_681_;
v___y_629_ = v_fst_671_;
v___y_630_ = v___x_682_;
v___y_631_ = v___y_659_;
v___y_632_ = v___x_683_;
v___y_633_ = v_x_661_;
v___y_634_ = v___x_677_;
v___y_635_ = v___x_687_;
goto v___jp_624_;
}
else
{
lean_object* v___x_688_; 
lean_dec(v___y_658_);
v___x_688_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
v___y_625_ = v_snd_672_;
v___y_626_ = v___x_678_;
v___y_627_ = v_a_670_;
v___y_628_ = v___x_681_;
v___y_629_ = v_fst_671_;
v___y_630_ = v___x_682_;
v___y_631_ = v___y_659_;
v___y_632_ = v___x_683_;
v___y_633_ = v_x_661_;
v___y_634_ = v___x_677_;
v___y_635_ = v___x_688_;
goto v___jp_624_;
}
}
}
}
else
{
lean_object* v_a_691_; lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
lean_dec(v_x_661_);
lean_dec(v___y_659_);
lean_dec(v___y_658_);
v_a_691_ = lean_ctor_get(v___x_668_, 0);
v_a_692_ = lean_ctor_get(v___x_668_, 1);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_699_ == 0)
{
v___x_694_ = v___x_668_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_inc(v_a_691_);
lean_dec(v___x_668_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_691_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_a_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
}
else
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; uint8_t v___y_847_; lean_object* v_x_848_; lean_object* v_body_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; uint8_t v___y_892_; lean_object* v_h_x3f_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; uint8_t v___x_1010_; 
v___x_778_ = l_Lean_Syntax_getArg(v___x_621_, v___x_619_);
v___x_779_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
lean_inc(v___x_778_);
v___x_1010_ = l_Lean_Syntax_isOfKind(v___x_778_, v___x_779_);
if (v___x_1010_ == 0)
{
lean_object* v_decls_1011_; lean_object* v_decls_1012_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v_x_1017_; lean_object* v_body_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___x_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; 
lean_dec(v___x_778_);
v_decls_1011_ = l_Lean_Syntax_getArgs(v___x_621_);
lean_dec(v___x_621_);
v_decls_1012_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_1011_);
lean_dec_ref(v_decls_1011_);
v___x_1056_ = lean_box(0);
v___x_1057_ = lean_array_get(v___x_1056_, v_decls_1012_, v___x_619_);
lean_inc(v___x_1057_);
v___x_1058_ = l_Lean_Syntax_isOfKind(v___x_1057_, v___x_779_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; 
lean_dec(v___x_1057_);
lean_dec_ref(v_decls_1012_);
lean_dec(v_stx_613_);
v___x_1059_ = l_Lean_Macro_throwUnsupported___redArg(v_a_615_);
return v___x_1059_;
}
else
{
lean_object* v___x_1060_; lean_object* v_body_1061_; lean_object* v_h_x3f_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___x_1126_; uint8_t v___x_1127_; 
v___x_1060_ = lean_unsigned_to_nat(3u);
v_body_1061_ = l_Lean_Syntax_getArg(v_stx_613_, v___x_1060_);
lean_dec(v_stx_613_);
v___x_1126_ = l_Lean_Syntax_getArg(v___x_1057_, v___x_619_);
v___x_1127_ = l_Lean_Syntax_isNone(v___x_1126_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1128_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1126_);
v___x_1129_ = l_Lean_Syntax_matchesNull(v___x_1126_, v___x_1128_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; 
lean_dec(v___x_1126_);
lean_dec(v_body_1061_);
lean_dec(v___x_1057_);
lean_dec_ref(v_decls_1012_);
v___x_1130_ = l_Lean_Macro_throwUnsupported___redArg(v_a_615_);
return v___x_1130_;
}
else
{
lean_object* v_h_x3f_1131_; lean_object* v___x_1132_; 
v_h_x3f_1131_ = l_Lean_Syntax_getArg(v___x_1126_, v___x_619_);
lean_dec(v___x_1126_);
v___x_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1132_, 0, v_h_x3f_1131_);
v_h_x3f_1063_ = v___x_1132_;
v___y_1064_ = v_a_614_;
v___y_1065_ = v_a_615_;
goto v___jp_1062_;
}
}
else
{
lean_object* v___x_1133_; 
lean_dec(v___x_1126_);
v___x_1133_ = lean_box(0);
v_h_x3f_1063_ = v___x_1133_;
v___y_1064_ = v_a_614_;
v___y_1065_ = v_a_615_;
goto v___jp_1062_;
}
v___jp_1062_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v_doElems_1068_; uint8_t v___x_1069_; 
v___x_1066_ = l_Lean_Syntax_getArg(v___x_1057_, v___x_620_);
v___x_1067_ = l_Lean_Syntax_getArg(v___x_1057_, v___x_1060_);
lean_dec(v___x_1057_);
v_doElems_1068_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_1069_ = l_Lean_Syntax_isIdent(v___x_1066_);
if (v___x_1069_ == 0)
{
lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1070_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_1066_);
v___x_1071_ = l_Lean_Syntax_isOfKind(v___x_1066_, v___x_1070_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1066_, v___x_1071_, v___y_1064_, v___y_1065_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v_a_1074_; lean_object* v_ref_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc_n(v_a_1073_, 2);
v_a_1074_ = lean_ctor_get(v___x_1072_, 1);
lean_inc(v_a_1074_);
lean_dec_ref(v___x_1072_);
v_ref_1075_ = lean_ctor_get(v___y_1064_, 5);
v___x_1076_ = l_Lean_SourceInfo_fromRef(v_ref_1075_, v___x_1071_);
v___x_1077_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_1078_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1079_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_1080_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_1081_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29));
lean_inc_n(v___x_1076_, 15);
v___x_1082_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1076_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25);
v___x_1084_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1076_);
lean_ctor_set(v___x_1084_, 1, v___x_1078_);
lean_ctor_set(v___x_1084_, 2, v___x_1083_);
v___x_1085_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_1084_, 4);
v___x_1086_ = l_Lean_Syntax_node2(v___x_1076_, v___x_1085_, v___x_1084_, v_a_1073_);
v___x_1087_ = l_Lean_Syntax_node1(v___x_1076_, v___x_1078_, v___x_1086_);
v___x_1088_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38));
v___x_1089_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1076_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_1091_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_1092_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41));
v___x_1093_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1076_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = l_Lean_Syntax_node1(v___x_1076_, v___x_1078_, v___x_1066_);
v___x_1095_ = l_Lean_Syntax_node1(v___x_1076_, v___x_1078_, v___x_1094_);
v___x_1096_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49));
v___x_1097_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1076_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = l_Lean_Syntax_node4(v___x_1076_, v___x_1091_, v___x_1093_, v___x_1095_, v___x_1097_, v_body_1061_);
v___x_1099_ = l_Lean_Syntax_node1(v___x_1076_, v___x_1078_, v___x_1098_);
v___x_1100_ = l_Lean_Syntax_node1(v___x_1076_, v___x_1090_, v___x_1099_);
v___x_1101_ = l_Lean_Syntax_node7(v___x_1076_, v___x_1080_, v___x_1082_, v___x_1084_, v___x_1084_, v___x_1084_, v___x_1087_, v___x_1089_, v___x_1100_);
v___x_1102_ = l_Lean_Syntax_node2(v___x_1076_, v___x_1079_, v___x_1101_, v___x_1084_);
v___x_1103_ = l_Lean_Syntax_node1(v___x_1076_, v___x_1078_, v___x_1102_);
v___x_1104_ = l_Lean_Syntax_node1(v___x_1076_, v___x_1077_, v___x_1103_);
v___y_1014_ = v_h_x3f_1063_;
v___y_1015_ = v___x_1067_;
v___y_1016_ = v_doElems_1068_;
v_x_1017_ = v_a_1073_;
v_body_1018_ = v___x_1104_;
v___y_1019_ = v___y_1064_;
v___y_1020_ = v_a_1074_;
goto v___jp_1013_;
}
else
{
lean_object* v_a_1105_; lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
lean_dec(v___x_1067_);
lean_dec(v___x_1066_);
lean_dec(v_h_x3f_1063_);
lean_dec(v_body_1061_);
lean_dec_ref(v_decls_1012_);
v_a_1105_ = lean_ctor_get(v___x_1072_, 0);
v_a_1106_ = lean_ctor_get(v___x_1072_, 1);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1072_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_inc(v_a_1105_);
lean_dec(v___x_1072_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1105_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
else
{
lean_object* v___x_1114_; 
v___x_1114_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1066_, v___x_1069_, v___y_1064_, v___y_1065_);
lean_dec(v___x_1066_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v_a_1116_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1115_);
v_a_1116_ = lean_ctor_get(v___x_1114_, 1);
lean_inc(v_a_1116_);
lean_dec_ref(v___x_1114_);
v___y_1014_ = v_h_x3f_1063_;
v___y_1015_ = v___x_1067_;
v___y_1016_ = v_doElems_1068_;
v_x_1017_ = v_a_1115_;
v_body_1018_ = v_body_1061_;
v___y_1019_ = v___y_1064_;
v___y_1020_ = v_a_1116_;
goto v___jp_1013_;
}
else
{
lean_object* v_a_1117_; lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
lean_dec(v___x_1067_);
lean_dec(v_h_x3f_1063_);
lean_dec(v_body_1061_);
lean_dec_ref(v_decls_1012_);
v_a_1117_ = lean_ctor_get(v___x_1114_, 0);
v_a_1118_ = lean_ctor_get(v___x_1114_, 1);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1114_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_inc(v_a_1117_);
lean_dec(v___x_1114_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1117_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
}
else
{
v___y_1014_ = v_h_x3f_1063_;
v___y_1015_ = v___x_1067_;
v___y_1016_ = v_doElems_1068_;
v_x_1017_ = v___x_1066_;
v_body_1018_ = v_body_1061_;
v___y_1019_ = v___y_1064_;
v___y_1020_ = v___y_1065_;
goto v___jp_1013_;
}
}
}
v___jp_1013_:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1021_ = lean_array_get_size(v_decls_1012_);
v___x_1022_ = l_Array_toSubarray___redArg(v_decls_1012_, v___x_620_, v___x_1021_);
lean_inc_ref(v___y_1016_);
v___x_1023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___y_1016_);
lean_ctor_set(v___x_1023_, 1, v_body_1018_);
v___x_1024_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_1010_, v___x_1022_, v___x_1023_, v___y_1019_, v___y_1020_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v_a_1026_; lean_object* v_fst_1027_; lean_object* v_snd_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1046_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_a_1025_);
v_a_1026_ = lean_ctor_get(v___x_1024_, 1);
lean_inc(v_a_1026_);
lean_dec_ref(v___x_1024_);
v_fst_1027_ = lean_ctor_get(v_a_1025_, 0);
v_snd_1028_ = lean_ctor_get(v_a_1025_, 1);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_a_1025_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1030_ = v_a_1025_;
v_isShared_1031_ = v_isSharedCheck_1046_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_snd_1028_);
lean_inc(v_fst_1027_);
lean_dec(v_a_1025_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1046_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v_ref_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1037_; 
v_ref_1032_ = lean_ctor_get(v___y_1019_, 5);
v___x_1033_ = l_Lean_SourceInfo_fromRef(v_ref_1032_, v___x_1010_);
v___x_1034_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_1035_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
lean_inc(v___x_1033_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set_tag(v___x_1030_, 2);
lean_ctor_set(v___x_1030_, 1, v___x_1035_);
lean_ctor_set(v___x_1030_, 0, v___x_1033_);
v___x_1037_ = v___x_1030_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1033_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1039_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25);
if (lean_obj_tag(v___y_1014_) == 1)
{
lean_object* v_val_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v_val_1040_ = lean_ctor_get(v___y_1014_, 0);
lean_inc(v_val_1040_);
lean_dec_ref(v___y_1014_);
v___x_1041_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
lean_inc(v___x_1033_);
v___x_1042_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1033_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = l_Array_mkArray2___redArg(v_val_1040_, v___x_1042_);
v___y_980_ = v___x_1038_;
v___y_981_ = v___y_1015_;
v___y_982_ = v___x_1037_;
v___y_983_ = v_x_1017_;
v___y_984_ = v___x_1039_;
v___y_985_ = v_a_1026_;
v___y_986_ = v_fst_1027_;
v___y_987_ = v___x_1034_;
v___y_988_ = v___x_1033_;
v___y_989_ = v_snd_1028_;
v___y_990_ = v___x_1043_;
goto v___jp_979_;
}
else
{
lean_object* v___x_1044_; 
lean_dec(v___y_1014_);
v___x_1044_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
v___y_980_ = v___x_1038_;
v___y_981_ = v___y_1015_;
v___y_982_ = v___x_1037_;
v___y_983_ = v_x_1017_;
v___y_984_ = v___x_1039_;
v___y_985_ = v_a_1026_;
v___y_986_ = v_fst_1027_;
v___y_987_ = v___x_1034_;
v___y_988_ = v___x_1033_;
v___y_989_ = v_snd_1028_;
v___y_990_ = v___x_1044_;
goto v___jp_979_;
}
}
}
}
else
{
lean_object* v_a_1047_; lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
lean_dec(v_x_1017_);
lean_dec(v___y_1015_);
lean_dec(v___y_1014_);
v_a_1047_ = lean_ctor_get(v___x_1024_, 0);
v_a_1048_ = lean_ctor_get(v___x_1024_, 1);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_1024_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_inc(v_a_1047_);
lean_dec(v___x_1024_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1047_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
}
else
{
lean_object* v___x_1134_; uint8_t v___x_1135_; 
v___x_1134_ = l_Lean_Syntax_getArg(v___x_778_, v___x_619_);
v___x_1135_ = l_Lean_Syntax_isNone(v___x_1134_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; uint8_t v___x_1137_; 
v___x_1136_ = lean_unsigned_to_nat(2u);
v___x_1137_ = l_Lean_Syntax_matchesNull(v___x_1134_, v___x_1136_);
if (v___x_1137_ == 0)
{
lean_object* v_decls_1138_; lean_object* v_decls_1139_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v_x_1144_; lean_object* v_body_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___x_1183_; lean_object* v___x_1184_; uint8_t v___x_1185_; 
lean_dec(v___x_778_);
v_decls_1138_ = l_Lean_Syntax_getArgs(v___x_621_);
lean_dec(v___x_621_);
v_decls_1139_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_1138_);
lean_dec_ref(v_decls_1138_);
v___x_1183_ = lean_box(0);
v___x_1184_ = lean_array_get(v___x_1183_, v_decls_1139_, v___x_619_);
lean_inc(v___x_1184_);
v___x_1185_ = l_Lean_Syntax_isOfKind(v___x_1184_, v___x_779_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; 
lean_dec(v___x_1184_);
lean_dec_ref(v_decls_1139_);
lean_dec(v_stx_613_);
v___x_1186_ = l_Lean_Macro_throwUnsupported___redArg(v_a_615_);
return v___x_1186_;
}
else
{
lean_object* v___x_1187_; lean_object* v_body_1188_; lean_object* v_h_x3f_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___x_1253_; uint8_t v___x_1254_; 
v___x_1187_ = lean_unsigned_to_nat(3u);
v_body_1188_ = l_Lean_Syntax_getArg(v_stx_613_, v___x_1187_);
lean_dec(v_stx_613_);
v___x_1253_ = l_Lean_Syntax_getArg(v___x_1184_, v___x_619_);
v___x_1254_ = l_Lean_Syntax_isNone(v___x_1253_);
if (v___x_1254_ == 0)
{
uint8_t v___x_1255_; 
lean_inc(v___x_1253_);
v___x_1255_ = l_Lean_Syntax_matchesNull(v___x_1253_, v___x_1136_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; 
lean_dec(v___x_1253_);
lean_dec(v_body_1188_);
lean_dec(v___x_1184_);
lean_dec_ref(v_decls_1139_);
v___x_1256_ = l_Lean_Macro_throwUnsupported___redArg(v_a_615_);
return v___x_1256_;
}
else
{
lean_object* v_h_x3f_1257_; lean_object* v___x_1258_; 
v_h_x3f_1257_ = l_Lean_Syntax_getArg(v___x_1253_, v___x_619_);
lean_dec(v___x_1253_);
v___x_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1258_, 0, v_h_x3f_1257_);
v_h_x3f_1190_ = v___x_1258_;
v___y_1191_ = v_a_614_;
v___y_1192_ = v_a_615_;
goto v___jp_1189_;
}
}
else
{
lean_object* v___x_1259_; 
lean_dec(v___x_1253_);
v___x_1259_ = lean_box(0);
v_h_x3f_1190_ = v___x_1259_;
v___y_1191_ = v_a_614_;
v___y_1192_ = v_a_615_;
goto v___jp_1189_;
}
v___jp_1189_:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v_doElems_1195_; uint8_t v___x_1196_; 
v___x_1193_ = l_Lean_Syntax_getArg(v___x_1184_, v___x_620_);
v___x_1194_ = l_Lean_Syntax_getArg(v___x_1184_, v___x_1187_);
lean_dec(v___x_1184_);
v_doElems_1195_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_1196_ = l_Lean_Syntax_isIdent(v___x_1193_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; uint8_t v___x_1198_; 
v___x_1197_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_1193_);
v___x_1198_ = l_Lean_Syntax_isOfKind(v___x_1193_, v___x_1197_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; 
v___x_1199_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1193_, v___x_1198_, v___y_1191_, v___y_1192_);
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_object* v_a_1200_; lean_object* v_a_1201_; lean_object* v_ref_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
lean_inc_n(v_a_1200_, 2);
v_a_1201_ = lean_ctor_get(v___x_1199_, 1);
lean_inc(v_a_1201_);
lean_dec_ref(v___x_1199_);
v_ref_1202_ = lean_ctor_get(v___y_1191_, 5);
v___x_1203_ = l_Lean_SourceInfo_fromRef(v_ref_1202_, v___x_1198_);
v___x_1204_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_1205_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1206_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_1207_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_1208_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29));
lean_inc_n(v___x_1203_, 15);
v___x_1209_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1203_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
v___x_1210_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25);
v___x_1211_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1203_);
lean_ctor_set(v___x_1211_, 1, v___x_1205_);
lean_ctor_set(v___x_1211_, 2, v___x_1210_);
v___x_1212_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_1211_, 4);
v___x_1213_ = l_Lean_Syntax_node2(v___x_1203_, v___x_1212_, v___x_1211_, v_a_1200_);
v___x_1214_ = l_Lean_Syntax_node1(v___x_1203_, v___x_1205_, v___x_1213_);
v___x_1215_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38));
v___x_1216_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1203_);
lean_ctor_set(v___x_1216_, 1, v___x_1215_);
v___x_1217_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_1218_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_1219_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41));
v___x_1220_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1203_);
lean_ctor_set(v___x_1220_, 1, v___x_1219_);
v___x_1221_ = l_Lean_Syntax_node1(v___x_1203_, v___x_1205_, v___x_1193_);
v___x_1222_ = l_Lean_Syntax_node1(v___x_1203_, v___x_1205_, v___x_1221_);
v___x_1223_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49));
v___x_1224_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1203_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v___x_1225_ = l_Lean_Syntax_node4(v___x_1203_, v___x_1218_, v___x_1220_, v___x_1222_, v___x_1224_, v_body_1188_);
v___x_1226_ = l_Lean_Syntax_node1(v___x_1203_, v___x_1205_, v___x_1225_);
v___x_1227_ = l_Lean_Syntax_node1(v___x_1203_, v___x_1217_, v___x_1226_);
v___x_1228_ = l_Lean_Syntax_node7(v___x_1203_, v___x_1207_, v___x_1209_, v___x_1211_, v___x_1211_, v___x_1211_, v___x_1214_, v___x_1216_, v___x_1227_);
v___x_1229_ = l_Lean_Syntax_node2(v___x_1203_, v___x_1206_, v___x_1228_, v___x_1211_);
v___x_1230_ = l_Lean_Syntax_node1(v___x_1203_, v___x_1205_, v___x_1229_);
v___x_1231_ = l_Lean_Syntax_node1(v___x_1203_, v___x_1204_, v___x_1230_);
v___y_1141_ = v___x_1194_;
v___y_1142_ = v_h_x3f_1190_;
v___y_1143_ = v_doElems_1195_;
v_x_1144_ = v_a_1200_;
v_body_1145_ = v___x_1231_;
v___y_1146_ = v___y_1191_;
v___y_1147_ = v_a_1201_;
goto v___jp_1140_;
}
else
{
lean_object* v_a_1232_; lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_dec(v___x_1194_);
lean_dec(v___x_1193_);
lean_dec(v_h_x3f_1190_);
lean_dec(v_body_1188_);
lean_dec_ref(v_decls_1139_);
v_a_1232_ = lean_ctor_get(v___x_1199_, 0);
v_a_1233_ = lean_ctor_get(v___x_1199_, 1);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1199_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_inc(v_a_1232_);
lean_dec(v___x_1199_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1232_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
else
{
lean_object* v___x_1241_; 
v___x_1241_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1193_, v___x_1196_, v___y_1191_, v___y_1192_);
lean_dec(v___x_1193_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v_a_1243_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1242_);
v_a_1243_ = lean_ctor_get(v___x_1241_, 1);
lean_inc(v_a_1243_);
lean_dec_ref(v___x_1241_);
v___y_1141_ = v___x_1194_;
v___y_1142_ = v_h_x3f_1190_;
v___y_1143_ = v_doElems_1195_;
v_x_1144_ = v_a_1242_;
v_body_1145_ = v_body_1188_;
v___y_1146_ = v___y_1191_;
v___y_1147_ = v_a_1243_;
goto v___jp_1140_;
}
else
{
lean_object* v_a_1244_; lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_dec(v___x_1194_);
lean_dec(v_h_x3f_1190_);
lean_dec(v_body_1188_);
lean_dec_ref(v_decls_1139_);
v_a_1244_ = lean_ctor_get(v___x_1241_, 0);
v_a_1245_ = lean_ctor_get(v___x_1241_, 1);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1241_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_inc(v_a_1244_);
lean_dec(v___x_1241_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1244_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
}
else
{
v___y_1141_ = v___x_1194_;
v___y_1142_ = v_h_x3f_1190_;
v___y_1143_ = v_doElems_1195_;
v_x_1144_ = v___x_1193_;
v_body_1145_ = v_body_1188_;
v___y_1146_ = v___y_1191_;
v___y_1147_ = v___y_1192_;
goto v___jp_1140_;
}
}
}
v___jp_1140_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1148_ = lean_array_get_size(v_decls_1139_);
v___x_1149_ = l_Array_toSubarray___redArg(v_decls_1139_, v___x_620_, v___x_1148_);
lean_inc_ref(v___y_1143_);
v___x_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___y_1143_);
lean_ctor_set(v___x_1150_, 1, v_body_1145_);
v___x_1151_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_1137_, v___x_1149_, v___x_1150_, v___y_1146_, v___y_1147_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_a_1152_; lean_object* v_a_1153_; lean_object* v_fst_1154_; lean_object* v_snd_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1173_; 
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_a_1152_);
v_a_1153_ = lean_ctor_get(v___x_1151_, 1);
lean_inc(v_a_1153_);
lean_dec_ref(v___x_1151_);
v_fst_1154_ = lean_ctor_get(v_a_1152_, 0);
v_snd_1155_ = lean_ctor_get(v_a_1152_, 1);
v_isSharedCheck_1173_ = !lean_is_exclusive(v_a_1152_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1157_ = v_a_1152_;
v_isShared_1158_ = v_isSharedCheck_1173_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_snd_1155_);
lean_inc(v_fst_1154_);
lean_dec(v_a_1152_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1173_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v_ref_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1164_; 
v_ref_1159_ = lean_ctor_get(v___y_1146_, 5);
v___x_1160_ = l_Lean_SourceInfo_fromRef(v_ref_1159_, v___x_1137_);
v___x_1161_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_1162_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
lean_inc(v___x_1160_);
if (v_isShared_1158_ == 0)
{
lean_ctor_set_tag(v___x_1157_, 2);
lean_ctor_set(v___x_1157_, 1, v___x_1162_);
lean_ctor_set(v___x_1157_, 0, v___x_1160_);
v___x_1164_ = v___x_1157_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1160_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v___x_1162_);
v___x_1164_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1166_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25);
if (lean_obj_tag(v___y_1142_) == 1)
{
lean_object* v_val_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v_val_1167_ = lean_ctor_get(v___y_1142_, 0);
lean_inc(v_val_1167_);
lean_dec_ref(v___y_1142_);
v___x_1168_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
lean_inc(v___x_1160_);
v___x_1169_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1160_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
v___x_1170_ = l_Array_mkArray2___redArg(v_val_1167_, v___x_1169_);
v___y_781_ = v___x_1161_;
v___y_782_ = v___y_1141_;
v___y_783_ = v___x_1164_;
v___y_784_ = v_snd_1155_;
v___y_785_ = v_a_1153_;
v___y_786_ = v___x_1165_;
v___y_787_ = v___x_1160_;
v___y_788_ = v_x_1144_;
v___y_789_ = v_fst_1154_;
v___y_790_ = v___x_1166_;
v___y_791_ = v___x_1170_;
goto v___jp_780_;
}
else
{
lean_object* v___x_1171_; 
lean_dec(v___y_1142_);
v___x_1171_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
v___y_781_ = v___x_1161_;
v___y_782_ = v___y_1141_;
v___y_783_ = v___x_1164_;
v___y_784_ = v_snd_1155_;
v___y_785_ = v_a_1153_;
v___y_786_ = v___x_1165_;
v___y_787_ = v___x_1160_;
v___y_788_ = v_x_1144_;
v___y_789_ = v_fst_1154_;
v___y_790_ = v___x_1166_;
v___y_791_ = v___x_1171_;
goto v___jp_780_;
}
}
}
}
else
{
lean_object* v_a_1174_; lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
lean_dec(v_x_1144_);
lean_dec(v___y_1142_);
lean_dec(v___y_1141_);
v_a_1174_ = lean_ctor_get(v___x_1151_, 0);
v_a_1175_ = lean_ctor_get(v___x_1151_, 1);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1177_ = v___x_1151_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_inc(v_a_1174_);
lean_dec(v___x_1151_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1174_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_a_1175_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
else
{
v___y_957_ = v_a_614_;
v___y_958_ = v_a_615_;
goto v___jp_956_;
}
}
else
{
lean_dec(v___x_1134_);
v___y_957_ = v_a_614_;
v___y_958_ = v_a_615_;
goto v___jp_956_;
}
}
v___jp_780_:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
lean_inc_ref_n(v___y_790_, 3);
v___x_792_ = l_Array_append___redArg(v___y_790_, v___y_791_);
lean_dec_ref(v___y_791_);
lean_inc_n(v___y_786_, 4);
lean_inc_n(v___y_787_, 10);
v___x_793_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_793_, 0, v___y_787_);
lean_ctor_set(v___x_793_, 1, v___y_786_);
lean_ctor_set(v___x_793_, 2, v___x_792_);
v___x_794_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_795_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_795_, 0, v___y_787_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
v___x_796_ = l_Lean_Syntax_node4(v___y_787_, v___x_779_, v___x_793_, v___y_788_, v___x_795_, v___y_782_);
v___x_797_ = l_Lean_Syntax_node1(v___y_787_, v___y_786_, v___x_796_);
v___x_798_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75));
v___x_799_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_799_, 0, v___y_787_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
lean_inc_ref(v___x_799_);
v___x_800_ = l_Lean_Syntax_node4(v___y_787_, v___x_616_, v___y_783_, v___x_797_, v___x_799_, v___y_784_);
v___x_801_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_801_, 0, v___y_787_);
lean_ctor_set(v___x_801_, 1, v___y_786_);
lean_ctor_set(v___x_801_, 2, v___y_790_);
lean_inc(v___y_781_);
v___x_802_ = l_Lean_Syntax_node2(v___y_787_, v___y_781_, v___x_800_, v___x_801_);
v___x_803_ = lean_array_push(v___y_789_, v___x_802_);
v___x_804_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_805_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_806_ = l_Array_append___redArg(v___y_790_, v___x_803_);
lean_dec_ref(v___x_803_);
v___x_807_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_807_, 0, v___y_787_);
lean_ctor_set(v___x_807_, 1, v___y_786_);
lean_ctor_set(v___x_807_, 2, v___x_806_);
v___x_808_ = l_Lean_Syntax_node1(v___y_787_, v___x_805_, v___x_807_);
v___x_809_ = l_Lean_Syntax_node2(v___y_787_, v___x_804_, v___x_799_, v___x_808_);
v___x_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
lean_ctor_set(v___x_810_, 1, v___y_785_);
return v___x_810_;
}
v___jp_811_:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
lean_inc_ref_n(v___y_821_, 3);
v___x_823_ = l_Array_append___redArg(v___y_821_, v___y_822_);
lean_dec_ref(v___y_822_);
lean_inc_n(v___y_814_, 4);
lean_inc_n(v___y_818_, 10);
v___x_824_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_824_, 0, v___y_818_);
lean_ctor_set(v___x_824_, 1, v___y_814_);
lean_ctor_set(v___x_824_, 2, v___x_823_);
v___x_825_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_826_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_826_, 0, v___y_818_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
v___x_827_ = l_Lean_Syntax_node4(v___y_818_, v___x_779_, v___x_824_, v___y_813_, v___x_826_, v___y_815_);
v___x_828_ = l_Lean_Syntax_node1(v___y_818_, v___y_814_, v___x_827_);
v___x_829_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75));
v___x_830_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_830_, 0, v___y_818_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
lean_inc_ref(v___x_830_);
v___x_831_ = l_Lean_Syntax_node4(v___y_818_, v___x_616_, v___y_817_, v___x_828_, v___x_830_, v___y_819_);
v___x_832_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_832_, 0, v___y_818_);
lean_ctor_set(v___x_832_, 1, v___y_814_);
lean_ctor_set(v___x_832_, 2, v___y_821_);
lean_inc(v___y_820_);
v___x_833_ = l_Lean_Syntax_node2(v___y_818_, v___y_820_, v___x_831_, v___x_832_);
v___x_834_ = lean_array_push(v___y_812_, v___x_833_);
v___x_835_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_836_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_837_ = l_Array_append___redArg(v___y_821_, v___x_834_);
lean_dec_ref(v___x_834_);
v___x_838_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_838_, 0, v___y_818_);
lean_ctor_set(v___x_838_, 1, v___y_814_);
lean_ctor_set(v___x_838_, 2, v___x_837_);
v___x_839_ = l_Lean_Syntax_node1(v___y_818_, v___x_836_, v___x_838_);
v___x_840_ = l_Lean_Syntax_node2(v___y_818_, v___x_835_, v___x_830_, v___x_839_);
v___x_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
lean_ctor_set(v___x_841_, 1, v___y_816_);
return v___x_841_;
}
v___jp_842_:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_852_ = lean_array_get_size(v___y_844_);
v___x_853_ = l_Array_toSubarray___redArg(v___y_844_, v___x_620_, v___x_852_);
lean_inc_ref(v___y_843_);
v___x_854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_854_, 0, v___y_843_);
lean_ctor_set(v___x_854_, 1, v_body_849_);
v___x_855_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___y_847_, v___x_853_, v___x_854_, v___y_850_, v___y_851_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v_a_857_; lean_object* v_fst_858_; lean_object* v_snd_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_877_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_856_);
v_a_857_ = lean_ctor_get(v___x_855_, 1);
lean_inc(v_a_857_);
lean_dec_ref(v___x_855_);
v_fst_858_ = lean_ctor_get(v_a_856_, 0);
v_snd_859_ = lean_ctor_get(v_a_856_, 1);
v_isSharedCheck_877_ = !lean_is_exclusive(v_a_856_);
if (v_isSharedCheck_877_ == 0)
{
v___x_861_ = v_a_856_;
v_isShared_862_ = v_isSharedCheck_877_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_snd_859_);
lean_inc(v_fst_858_);
lean_dec(v_a_856_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_877_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v_ref_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_868_; 
v_ref_863_ = lean_ctor_get(v___y_850_, 5);
v___x_864_ = l_Lean_SourceInfo_fromRef(v_ref_863_, v___y_847_);
v___x_865_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_866_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
lean_inc(v___x_864_);
if (v_isShared_862_ == 0)
{
lean_ctor_set_tag(v___x_861_, 2);
lean_ctor_set(v___x_861_, 1, v___x_866_);
lean_ctor_set(v___x_861_, 0, v___x_864_);
v___x_868_ = v___x_861_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_864_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v___x_866_);
v___x_868_ = v_reuseFailAlloc_876_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_870_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25);
if (lean_obj_tag(v___y_845_) == 1)
{
lean_object* v_val_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v_val_871_ = lean_ctor_get(v___y_845_, 0);
lean_inc(v_val_871_);
lean_dec_ref(v___y_845_);
v___x_872_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
lean_inc(v___x_864_);
v___x_873_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_864_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = l_Array_mkArray2___redArg(v_val_871_, v___x_873_);
v___y_812_ = v_fst_858_;
v___y_813_ = v_x_848_;
v___y_814_ = v___x_869_;
v___y_815_ = v___y_846_;
v___y_816_ = v_a_857_;
v___y_817_ = v___x_868_;
v___y_818_ = v___x_864_;
v___y_819_ = v_snd_859_;
v___y_820_ = v___x_865_;
v___y_821_ = v___x_870_;
v___y_822_ = v___x_874_;
goto v___jp_811_;
}
else
{
lean_object* v___x_875_; 
lean_dec(v___y_845_);
v___x_875_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
v___y_812_ = v_fst_858_;
v___y_813_ = v_x_848_;
v___y_814_ = v___x_869_;
v___y_815_ = v___y_846_;
v___y_816_ = v_a_857_;
v___y_817_ = v___x_868_;
v___y_818_ = v___x_864_;
v___y_819_ = v_snd_859_;
v___y_820_ = v___x_865_;
v___y_821_ = v___x_870_;
v___y_822_ = v___x_875_;
goto v___jp_811_;
}
}
}
}
else
{
lean_object* v_a_878_; lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
lean_dec(v_x_848_);
lean_dec(v___y_846_);
lean_dec(v___y_845_);
v_a_878_ = lean_ctor_get(v___x_855_, 0);
v_a_879_ = lean_ctor_get(v___x_855_, 1);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_855_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_inc(v_a_878_);
lean_dec(v___x_855_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_878_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
v___jp_887_:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v_doElems_898_; uint8_t v___x_899_; 
v___x_896_ = l_Lean_Syntax_getArg(v___y_888_, v___x_620_);
v___x_897_ = l_Lean_Syntax_getArg(v___y_888_, v___y_889_);
lean_dec(v___y_888_);
v_doElems_898_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_899_ = l_Lean_Syntax_isIdent(v___x_896_);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; uint8_t v___x_901_; 
v___x_900_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_896_);
v___x_901_ = l_Lean_Syntax_isOfKind(v___x_896_, v___x_900_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; 
v___x_902_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_896_, v___y_892_, v___y_894_, v___y_895_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v_a_904_; lean_object* v_ref_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc_n(v_a_903_, 2);
v_a_904_ = lean_ctor_get(v___x_902_, 1);
lean_inc(v_a_904_);
lean_dec_ref(v___x_902_);
v_ref_905_ = lean_ctor_get(v___y_894_, 5);
v___x_906_ = l_Lean_SourceInfo_fromRef(v_ref_905_, v___y_892_);
v___x_907_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_908_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_909_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_910_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_911_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29));
lean_inc_n(v___x_906_, 15);
v___x_912_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_906_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
v___x_913_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25);
v___x_914_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_914_, 0, v___x_906_);
lean_ctor_set(v___x_914_, 1, v___x_908_);
lean_ctor_set(v___x_914_, 2, v___x_913_);
v___x_915_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_914_, 4);
v___x_916_ = l_Lean_Syntax_node2(v___x_906_, v___x_915_, v___x_914_, v_a_903_);
v___x_917_ = l_Lean_Syntax_node1(v___x_906_, v___x_908_, v___x_916_);
v___x_918_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38));
v___x_919_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_906_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_921_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_922_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41));
v___x_923_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_906_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
v___x_924_ = l_Lean_Syntax_node1(v___x_906_, v___x_908_, v___x_896_);
v___x_925_ = l_Lean_Syntax_node1(v___x_906_, v___x_908_, v___x_924_);
v___x_926_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49));
v___x_927_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_906_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = l_Lean_Syntax_node4(v___x_906_, v___x_921_, v___x_923_, v___x_925_, v___x_927_, v___y_891_);
v___x_929_ = l_Lean_Syntax_node1(v___x_906_, v___x_908_, v___x_928_);
v___x_930_ = l_Lean_Syntax_node1(v___x_906_, v___x_920_, v___x_929_);
v___x_931_ = l_Lean_Syntax_node7(v___x_906_, v___x_910_, v___x_912_, v___x_914_, v___x_914_, v___x_914_, v___x_917_, v___x_919_, v___x_930_);
v___x_932_ = l_Lean_Syntax_node2(v___x_906_, v___x_909_, v___x_931_, v___x_914_);
v___x_933_ = l_Lean_Syntax_node1(v___x_906_, v___x_908_, v___x_932_);
v___x_934_ = l_Lean_Syntax_node1(v___x_906_, v___x_907_, v___x_933_);
v___y_843_ = v_doElems_898_;
v___y_844_ = v___y_890_;
v___y_845_ = v_h_x3f_893_;
v___y_846_ = v___x_897_;
v___y_847_ = v___y_892_;
v_x_848_ = v_a_903_;
v_body_849_ = v___x_934_;
v___y_850_ = v___y_894_;
v___y_851_ = v_a_904_;
goto v___jp_842_;
}
else
{
lean_object* v_a_935_; lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
lean_dec(v___x_897_);
lean_dec(v___x_896_);
lean_dec(v_h_x3f_893_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
v_a_935_ = lean_ctor_get(v___x_902_, 0);
v_a_936_ = lean_ctor_get(v___x_902_, 1);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_943_ == 0)
{
v___x_938_ = v___x_902_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_inc(v_a_935_);
lean_dec(v___x_902_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_935_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_a_936_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
else
{
lean_object* v___x_944_; 
v___x_944_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_896_, v___y_892_, v___y_894_, v___y_895_);
lean_dec(v___x_896_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v_a_945_; lean_object* v_a_946_; 
v_a_945_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_a_945_);
v_a_946_ = lean_ctor_get(v___x_944_, 1);
lean_inc(v_a_946_);
lean_dec_ref(v___x_944_);
v___y_843_ = v_doElems_898_;
v___y_844_ = v___y_890_;
v___y_845_ = v_h_x3f_893_;
v___y_846_ = v___x_897_;
v___y_847_ = v___y_892_;
v_x_848_ = v_a_945_;
v_body_849_ = v___y_891_;
v___y_850_ = v___y_894_;
v___y_851_ = v_a_946_;
goto v___jp_842_;
}
else
{
lean_object* v_a_947_; lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec(v___x_897_);
lean_dec(v_h_x3f_893_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
v_a_947_ = lean_ctor_get(v___x_944_, 0);
v_a_948_ = lean_ctor_get(v___x_944_, 1);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_944_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_inc(v_a_947_);
lean_dec(v___x_944_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_947_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
else
{
v___y_843_ = v_doElems_898_;
v___y_844_ = v___y_890_;
v___y_845_ = v_h_x3f_893_;
v___y_846_ = v___x_897_;
v___y_847_ = v___y_892_;
v_x_848_ = v___x_896_;
v_body_849_ = v___y_891_;
v___y_850_ = v___y_894_;
v___y_851_ = v___y_895_;
goto v___jp_842_;
}
}
v___jp_956_:
{
lean_object* v___x_959_; lean_object* v___x_960_; uint8_t v___x_961_; 
v___x_959_ = l_Lean_Syntax_getArg(v___x_778_, v___x_620_);
lean_dec(v___x_778_);
v___x_960_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__16));
v___x_961_ = l_Lean_Syntax_isOfKind(v___x_959_, v___x_960_);
if (v___x_961_ == 0)
{
lean_object* v_decls_962_; lean_object* v_decls_963_; lean_object* v___x_964_; lean_object* v___x_965_; uint8_t v___x_966_; 
v_decls_962_ = l_Lean_Syntax_getArgs(v___x_621_);
lean_dec(v___x_621_);
v_decls_963_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_962_);
lean_dec_ref(v_decls_962_);
v___x_964_ = lean_box(0);
v___x_965_ = lean_array_get(v___x_964_, v_decls_963_, v___x_619_);
lean_inc(v___x_965_);
v___x_966_ = l_Lean_Syntax_isOfKind(v___x_965_, v___x_779_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; 
lean_dec(v___x_965_);
lean_dec_ref(v_decls_963_);
lean_dec(v_stx_613_);
v___x_967_ = l_Lean_Macro_throwUnsupported___redArg(v___y_958_);
return v___x_967_;
}
else
{
lean_object* v___x_968_; lean_object* v_body_969_; lean_object* v___x_970_; uint8_t v___x_971_; 
v___x_968_ = lean_unsigned_to_nat(3u);
v_body_969_ = l_Lean_Syntax_getArg(v_stx_613_, v___x_968_);
lean_dec(v_stx_613_);
v___x_970_ = l_Lean_Syntax_getArg(v___x_965_, v___x_619_);
v___x_971_ = l_Lean_Syntax_isNone(v___x_970_);
if (v___x_971_ == 0)
{
lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_972_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_970_);
v___x_973_ = l_Lean_Syntax_matchesNull(v___x_970_, v___x_972_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; 
lean_dec(v___x_970_);
lean_dec(v_body_969_);
lean_dec(v___x_965_);
lean_dec_ref(v_decls_963_);
v___x_974_ = l_Lean_Macro_throwUnsupported___redArg(v___y_958_);
return v___x_974_;
}
else
{
lean_object* v_h_x3f_975_; lean_object* v___x_976_; 
v_h_x3f_975_ = l_Lean_Syntax_getArg(v___x_970_, v___x_619_);
lean_dec(v___x_970_);
v___x_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_976_, 0, v_h_x3f_975_);
v___y_888_ = v___x_965_;
v___y_889_ = v___x_968_;
v___y_890_ = v_decls_963_;
v___y_891_ = v_body_969_;
v___y_892_ = v___x_961_;
v_h_x3f_893_ = v___x_976_;
v___y_894_ = v___y_957_;
v___y_895_ = v___y_958_;
goto v___jp_887_;
}
}
else
{
lean_object* v___x_977_; 
lean_dec(v___x_970_);
v___x_977_ = lean_box(0);
v___y_888_ = v___x_965_;
v___y_889_ = v___x_968_;
v___y_890_ = v_decls_963_;
v___y_891_ = v_body_969_;
v___y_892_ = v___x_961_;
v_h_x3f_893_ = v___x_977_;
v___y_894_ = v___y_957_;
v___y_895_ = v___y_958_;
goto v___jp_887_;
}
}
}
else
{
lean_object* v___x_978_; 
lean_dec(v___x_621_);
lean_dec(v_stx_613_);
v___x_978_ = l_Lean_Macro_throwUnsupported___redArg(v___y_958_);
return v___x_978_;
}
}
v___jp_979_:
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
lean_inc_ref_n(v___y_984_, 3);
v___x_991_ = l_Array_append___redArg(v___y_984_, v___y_990_);
lean_dec_ref(v___y_990_);
lean_inc_n(v___y_980_, 4);
lean_inc_n(v___y_988_, 10);
v___x_992_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_992_, 0, v___y_988_);
lean_ctor_set(v___x_992_, 1, v___y_980_);
lean_ctor_set(v___x_992_, 2, v___x_991_);
v___x_993_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_994_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_994_, 0, v___y_988_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = l_Lean_Syntax_node4(v___y_988_, v___x_779_, v___x_992_, v___y_983_, v___x_994_, v___y_981_);
v___x_996_ = l_Lean_Syntax_node1(v___y_988_, v___y_980_, v___x_995_);
v___x_997_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75));
v___x_998_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_998_, 0, v___y_988_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
lean_inc_ref(v___x_998_);
v___x_999_ = l_Lean_Syntax_node4(v___y_988_, v___x_616_, v___y_982_, v___x_996_, v___x_998_, v___y_989_);
v___x_1000_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1000_, 0, v___y_988_);
lean_ctor_set(v___x_1000_, 1, v___y_980_);
lean_ctor_set(v___x_1000_, 2, v___y_984_);
lean_inc(v___y_987_);
v___x_1001_ = l_Lean_Syntax_node2(v___y_988_, v___y_987_, v___x_999_, v___x_1000_);
v___x_1002_ = lean_array_push(v___y_986_, v___x_1001_);
v___x_1003_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_1004_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_1005_ = l_Array_append___redArg(v___y_984_, v___x_1002_);
lean_dec_ref(v___x_1002_);
v___x_1006_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1006_, 0, v___y_988_);
lean_ctor_set(v___x_1006_, 1, v___y_980_);
lean_ctor_set(v___x_1006_, 2, v___x_1005_);
v___x_1007_ = l_Lean_Syntax_node1(v___y_988_, v___x_1004_, v___x_1006_);
v___x_1008_ = l_Lean_Syntax_node2(v___y_988_, v___x_1003_, v___x_998_, v___x_1007_);
v___x_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
lean_ctor_set(v___x_1009_, 1, v___y_985_);
return v___x_1009_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor___boxed(lean_object* v_stx_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Lean_Elab_Do_expandDoFor(v_stx_1260_, v_a_1261_, v_a_1262_);
lean_dec_ref(v_a_1261_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0(uint8_t v___x_1264_, lean_object* v_inst_1265_, lean_object* v_R_1266_, lean_object* v_a_1267_, lean_object* v_b_1268_, lean_object* v_c_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_1264_, v_a_1267_, v_b_1268_, v___y_1270_, v___y_1271_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___boxed(lean_object* v___x_1273_, lean_object* v_inst_1274_, lean_object* v_R_1275_, lean_object* v_a_1276_, lean_object* v_b_1277_, lean_object* v_c_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
uint8_t v___x_147670__boxed_1281_; lean_object* v_res_1282_; 
v___x_147670__boxed_1281_ = lean_unbox(v___x_1273_);
v_res_1282_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0(v___x_147670__boxed_1281_, v_inst_1274_, v_R_1275_, v_a_1276_, v_b_1277_, v_c_1278_, v___y_1279_, v___y_1280_);
lean_dec_ref(v___y_1279_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1(){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1290_ = l_Lean_Elab_macroAttribute;
v___x_1291_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
v___x_1292_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1));
v___x_1293_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_expandDoFor___boxed), 3, 0);
v___x_1294_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1290_, v___x_1291_, v___x_1292_, v___x_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___boxed(lean_object* v_a_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1();
return v_res_1296_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1297_ = lean_box(0);
v___x_1298_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
lean_ctor_set(v___x_1299_, 1, v___x_1297_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg(){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0);
v___x_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___boxed(lean_object* v___y_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0(lean_object* v_00_u03b1_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___boxed(lean_object* v_00_u03b1_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0(v_00_u03b1_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec_ref(v___y_1316_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0(lean_object* v_k_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v_b_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v___x_1335_; 
lean_inc(v___y_1333_);
lean_inc_ref(v___y_1332_);
lean_inc(v___y_1331_);
lean_inc_ref(v___y_1330_);
lean_inc(v___y_1328_);
lean_inc_ref(v___y_1327_);
lean_inc_ref(v___y_1326_);
v___x_1335_ = lean_apply_9(v_k_1325_, v_b_1329_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, lean_box(0));
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0___boxed(lean_object* v_k_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v_b_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0(v_k_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v_b_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec_ref(v___y_1337_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(lean_object* v_name_1347_, uint8_t v_bi_1348_, lean_object* v_type_1349_, lean_object* v_k_1350_, uint8_t v_kind_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v___f_1360_; lean_object* v___x_1361_; 
lean_inc(v___y_1354_);
lean_inc_ref(v___y_1353_);
lean_inc_ref(v___y_1352_);
v___f_1360_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1360_, 0, v_k_1350_);
lean_closure_set(v___f_1360_, 1, v___y_1352_);
lean_closure_set(v___f_1360_, 2, v___y_1353_);
lean_closure_set(v___f_1360_, 3, v___y_1354_);
v___x_1361_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1347_, v_bi_1348_, v_type_1349_, v___f_1360_, v_kind_1351_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
if (lean_obj_tag(v___x_1361_) == 0)
{
return v___x_1361_;
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1361_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1361_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___boxed(lean_object* v_name_1370_, lean_object* v_bi_1371_, lean_object* v_type_1372_, lean_object* v_k_1373_, lean_object* v_kind_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
uint8_t v_bi_boxed_1383_; uint8_t v_kind_boxed_1384_; lean_object* v_res_1385_; 
v_bi_boxed_1383_ = lean_unbox(v_bi_1371_);
v_kind_boxed_1384_ = lean_unbox(v_kind_1374_);
v_res_1385_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_name_1370_, v_bi_boxed_1383_, v_type_1372_, v_k_1373_, v_kind_boxed_1384_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec_ref(v___y_1375_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3(lean_object* v_00_u03b1_1386_, lean_object* v_name_1387_, uint8_t v_bi_1388_, lean_object* v_type_1389_, lean_object* v_k_1390_, uint8_t v_kind_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_name_1387_, v_bi_1388_, v_type_1389_, v_k_1390_, v_kind_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___boxed(lean_object* v_00_u03b1_1401_, lean_object* v_name_1402_, lean_object* v_bi_1403_, lean_object* v_type_1404_, lean_object* v_k_1405_, lean_object* v_kind_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
uint8_t v_bi_boxed_1415_; uint8_t v_kind_boxed_1416_; lean_object* v_res_1417_; 
v_bi_boxed_1415_ = lean_unbox(v_bi_1403_);
v_kind_boxed_1416_ = lean_unbox(v_kind_1406_);
v_res_1417_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3(v_00_u03b1_1401_, v_name_1402_, v_bi_boxed_1415_, v_type_1404_, v_k_1405_, v_kind_boxed_1416_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec_ref(v___y_1407_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__0(lean_object* v_a_1418_, lean_object* v_x_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1428_, 0, v_a_1418_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__0___boxed(lean_object* v_a_1429_, lean_object* v_x_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_Lean_Elab_Do_elabDoFor___lam__0(v_a_1429_, v_x_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec_ref(v_x_1430_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__1(lean_object* v_x_1440_, lean_object* v___f_1441_, lean_object* v___x_1442_, lean_object* v_x_1443_, lean_object* v_x_1444_){
_start:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1445_ = l_Lean_TSyntax_getId(v_x_1440_);
v___x_1446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
lean_ctor_set(v___x_1446_, 1, v___f_1441_);
v___x_1447_ = lean_mk_empty_array_with_capacity(v___x_1442_);
v___x_1448_ = lean_array_push(v___x_1447_, v___x_1446_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__1___boxed(lean_object* v_x_1449_, lean_object* v___f_1450_, lean_object* v___x_1451_, lean_object* v_x_1452_, lean_object* v_x_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l_Lean_Elab_Do_elabDoFor___lam__1(v_x_1449_, v___f_1450_, v___x_1451_, v_x_1452_, v_x_1453_);
lean_dec(v_x_1453_);
lean_dec(v_x_1452_);
lean_dec(v___x_1451_);
lean_dec(v_x_1449_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__3(lean_object* v_a_1455_, lean_object* v___x_1456_, uint8_t v___x_1457_, lean_object* v_r_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v_k_1467_; lean_object* v___x_1468_; 
v_k_1467_ = lean_ctor_get(v_a_1455_, 1);
lean_inc_ref(v_k_1467_);
lean_dec_ref(v_a_1455_);
lean_inc(v___y_1465_);
lean_inc_ref(v___y_1464_);
lean_inc(v___y_1463_);
lean_inc_ref(v___y_1462_);
lean_inc(v___y_1461_);
lean_inc_ref(v___y_1460_);
lean_inc_ref(v___y_1459_);
lean_inc_ref(v_r_1458_);
v___x_1468_ = lean_apply_9(v_k_1467_, v_r_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, lean_box(0));
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; uint8_t v___x_1472_; uint8_t v___x_1473_; lean_object* v___x_1474_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
lean_inc(v_a_1469_);
lean_dec_ref(v___x_1468_);
v___x_1470_ = lean_mk_empty_array_with_capacity(v___x_1456_);
v___x_1471_ = lean_array_push(v___x_1470_, v_r_1458_);
v___x_1472_ = 0;
v___x_1473_ = 1;
v___x_1474_ = l_Lean_Meta_mkLambdaFVars(v___x_1471_, v_a_1469_, v___x_1472_, v___x_1457_, v___x_1472_, v___x_1457_, v___x_1473_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec_ref(v___x_1471_);
return v___x_1474_;
}
else
{
lean_dec_ref(v_r_1458_);
return v___x_1468_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___boxed(lean_object* v_a_1475_, lean_object* v___x_1476_, lean_object* v___x_1477_, lean_object* v_r_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
uint8_t v___x_77835__boxed_1487_; lean_object* v_res_1488_; 
v___x_77835__boxed_1487_ = lean_unbox(v___x_1477_);
v_res_1488_ = l_Lean_Elab_Do_elabDoFor___lam__3(v_a_1475_, v___x_1476_, v___x_77835__boxed_1487_, v_r_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___x_1476_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1(lean_object* v___x_1489_, lean_object* v_as_1490_, size_t v_sz_1491_, size_t v_i_1492_, lean_object* v_b_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
uint8_t v___x_1501_; 
v___x_1501_ = lean_usize_dec_lt(v_i_1492_, v_sz_1491_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; 
lean_dec_ref(v___x_1489_);
v___x_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1502_, 0, v_b_1493_);
return v___x_1502_;
}
else
{
lean_object* v_a_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v_a_1503_ = lean_array_uget_borrowed(v_as_1490_, v_i_1492_);
v___x_1504_ = l_Lean_TSyntax_getId(v_a_1503_);
v___x_1505_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_1504_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; uint8_t v___x_1510_; lean_object* v___x_1511_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc_n(v_a_1506_, 2);
lean_dec_ref(v___x_1505_);
v___x_1507_ = l_Lean_LocalDecl_toExpr(v_a_1506_);
v___x_1508_ = lean_box(0);
v___x_1509_ = lean_box(0);
v___x_1510_ = 0;
lean_inc_ref(v___x_1507_);
lean_inc(v_a_1503_);
v___x_1511_ = l_Lean_Elab_Term_addTermInfo_x27(v_a_1503_, v___x_1507_, v___x_1508_, v___x_1508_, v___x_1509_, v___x_1510_, v___x_1510_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_u_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
lean_dec_ref(v___x_1511_);
v_u_1512_ = lean_ctor_get(v___x_1489_, 1);
lean_inc(v_u_1512_);
v___x_1513_ = l_Lean_Level_succ___override(v_u_1512_);
v___x_1514_ = l_Lean_mkSort(v___x_1513_);
v___x_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
v___x_1516_ = l_Lean_LocalDecl_type(v_a_1506_);
lean_dec(v_a_1506_);
v___x_1517_ = l_Lean_Elab_Term_ensureHasType(v___x_1515_, v___x_1516_, v___x_1508_, v___x_1508_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v___x_1518_; size_t v___x_1519_; size_t v___x_1520_; 
lean_dec_ref(v___x_1517_);
v___x_1518_ = lean_array_push(v_b_1493_, v___x_1507_);
v___x_1519_ = ((size_t)1ULL);
v___x_1520_ = lean_usize_add(v_i_1492_, v___x_1519_);
v_i_1492_ = v___x_1520_;
v_b_1493_ = v___x_1518_;
goto _start;
}
else
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
lean_dec_ref(v___x_1507_);
lean_dec_ref(v_b_1493_);
lean_dec_ref(v___x_1489_);
v_a_1522_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___x_1517_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1517_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1522_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
else
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1537_; 
lean_dec_ref(v___x_1507_);
lean_dec(v_a_1506_);
lean_dec_ref(v_b_1493_);
lean_dec_ref(v___x_1489_);
v_a_1530_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1532_ = v___x_1511_;
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1511_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_a_1530_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
else
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
lean_dec_ref(v_b_1493_);
lean_dec_ref(v___x_1489_);
v_a_1538_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v___x_1505_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1505_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1___boxed(lean_object* v___x_1546_, lean_object* v_as_1547_, lean_object* v_sz_1548_, lean_object* v_i_1549_, lean_object* v_b_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
size_t v_sz_boxed_1558_; size_t v_i_boxed_1559_; lean_object* v_res_1560_; 
v_sz_boxed_1558_ = lean_unbox_usize(v_sz_1548_);
lean_dec(v_sz_1548_);
v_i_boxed_1559_ = lean_unbox_usize(v_i_1549_);
lean_dec(v_i_1549_);
v_res_1560_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1(v___x_1546_, v_as_1547_, v_sz_boxed_1558_, v_i_boxed_1559_, v_b_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec_ref(v_as_1547_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(lean_object* v_msgData_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v___x_1567_; lean_object* v_env_1568_; lean_object* v___x_1569_; lean_object* v_mctx_1570_; lean_object* v_lctx_1571_; lean_object* v_options_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1567_ = lean_st_ref_get(v___y_1565_);
v_env_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc_ref(v_env_1568_);
lean_dec(v___x_1567_);
v___x_1569_ = lean_st_ref_get(v___y_1563_);
v_mctx_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc_ref(v_mctx_1570_);
lean_dec(v___x_1569_);
v_lctx_1571_ = lean_ctor_get(v___y_1562_, 2);
v_options_1572_ = lean_ctor_get(v___y_1564_, 2);
lean_inc_ref(v_options_1572_);
lean_inc_ref(v_lctx_1571_);
v___x_1573_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1573_, 0, v_env_1568_);
lean_ctor_set(v___x_1573_, 1, v_mctx_1570_);
lean_ctor_set(v___x_1573_, 2, v_lctx_1571_);
lean_ctor_set(v___x_1573_, 3, v_options_1572_);
v___x_1574_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
lean_ctor_set(v___x_1574_, 1, v_msgData_1561_);
v___x_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2___boxed(lean_object* v_msgData_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(v_msgData_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
return v_res_1582_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0(void){
_start:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = lean_box(1);
v___x_1584_ = l_Lean_MessageData_ofFormat(v___x_1583_);
return v___x_1584_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3(void){
_start:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__2));
v___x_1589_ = l_Lean_MessageData_ofFormat(v___x_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6(lean_object* v_x_1590_, lean_object* v_x_1591_){
_start:
{
if (lean_obj_tag(v_x_1591_) == 0)
{
return v_x_1590_;
}
else
{
lean_object* v_head_1592_; lean_object* v_tail_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1615_; 
v_head_1592_ = lean_ctor_get(v_x_1591_, 0);
v_tail_1593_ = lean_ctor_get(v_x_1591_, 1);
v_isSharedCheck_1615_ = !lean_is_exclusive(v_x_1591_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1595_ = v_x_1591_;
v_isShared_1596_ = v_isSharedCheck_1615_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_tail_1593_);
lean_inc(v_head_1592_);
lean_dec(v_x_1591_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1615_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v_before_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1613_; 
v_before_1597_ = lean_ctor_get(v_head_1592_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v_head_1592_);
if (v_isSharedCheck_1613_ == 0)
{
lean_object* v_unused_1614_; 
v_unused_1614_ = lean_ctor_get(v_head_1592_, 1);
lean_dec(v_unused_1614_);
v___x_1599_ = v_head_1592_;
v_isShared_1600_ = v_isSharedCheck_1613_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_before_1597_);
lean_dec(v_head_1592_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1613_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1601_; lean_object* v___x_1603_; 
v___x_1601_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0);
if (v_isShared_1600_ == 0)
{
lean_ctor_set_tag(v___x_1599_, 7);
lean_ctor_set(v___x_1599_, 1, v___x_1601_);
lean_ctor_set(v___x_1599_, 0, v_x_1590_);
v___x_1603_ = v___x_1599_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_x_1590_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v___x_1601_);
v___x_1603_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
lean_object* v___x_1604_; lean_object* v___x_1606_; 
v___x_1604_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3);
if (v_isShared_1596_ == 0)
{
lean_ctor_set_tag(v___x_1595_, 7);
lean_ctor_set(v___x_1595_, 1, v___x_1604_);
lean_ctor_set(v___x_1595_, 0, v___x_1603_);
v___x_1606_ = v___x_1595_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1603_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v___x_1604_);
v___x_1606_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1607_ = l_Lean_MessageData_ofSyntax(v_before_1597_);
v___x_1608_ = l_Lean_indentD(v___x_1607_);
v___x_1609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1606_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
v_x_1590_ = v___x_1609_;
v_x_1591_ = v_tail_1593_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5(lean_object* v_opts_1616_, lean_object* v_opt_1617_){
_start:
{
lean_object* v_name_1618_; lean_object* v_defValue_1619_; lean_object* v_map_1620_; lean_object* v___x_1621_; 
v_name_1618_ = lean_ctor_get(v_opt_1617_, 0);
v_defValue_1619_ = lean_ctor_get(v_opt_1617_, 1);
v_map_1620_ = lean_ctor_get(v_opts_1616_, 0);
v___x_1621_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1620_, v_name_1618_);
if (lean_obj_tag(v___x_1621_) == 0)
{
uint8_t v___x_1622_; 
v___x_1622_ = lean_unbox(v_defValue_1619_);
return v___x_1622_;
}
else
{
lean_object* v_val_1623_; 
v_val_1623_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_val_1623_);
lean_dec_ref(v___x_1621_);
if (lean_obj_tag(v_val_1623_) == 1)
{
uint8_t v_v_1624_; 
v_v_1624_ = lean_ctor_get_uint8(v_val_1623_, 0);
lean_dec_ref(v_val_1623_);
return v_v_1624_;
}
else
{
uint8_t v___x_1625_; 
lean_dec(v_val_1623_);
v___x_1625_ = lean_unbox(v_defValue_1619_);
return v___x_1625_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5___boxed(lean_object* v_opts_1626_, lean_object* v_opt_1627_){
_start:
{
uint8_t v_res_1628_; lean_object* v_r_1629_; 
v_res_1628_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5(v_opts_1626_, v_opt_1627_);
lean_dec_ref(v_opt_1627_);
lean_dec_ref(v_opts_1626_);
v_r_1629_ = lean_box(v_res_1628_);
return v_r_1629_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__1));
v___x_1634_ = l_Lean_MessageData_ofFormat(v___x_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(lean_object* v_msgData_1635_, lean_object* v_macroStack_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v_options_1639_; lean_object* v___x_1640_; uint8_t v___x_1641_; 
v_options_1639_ = lean_ctor_get(v___y_1637_, 2);
v___x_1640_ = l_Lean_Elab_pp_macroStack;
v___x_1641_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5(v_options_1639_, v___x_1640_);
if (v___x_1641_ == 0)
{
lean_object* v___x_1642_; 
lean_dec(v_macroStack_1636_);
v___x_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1642_, 0, v_msgData_1635_);
return v___x_1642_;
}
else
{
if (lean_obj_tag(v_macroStack_1636_) == 0)
{
lean_object* v___x_1643_; 
v___x_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1643_, 0, v_msgData_1635_);
return v___x_1643_;
}
else
{
lean_object* v_head_1644_; lean_object* v_after_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1660_; 
v_head_1644_ = lean_ctor_get(v_macroStack_1636_, 0);
lean_inc(v_head_1644_);
v_after_1645_ = lean_ctor_get(v_head_1644_, 1);
v_isSharedCheck_1660_ = !lean_is_exclusive(v_head_1644_);
if (v_isSharedCheck_1660_ == 0)
{
lean_object* v_unused_1661_; 
v_unused_1661_ = lean_ctor_get(v_head_1644_, 0);
lean_dec(v_unused_1661_);
v___x_1647_ = v_head_1644_;
v_isShared_1648_ = v_isSharedCheck_1660_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_after_1645_);
lean_dec(v_head_1644_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1660_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1649_; lean_object* v___x_1651_; 
v___x_1649_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0);
if (v_isShared_1648_ == 0)
{
lean_ctor_set_tag(v___x_1647_, 7);
lean_ctor_set(v___x_1647_, 1, v___x_1649_);
lean_ctor_set(v___x_1647_, 0, v_msgData_1635_);
v___x_1651_ = v___x_1647_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_msgData_1635_);
lean_ctor_set(v_reuseFailAlloc_1659_, 1, v___x_1649_);
v___x_1651_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v_msgData_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1652_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2);
v___x_1653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1651_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
v___x_1654_ = l_Lean_MessageData_ofSyntax(v_after_1645_);
v___x_1655_ = l_Lean_indentD(v___x_1654_);
v_msgData_1656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1656_, 0, v___x_1653_);
lean_ctor_set(v_msgData_1656_, 1, v___x_1655_);
v___x_1657_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6(v_msgData_1656_, v_macroStack_1636_);
v___x_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
return v___x_1658_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___boxed(lean_object* v_msgData_1662_, lean_object* v_macroStack_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(v_msgData_1662_, v_macroStack_1663_, v___y_1664_);
lean_dec_ref(v___y_1664_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(lean_object* v_msg_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v_ref_1675_; lean_object* v___x_1676_; lean_object* v_a_1677_; lean_object* v_macroStack_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1689_; 
v_ref_1675_ = lean_ctor_get(v___y_1672_, 5);
v___x_1676_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(v_msg_1667_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_a_1677_);
lean_dec_ref(v___x_1676_);
v_macroStack_1678_ = lean_ctor_get(v___y_1668_, 1);
lean_inc_n(v_macroStack_1678_, 2);
v___x_1679_ = l_Lean_Elab_getBetterRef(v_ref_1675_, v_macroStack_1678_);
v___x_1680_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(v_a_1677_, v_macroStack_1678_, v___y_1672_);
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1683_ = v___x_1680_;
v_isShared_1684_ = v_isSharedCheck_1689_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1680_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1689_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1685_; lean_object* v___x_1687_; 
v___x_1685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1679_);
lean_ctor_set(v___x_1685_, 1, v_a_1681_);
if (v_isShared_1684_ == 0)
{
lean_ctor_set_tag(v___x_1683_, 1);
lean_ctor_set(v___x_1683_, 0, v___x_1685_);
v___x_1687_ = v___x_1683_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg___boxed(lean_object* v_msg_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v_msg_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
return v_res_1698_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1704_ = lean_box(0);
v___x_1705_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__2___closed__2));
v___x_1706_ = l_Lean_mkConst(v___x_1705_, v___x_1704_);
return v___x_1706_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__2___closed__5(void){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1708_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__2___closed__4));
v___x_1709_ = l_Lean_stringToMessageData(v___x_1708_);
return v___x_1709_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__2___closed__7(void){
_start:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1711_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__2___closed__6));
v___x_1712_ = l_Lean_stringToMessageData(v___x_1711_);
return v___x_1712_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__2___closed__10(void){
_start:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__2___closed__9));
v___x_1717_ = l_Lean_MessageData_ofFormat(v___x_1716_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__2(lean_object* v___y_1718_, lean_object* v_monadInfo_1719_, uint8_t v_returnsEarly_1720_, lean_object* v___x_1721_, lean_object* v_a_1722_, uint8_t v___x_1723_, lean_object* v_e_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v_defs_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___x_1756_; lean_object* v_returnVar_1758_; lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1791_; lean_object* v___y_1792_; 
v___x_1756_ = lean_mk_empty_array_with_capacity(v___x_1721_);
if (lean_obj_tag(v_e_1724_) == 0)
{
if (v___x_1723_ == 0)
{
goto v___jp_1805_;
}
else
{
goto v___jp_1766_;
}
}
else
{
goto v___jp_1805_;
}
v___jp_1732_:
{
size_t v_sz_1740_; size_t v___x_1741_; lean_object* v___x_1742_; 
v_sz_1740_ = lean_array_size(v___y_1718_);
v___x_1741_ = ((size_t)0ULL);
v___x_1742_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1(v_monadInfo_1719_, v___y_1718_, v_sz_1740_, v___x_1741_, v_defs_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_1742_) == 0)
{
if (v_returnsEarly_1720_ == 0)
{
return v___x_1742_;
}
else
{
lean_object* v_a_1743_; lean_object* v___x_1744_; uint8_t v___x_1745_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_a_1743_);
v___x_1744_ = lean_array_get_size(v___y_1718_);
v___x_1745_ = lean_nat_dec_eq(v___x_1744_, v___x_1721_);
if (v___x_1745_ == 0)
{
lean_dec(v_a_1743_);
return v___x_1742_;
}
else
{
lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1754_; 
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1754_ == 0)
{
lean_object* v_unused_1755_; 
v_unused_1755_ = lean_ctor_get(v___x_1742_, 0);
lean_dec(v_unused_1755_);
v___x_1747_ = v___x_1742_;
v_isShared_1748_ = v_isSharedCheck_1754_;
goto v_resetjp_1746_;
}
else
{
lean_dec(v___x_1742_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1754_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1752_; 
v___x_1749_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__2___closed__3, &l_Lean_Elab_Do_elabDoFor___lam__2___closed__3_once, _init_l_Lean_Elab_Do_elabDoFor___lam__2___closed__3);
v___x_1750_ = lean_array_push(v_a_1743_, v___x_1749_);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 0, v___x_1750_);
v___x_1752_ = v___x_1747_;
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
else
{
return v___x_1742_;
}
}
v___jp_1757_:
{
lean_object* v___x_1765_; 
v___x_1765_ = lean_array_push(v___x_1756_, v_returnVar_1758_);
v_defs_1733_ = v___x_1765_;
v___y_1734_ = v___y_1759_;
v___y_1735_ = v___y_1760_;
v___y_1736_ = v___y_1761_;
v___y_1737_ = v___y_1762_;
v___y_1738_ = v___y_1763_;
v___y_1739_ = v___y_1764_;
goto v___jp_1732_;
}
v___jp_1766_:
{
if (v_returnsEarly_1720_ == 0)
{
lean_dec(v_e_1724_);
lean_dec_ref(v_a_1722_);
v_defs_1733_ = v___x_1756_;
v___y_1734_ = v___y_1725_;
v___y_1735_ = v___y_1726_;
v___y_1736_ = v___y_1727_;
v___y_1737_ = v___y_1728_;
v___y_1738_ = v___y_1729_;
v___y_1739_ = v___y_1730_;
goto v___jp_1732_;
}
else
{
if (lean_obj_tag(v_e_1724_) == 0)
{
lean_object* v_resultType_1767_; lean_object* v___x_1768_; 
v_resultType_1767_ = lean_ctor_get(v_a_1722_, 0);
lean_inc_ref(v_resultType_1767_);
lean_dec_ref(v_a_1722_);
v___x_1768_ = l_Lean_Meta_mkNone(v_resultType_1767_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1769_);
lean_dec_ref(v___x_1768_);
v_returnVar_1758_ = v_a_1769_;
v___y_1759_ = v___y_1725_;
v___y_1760_ = v___y_1726_;
v___y_1761_ = v___y_1727_;
v___y_1762_ = v___y_1728_;
v___y_1763_ = v___y_1729_;
v___y_1764_ = v___y_1730_;
goto v___jp_1757_;
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
lean_dec_ref(v___x_1756_);
lean_dec_ref(v_monadInfo_1719_);
v_a_1770_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1768_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1768_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
else
{
lean_object* v_val_1778_; lean_object* v_resultType_1779_; lean_object* v___x_1780_; 
v_val_1778_ = lean_ctor_get(v_e_1724_, 0);
lean_inc(v_val_1778_);
lean_dec_ref(v_e_1724_);
v_resultType_1779_ = lean_ctor_get(v_a_1722_, 0);
lean_inc_ref(v_resultType_1779_);
lean_dec_ref(v_a_1722_);
v___x_1780_ = l_Lean_Meta_mkSome(v_resultType_1779_, v_val_1778_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v_a_1781_; 
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_a_1781_);
lean_dec_ref(v___x_1780_);
v_returnVar_1758_ = v_a_1781_;
v___y_1759_ = v___y_1725_;
v___y_1760_ = v___y_1726_;
v___y_1761_ = v___y_1727_;
v___y_1762_ = v___y_1728_;
v___y_1763_ = v___y_1729_;
v___y_1764_ = v___y_1730_;
goto v___jp_1757_;
}
else
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
lean_dec_ref(v___x_1756_);
lean_dec_ref(v_monadInfo_1719_);
v_a_1782_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1780_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1780_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1782_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
}
}
v___jp_1790_:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
lean_inc_ref(v___y_1791_);
v___x_1793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1793_, 0, v___y_1791_);
lean_ctor_set(v___x_1793_, 1, v___y_1792_);
v___x_1794_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__2___closed__5, &l_Lean_Elab_Do_elabDoFor___lam__2___closed__5_once, _init_l_Lean_Elab_Do_elabDoFor___lam__2___closed__5);
v___x_1795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1793_);
lean_ctor_set(v___x_1795_, 1, v___x_1794_);
v___x_1796_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v___x_1795_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1796_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1796_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
v___jp_1805_:
{
if (v_returnsEarly_1720_ == 0)
{
lean_object* v___x_1806_; 
lean_dec_ref(v___x_1756_);
lean_dec_ref(v_a_1722_);
lean_dec_ref(v_monadInfo_1719_);
v___x_1806_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__2___closed__7, &l_Lean_Elab_Do_elabDoFor___lam__2___closed__7_once, _init_l_Lean_Elab_Do_elabDoFor___lam__2___closed__7);
if (lean_obj_tag(v_e_1724_) == 0)
{
lean_object* v___x_1807_; 
v___x_1807_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__2___closed__10, &l_Lean_Elab_Do_elabDoFor___lam__2___closed__10_once, _init_l_Lean_Elab_Do_elabDoFor___lam__2___closed__10);
v___y_1791_ = v___x_1806_;
v___y_1792_ = v___x_1807_;
goto v___jp_1790_;
}
else
{
lean_object* v_val_1808_; lean_object* v___x_1809_; 
v_val_1808_ = lean_ctor_get(v_e_1724_, 0);
lean_inc(v_val_1808_);
lean_dec_ref(v_e_1724_);
v___x_1809_ = l_Lean_MessageData_ofExpr(v_val_1808_);
v___y_1791_ = v___x_1806_;
v___y_1792_ = v___x_1809_;
goto v___jp_1790_;
}
}
else
{
goto v___jp_1766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__2___boxed(lean_object* v___y_1810_, lean_object* v_monadInfo_1811_, lean_object* v_returnsEarly_1812_, lean_object* v___x_1813_, lean_object* v_a_1814_, lean_object* v___x_1815_, lean_object* v_e_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
uint8_t v_returnsEarly_boxed_1824_; uint8_t v___x_78251__boxed_1825_; lean_object* v_res_1826_; 
v_returnsEarly_boxed_1824_ = lean_unbox(v_returnsEarly_1812_);
v___x_78251__boxed_1825_ = lean_unbox(v___x_1815_);
v_res_1826_ = l_Lean_Elab_Do_elabDoFor___lam__2(v___y_1810_, v_monadInfo_1811_, v_returnsEarly_boxed_1824_, v___x_1813_, v_a_1814_, v___x_78251__boxed_1825_, v_e_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___x_1813_);
lean_dec_ref(v___y_1810_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__4(lean_object* v___f_1828_, lean_object* v_u_1829_, lean_object* v___x_1830_, lean_object* v___x_1831_, lean_object* v_snd_1832_, lean_object* v___x_1833_, lean_object* v_e_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1843_, 0, v_e_1834_);
lean_inc(v___y_1841_);
lean_inc_ref(v___y_1840_);
lean_inc(v___y_1839_);
lean_inc_ref(v___y_1838_);
lean_inc(v___y_1837_);
lean_inc_ref(v___y_1836_);
v___x_1844_ = lean_apply_8(v___f_1828_, v___x_1843_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, lean_box(0));
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_a_1845_; lean_object* v___x_1846_; 
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_a_1845_);
lean_dec_ref(v___x_1844_);
v___x_1846_ = l_Lean_Meta_mkProdMkN(v_a_1845_, v_u_1829_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v_fst_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_a_1847_);
lean_dec_ref(v___x_1846_);
v_fst_1848_ = lean_ctor_get(v_a_1847_, 0);
lean_inc(v_fst_1848_);
lean_dec(v_a_1847_);
v___x_1849_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__4___closed__0));
v___x_1850_ = l_Lean_Name_mkStr2(v___x_1830_, v___x_1849_);
v___x_1851_ = l_Lean_mkConst(v___x_1850_, v___x_1831_);
v___x_1852_ = l_Lean_mkAppB(v___x_1851_, v_snd_1832_, v_fst_1848_);
v___x_1853_ = l_Lean_Elab_Do_mkPureApp(v___x_1833_, v___x_1852_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
return v___x_1853_;
}
else
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
lean_dec_ref(v___x_1833_);
lean_dec_ref(v_snd_1832_);
lean_dec(v___x_1831_);
lean_dec_ref(v___x_1830_);
v_a_1854_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1846_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1846_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1854_);
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
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
lean_dec_ref(v___x_1833_);
lean_dec_ref(v_snd_1832_);
lean_dec(v___x_1831_);
lean_dec_ref(v___x_1830_);
lean_dec(v_u_1829_);
v_a_1862_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1844_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1844_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___boxed(lean_object* v___f_1870_, lean_object* v_u_1871_, lean_object* v___x_1872_, lean_object* v___x_1873_, lean_object* v_snd_1874_, lean_object* v___x_1875_, lean_object* v_e_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Lean_Elab_Do_elabDoFor___lam__4(v___f_1870_, v_u_1871_, v___x_1872_, v___x_1873_, v_snd_1874_, v___x_1875_, v_e_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec_ref(v___y_1877_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__5(lean_object* v___f_1887_, lean_object* v___x_1888_, lean_object* v_u_1889_, lean_object* v___x_1890_, lean_object* v___x_1891_, lean_object* v_snd_1892_, lean_object* v___x_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v___x_1902_; 
lean_inc(v___y_1900_);
lean_inc_ref(v___y_1899_);
lean_inc(v___y_1898_);
lean_inc_ref(v___y_1897_);
lean_inc(v___y_1896_);
lean_inc_ref(v___y_1895_);
v___x_1902_ = lean_apply_8(v___f_1887_, v___x_1888_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, lean_box(0));
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; lean_object* v___x_1904_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_a_1903_);
lean_dec_ref(v___x_1902_);
v___x_1904_ = l_Lean_Meta_mkProdMkN(v_a_1903_, v_u_1889_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v_fst_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_a_1905_);
lean_dec_ref(v___x_1904_);
v_fst_1906_ = lean_ctor_get(v_a_1905_, 0);
lean_inc(v_fst_1906_);
lean_dec(v_a_1905_);
v___x_1907_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__5___closed__0));
v___x_1908_ = l_Lean_Name_mkStr2(v___x_1890_, v___x_1907_);
v___x_1909_ = l_Lean_mkConst(v___x_1908_, v___x_1891_);
v___x_1910_ = l_Lean_mkAppB(v___x_1909_, v_snd_1892_, v_fst_1906_);
v___x_1911_ = l_Lean_Elab_Do_mkPureApp(v___x_1893_, v___x_1910_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
return v___x_1911_;
}
else
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1919_; 
lean_dec_ref(v___x_1893_);
lean_dec_ref(v_snd_1892_);
lean_dec(v___x_1891_);
lean_dec_ref(v___x_1890_);
v_a_1912_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1914_ = v___x_1904_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1904_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
lean_dec_ref(v___x_1893_);
lean_dec_ref(v_snd_1892_);
lean_dec(v___x_1891_);
lean_dec_ref(v___x_1890_);
lean_dec(v_u_1889_);
v_a_1920_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1902_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1902_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__5___boxed(lean_object* v___f_1928_, lean_object* v___x_1929_, lean_object* v_u_1930_, lean_object* v___x_1931_, lean_object* v___x_1932_, lean_object* v_snd_1933_, lean_object* v___x_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l_Lean_Elab_Do_elabDoFor___lam__5(v___f_1928_, v___x_1929_, v_u_1930_, v___x_1931_, v___x_1932_, v_snd_1933_, v___x_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec_ref(v___y_1935_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__6(lean_object* v___f_1944_, lean_object* v___x_1945_, lean_object* v_u_1946_, lean_object* v___x_1947_, lean_object* v___x_1948_, lean_object* v_snd_1949_, lean_object* v___x_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
lean_object* v___x_1959_; 
lean_inc(v___y_1957_);
lean_inc_ref(v___y_1956_);
lean_inc(v___y_1955_);
lean_inc_ref(v___y_1954_);
lean_inc(v___y_1953_);
lean_inc_ref(v___y_1952_);
v___x_1959_ = lean_apply_8(v___f_1944_, v___x_1945_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, lean_box(0));
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v_a_1960_; lean_object* v___x_1961_; 
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_a_1960_);
lean_dec_ref(v___x_1959_);
v___x_1961_ = l_Lean_Meta_mkProdMkN(v_a_1960_, v_u_1946_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v_a_1962_; lean_object* v_fst_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_a_1962_);
lean_dec_ref(v___x_1961_);
v_fst_1963_ = lean_ctor_get(v_a_1962_, 0);
lean_inc(v_fst_1963_);
lean_dec(v_a_1962_);
v___x_1964_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__4___closed__0));
v___x_1965_ = l_Lean_Name_mkStr2(v___x_1947_, v___x_1964_);
v___x_1966_ = l_Lean_mkConst(v___x_1965_, v___x_1948_);
v___x_1967_ = l_Lean_mkAppB(v___x_1966_, v_snd_1949_, v_fst_1963_);
v___x_1968_ = l_Lean_Elab_Do_mkPureApp(v___x_1950_, v___x_1967_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
return v___x_1968_;
}
else
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1976_; 
lean_dec_ref(v___x_1950_);
lean_dec_ref(v_snd_1949_);
lean_dec(v___x_1948_);
lean_dec_ref(v___x_1947_);
v_a_1969_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___x_1961_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1961_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1969_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
else
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1984_; 
lean_dec_ref(v___x_1950_);
lean_dec_ref(v_snd_1949_);
lean_dec(v___x_1948_);
lean_dec_ref(v___x_1947_);
lean_dec(v_u_1946_);
v_a_1977_ = lean_ctor_get(v___x_1959_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1979_ = v___x_1959_;
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v___x_1959_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1982_; 
if (v_isShared_1980_ == 0)
{
v___x_1982_ = v___x_1979_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_a_1977_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__6___boxed(lean_object* v___f_1985_, lean_object* v___x_1986_, lean_object* v_u_1987_, lean_object* v___x_1988_, lean_object* v___x_1989_, lean_object* v_snd_1990_, lean_object* v___x_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l_Lean_Elab_Do_elabDoFor___lam__6(v___f_1985_, v___x_1986_, v_u_1987_, v___x_1988_, v___x_1989_, v_snd_1990_, v___x_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec_ref(v___y_1992_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__7(lean_object* v___x_2001_, lean_object* v___f_2002_, lean_object* v___f_2003_, lean_object* v___x_2004_, lean_object* v___x_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
lean_object* v_monadInfo_2014_; lean_object* v_mutVars_2015_; lean_object* v_mutVarDefs_2016_; lean_object* v_contInfo_2017_; uint8_t v_deadCode_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2026_; 
v_monadInfo_2014_ = lean_ctor_get(v___y_2006_, 0);
v_mutVars_2015_ = lean_ctor_get(v___y_2006_, 1);
v_mutVarDefs_2016_ = lean_ctor_get(v___y_2006_, 2);
v_contInfo_2017_ = lean_ctor_get(v___y_2006_, 4);
v_deadCode_2018_ = lean_ctor_get_uint8(v___y_2006_, sizeof(void*)*5);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___y_2006_);
if (v_isSharedCheck_2026_ == 0)
{
lean_object* v_unused_2027_; 
v_unused_2027_ = lean_ctor_get(v___y_2006_, 3);
lean_dec(v_unused_2027_);
v___x_2020_ = v___y_2006_;
v_isShared_2021_ = v_isSharedCheck_2026_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_contInfo_2017_);
lean_inc(v_mutVarDefs_2016_);
lean_inc(v_mutVars_2015_);
lean_inc(v_monadInfo_2014_);
lean_dec(v___y_2006_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2026_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 3, v___x_2001_);
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_monadInfo_2014_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_mutVars_2015_);
lean_ctor_set(v_reuseFailAlloc_2025_, 2, v_mutVarDefs_2016_);
lean_ctor_set(v_reuseFailAlloc_2025_, 3, v___x_2001_);
lean_ctor_set(v_reuseFailAlloc_2025_, 4, v_contInfo_2017_);
lean_ctor_set_uint8(v_reuseFailAlloc_2025_, sizeof(void*)*5, v_deadCode_2018_);
v___x_2023_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
lean_object* v___x_2024_; 
v___x_2024_ = l_Lean_Elab_Do_enterLoopBody___redArg(v___f_2002_, v___f_2003_, v___x_2004_, v___x_2005_, v___x_2023_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
lean_dec_ref(v___x_2023_);
return v___x_2024_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__7___boxed(lean_object* v___x_2028_, lean_object* v___f_2029_, lean_object* v___f_2030_, lean_object* v___x_2031_, lean_object* v___x_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l_Lean_Elab_Do_elabDoFor___lam__7(v___x_2028_, v___f_2029_, v___f_2030_, v___x_2031_, v___x_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__8(lean_object* v_a_2045_, lean_object* v_u_2046_, lean_object* v_snd_2047_, lean_object* v___f_2048_, lean_object* v___x_2049_, lean_object* v_resultName_2050_, lean_object* v_resultType_2051_, lean_object* v_body_2052_, uint8_t v___x_2053_, lean_object* v___y_2054_, lean_object* v_xh_2055_, lean_object* v_loopS_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v_resultType_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2093_; 
v_resultType_2065_ = lean_ctor_get(v_a_2045_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v_a_2045_);
if (v_isSharedCheck_2093_ == 0)
{
lean_object* v_unused_2094_; 
v_unused_2094_ = lean_ctor_get(v_a_2045_, 1);
lean_dec(v_unused_2094_);
v___x_2067_ = v_a_2045_;
v_isShared_2068_ = v_isSharedCheck_2093_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_resultType_2065_);
lean_dec(v_a_2045_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2093_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___f_2076_; lean_object* v___f_2077_; lean_object* v___f_2078_; lean_object* v___x_2080_; 
v___x_2069_ = l_Lean_Expr_fvarId_x21(v_loopS_2056_);
v___x_2070_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__8___closed__0));
v___x_2071_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__8___closed__1));
v___x_2072_ = lean_box(0);
lean_inc_n(v_u_2046_, 3);
v___x_2073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2073_, 0, v_u_2046_);
lean_ctor_set(v___x_2073_, 1, v___x_2072_);
lean_inc_ref_n(v___x_2073_, 3);
v___x_2074_ = l_Lean_mkConst(v___x_2071_, v___x_2073_);
lean_inc_ref_n(v_snd_2047_, 3);
v___x_2075_ = l_Lean_Expr_app___override(v___x_2074_, v_snd_2047_);
lean_inc_ref_n(v___x_2075_, 3);
lean_inc_ref_n(v___f_2048_, 2);
v___f_2076_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__4___boxed), 15, 6);
lean_closure_set(v___f_2076_, 0, v___f_2048_);
lean_closure_set(v___f_2076_, 1, v_u_2046_);
lean_closure_set(v___f_2076_, 2, v___x_2070_);
lean_closure_set(v___f_2076_, 3, v___x_2073_);
lean_closure_set(v___f_2076_, 4, v_snd_2047_);
lean_closure_set(v___f_2076_, 5, v___x_2075_);
lean_inc(v___x_2049_);
v___f_2077_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__5___boxed), 15, 7);
lean_closure_set(v___f_2077_, 0, v___f_2048_);
lean_closure_set(v___f_2077_, 1, v___x_2049_);
lean_closure_set(v___f_2077_, 2, v_u_2046_);
lean_closure_set(v___f_2077_, 3, v___x_2070_);
lean_closure_set(v___f_2077_, 4, v___x_2073_);
lean_closure_set(v___f_2077_, 5, v_snd_2047_);
lean_closure_set(v___f_2077_, 6, v___x_2075_);
v___f_2078_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__6___boxed), 15, 7);
lean_closure_set(v___f_2078_, 0, v___f_2048_);
lean_closure_set(v___f_2078_, 1, v___x_2049_);
lean_closure_set(v___f_2078_, 2, v_u_2046_);
lean_closure_set(v___f_2078_, 3, v___x_2070_);
lean_closure_set(v___f_2078_, 4, v___x_2073_);
lean_closure_set(v___f_2078_, 5, v_snd_2047_);
lean_closure_set(v___f_2078_, 6, v___x_2075_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 1, v___f_2076_);
v___x_2080_ = v___x_2067_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_resultType_2065_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v___f_2076_);
v___x_2080_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
uint8_t v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___f_2085_; lean_object* v___x_2086_; 
v___x_2081_ = 1;
lean_inc_ref(v___f_2077_);
v___x_2082_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2082_, 0, v_resultName_2050_);
lean_ctor_set(v___x_2082_, 1, v_resultType_2051_);
lean_ctor_set(v___x_2082_, 2, v___f_2077_);
lean_ctor_set_uint8(v___x_2082_, sizeof(void*)*3, v___x_2081_);
v___x_2083_ = lean_box(v___x_2053_);
v___x_2084_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoSeq___boxed), 11, 3);
lean_closure_set(v___x_2084_, 0, v_body_2052_);
lean_closure_set(v___x_2084_, 1, v___x_2082_);
lean_closure_set(v___x_2084_, 2, v___x_2083_);
v___f_2085_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__7___boxed), 13, 5);
lean_closure_set(v___f_2085_, 0, v___x_2075_);
lean_closure_set(v___f_2085_, 1, v___f_2078_);
lean_closure_set(v___f_2085_, 2, v___f_2077_);
lean_closure_set(v___f_2085_, 3, v___x_2080_);
lean_closure_set(v___f_2085_, 4, v___x_2084_);
v___x_2086_ = l_Lean_Elab_Do_bindMutVarsFromTuple(v___y_2054_, v___x_2069_, v___f_2085_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; uint8_t v___x_2090_; lean_object* v___x_2091_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_a_2087_);
lean_dec_ref(v___x_2086_);
v___x_2088_ = lean_array_push(v_xh_2055_, v_loopS_2056_);
v___x_2089_ = 0;
v___x_2090_ = 1;
v___x_2091_ = l_Lean_Meta_mkLambdaFVars(v___x_2088_, v_a_2087_, v___x_2089_, v___x_2053_, v___x_2089_, v___x_2053_, v___x_2090_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
lean_dec_ref(v___x_2088_);
return v___x_2091_;
}
else
{
lean_dec_ref(v_loopS_2056_);
lean_dec_ref(v_xh_2055_);
return v___x_2086_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__8___boxed(lean_object** _args){
lean_object* v_a_2095_ = _args[0];
lean_object* v_u_2096_ = _args[1];
lean_object* v_snd_2097_ = _args[2];
lean_object* v___f_2098_ = _args[3];
lean_object* v___x_2099_ = _args[4];
lean_object* v_resultName_2100_ = _args[5];
lean_object* v_resultType_2101_ = _args[6];
lean_object* v_body_2102_ = _args[7];
lean_object* v___x_2103_ = _args[8];
lean_object* v___y_2104_ = _args[9];
lean_object* v_xh_2105_ = _args[10];
lean_object* v_loopS_2106_ = _args[11];
lean_object* v___y_2107_ = _args[12];
lean_object* v___y_2108_ = _args[13];
lean_object* v___y_2109_ = _args[14];
lean_object* v___y_2110_ = _args[15];
lean_object* v___y_2111_ = _args[16];
lean_object* v___y_2112_ = _args[17];
lean_object* v___y_2113_ = _args[18];
lean_object* v___y_2114_ = _args[19];
_start:
{
uint8_t v___x_78807__boxed_2115_; lean_object* v_res_2116_; 
v___x_78807__boxed_2115_ = lean_unbox(v___x_2103_);
v_res_2116_ = l_Lean_Elab_Do_elabDoFor___lam__8(v_a_2095_, v_u_2096_, v_snd_2097_, v___f_2098_, v___x_2099_, v_resultName_2100_, v_resultType_2101_, v_body_2102_, v___x_78807__boxed_2115_, v___y_2104_, v_xh_2105_, v_loopS_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec_ref(v___y_2107_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9(lean_object* v_a_2117_, lean_object* v_u_2118_, lean_object* v_snd_2119_, lean_object* v___f_2120_, lean_object* v___x_2121_, lean_object* v_resultName_2122_, lean_object* v_resultType_2123_, lean_object* v_body_2124_, uint8_t v___x_2125_, lean_object* v___y_2126_, lean_object* v_a_2127_, lean_object* v_xh_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v___x_2137_; lean_object* v___f_2138_; uint8_t v___x_2139_; uint8_t v___x_2140_; lean_object* v___x_2141_; 
v___x_2137_ = lean_box(v___x_2125_);
lean_inc_ref(v_snd_2119_);
v___f_2138_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__8___boxed), 20, 11);
lean_closure_set(v___f_2138_, 0, v_a_2117_);
lean_closure_set(v___f_2138_, 1, v_u_2118_);
lean_closure_set(v___f_2138_, 2, v_snd_2119_);
lean_closure_set(v___f_2138_, 3, v___f_2120_);
lean_closure_set(v___f_2138_, 4, v___x_2121_);
lean_closure_set(v___f_2138_, 5, v_resultName_2122_);
lean_closure_set(v___f_2138_, 6, v_resultType_2123_);
lean_closure_set(v___f_2138_, 7, v_body_2124_);
lean_closure_set(v___f_2138_, 8, v___x_2137_);
lean_closure_set(v___f_2138_, 9, v___y_2126_);
lean_closure_set(v___f_2138_, 10, v_xh_2128_);
v___x_2139_ = 0;
v___x_2140_ = 1;
v___x_2141_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_a_2127_, v___x_2139_, v_snd_2119_, v___f_2138_, v___x_2140_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9___boxed(lean_object** _args){
lean_object* v_a_2142_ = _args[0];
lean_object* v_u_2143_ = _args[1];
lean_object* v_snd_2144_ = _args[2];
lean_object* v___f_2145_ = _args[3];
lean_object* v___x_2146_ = _args[4];
lean_object* v_resultName_2147_ = _args[5];
lean_object* v_resultType_2148_ = _args[6];
lean_object* v_body_2149_ = _args[7];
lean_object* v___x_2150_ = _args[8];
lean_object* v___y_2151_ = _args[9];
lean_object* v_a_2152_ = _args[10];
lean_object* v_xh_2153_ = _args[11];
lean_object* v___y_2154_ = _args[12];
lean_object* v___y_2155_ = _args[13];
lean_object* v___y_2156_ = _args[14];
lean_object* v___y_2157_ = _args[15];
lean_object* v___y_2158_ = _args[16];
lean_object* v___y_2159_ = _args[17];
lean_object* v___y_2160_ = _args[18];
lean_object* v___y_2161_ = _args[19];
_start:
{
uint8_t v___x_78911__boxed_2162_; lean_object* v_res_2163_; 
v___x_78911__boxed_2162_ = lean_unbox(v___x_2150_);
v_res_2163_ = l_Lean_Elab_Do_elabDoFor___lam__9(v_a_2142_, v_u_2143_, v_snd_2144_, v___f_2145_, v___x_2146_, v_resultName_2147_, v_resultType_2148_, v_body_2149_, v___x_78911__boxed_2162_, v___y_2151_, v_a_2152_, v_xh_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec_ref(v___y_2154_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(lean_object* v_name_2164_, lean_object* v_type_2165_, lean_object* v_k_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
uint8_t v___x_2175_; uint8_t v___x_2176_; lean_object* v___x_2177_; 
v___x_2175_ = 0;
v___x_2176_ = 0;
v___x_2177_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_name_2164_, v___x_2175_, v_type_2165_, v_k_2166_, v___x_2176_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg___boxed(lean_object* v_name_2178_, lean_object* v_type_2179_, lean_object* v_k_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(v_name_2178_, v_type_2179_, v_k_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec_ref(v___y_2181_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__10(uint8_t v_returnsEarly_2207_, lean_object* v_dec_2208_, lean_object* v_a_2209_, lean_object* v_doBlockResultType_2210_, lean_object* v_a_2211_, lean_object* v_v_2212_, lean_object* v_u_2213_, lean_object* v___f_2214_, lean_object* v___y_2215_, lean_object* v___x_2216_, lean_object* v___x_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v_ret_2227_; lean_object* v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; 
if (v_returnsEarly_2207_ == 0)
{
lean_object* v___x_2281_; 
lean_dec_ref(v___f_2214_);
lean_dec(v_u_2213_);
lean_dec(v_v_2212_);
lean_dec_ref(v_a_2211_);
lean_dec_ref(v_doBlockResultType_2210_);
lean_dec(v_a_2209_);
v___x_2281_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_dec_2208_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
return v___x_2281_;
}
else
{
lean_object* v___x_2282_; 
v___x_2282_ = l_Lean_Meta_getFVarFromUserName(v_a_2209_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; lean_object* v___x_2284_; uint8_t v___x_2285_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_a_2283_);
lean_dec_ref(v___x_2282_);
v___x_2284_ = lean_array_get_size(v___y_2215_);
v___x_2285_ = lean_nat_dec_eq(v___x_2284_, v___x_2216_);
if (v___x_2285_ == 0)
{
v_ret_2227_ = v_a_2283_;
v___y_2228_ = v___y_2218_;
v___y_2229_ = v___y_2219_;
v___y_2230_ = v___y_2220_;
v___y_2231_ = v___y_2221_;
v___y_2232_ = v___y_2222_;
v___y_2233_ = v___y_2223_;
v___y_2234_ = v___y_2224_;
goto v___jp_2226_;
}
else
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2286_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__10___closed__9));
v___x_2287_ = lean_mk_empty_array_with_capacity(v___x_2217_);
v___x_2288_ = lean_array_push(v___x_2287_, v_a_2283_);
v___x_2289_ = l_Lean_Meta_mkAppM(v___x_2286_, v___x_2288_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v_a_2290_; 
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_a_2290_);
lean_dec_ref(v___x_2289_);
v_ret_2227_ = v_a_2290_;
v___y_2228_ = v___y_2218_;
v___y_2229_ = v___y_2219_;
v___y_2230_ = v___y_2220_;
v___y_2231_ = v___y_2221_;
v___y_2232_ = v___y_2222_;
v___y_2233_ = v___y_2223_;
v___y_2234_ = v___y_2224_;
goto v___jp_2226_;
}
else
{
lean_dec_ref(v___f_2214_);
lean_dec(v_u_2213_);
lean_dec(v_v_2212_);
lean_dec_ref(v_a_2211_);
lean_dec_ref(v_doBlockResultType_2210_);
lean_dec_ref(v_dec_2208_);
return v___x_2289_;
}
}
}
else
{
lean_dec_ref(v___f_2214_);
lean_dec(v_u_2213_);
lean_dec(v_v_2212_);
lean_dec_ref(v_a_2211_);
lean_dec_ref(v_doBlockResultType_2210_);
lean_dec_ref(v_dec_2208_);
return v___x_2282_;
}
}
v___jp_2226_:
{
lean_object* v___x_2235_; 
lean_inc(v___y_2234_);
lean_inc_ref(v___y_2233_);
lean_inc(v___y_2232_);
lean_inc_ref(v___y_2231_);
lean_inc_ref(v_ret_2227_);
v___x_2235_ = lean_infer_type(v_ret_2227_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; lean_object* v___x_2237_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2236_);
lean_dec_ref(v___x_2235_);
v___x_2237_ = l_Lean_Elab_Do_mkMonadicType___redArg(v_doBlockResultType_2210_, v___y_2228_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v_a_2238_; lean_object* v___x_2239_; 
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
lean_inc(v_a_2238_);
lean_dec_ref(v___x_2237_);
v___x_2239_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_dec_2208_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_a_2240_);
lean_dec_ref(v___x_2239_);
v___x_2241_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__10___closed__1));
v___x_2242_ = l_Lean_Core_mkFreshUserName(v___x_2241_, v___y_2233_, v___y_2234_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v_a_2243_; lean_object* v_resultType_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2271_; 
v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
lean_inc(v_a_2243_);
lean_dec_ref(v___x_2242_);
v_resultType_2244_ = lean_ctor_get(v_a_2211_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v_a_2211_);
if (v_isSharedCheck_2271_ == 0)
{
lean_object* v_unused_2272_; 
v_unused_2272_ = lean_ctor_get(v_a_2211_, 1);
lean_dec(v_unused_2272_);
v___x_2246_ = v_a_2211_;
v_isShared_2247_ = v_isSharedCheck_2271_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_resultType_2244_);
lean_dec(v_a_2211_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2271_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2248_; uint8_t v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2255_; 
v___x_2248_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__10___closed__2));
v___x_2249_ = 0;
v___x_2250_ = l_Lean_mkLambda(v___x_2248_, v___x_2249_, v_a_2236_, v_a_2238_);
v___x_2251_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__10___closed__6));
v___x_2252_ = l_Lean_Level_succ___override(v_v_2212_);
v___x_2253_ = lean_box(0);
if (v_isShared_2247_ == 0)
{
lean_ctor_set_tag(v___x_2246_, 1);
lean_ctor_set(v___x_2246_, 1, v___x_2253_);
lean_ctor_set(v___x_2246_, 0, v___x_2252_);
v___x_2255_ = v___x_2246_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2252_);
lean_ctor_set(v_reuseFailAlloc_2270_, 1, v___x_2253_);
v___x_2255_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2256_, 0, v_u_2213_);
lean_ctor_set(v___x_2256_, 1, v___x_2255_);
v___x_2257_ = l_Lean_mkConst(v___x_2251_, v___x_2256_);
lean_inc_ref(v_resultType_2244_);
v___x_2258_ = l_Lean_mkApp3(v___x_2257_, v_resultType_2244_, v___x_2250_, v_ret_2227_);
v___x_2259_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(v_a_2243_, v_resultType_2244_, v___f_2214_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2269_; 
v_a_2260_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2262_ = v___x_2259_;
v_isShared_2263_ = v_isSharedCheck_2269_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___x_2259_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2269_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2267_; 
v___x_2264_ = l_Lean_mkSimpleThunk(v_a_2240_);
v___x_2265_ = l_Lean_mkAppB(v___x_2258_, v_a_2260_, v___x_2264_);
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 0, v___x_2265_);
v___x_2267_ = v___x_2262_;
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
else
{
lean_dec_ref(v___x_2258_);
lean_dec(v_a_2240_);
return v___x_2259_;
}
}
}
}
else
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
lean_dec(v_a_2240_);
lean_dec(v_a_2238_);
lean_dec(v_a_2236_);
lean_dec_ref(v_ret_2227_);
lean_dec_ref(v___f_2214_);
lean_dec(v_u_2213_);
lean_dec(v_v_2212_);
lean_dec_ref(v_a_2211_);
v_a_2273_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2242_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2242_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_a_2273_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
else
{
lean_dec(v_a_2238_);
lean_dec(v_a_2236_);
lean_dec_ref(v_ret_2227_);
lean_dec_ref(v___f_2214_);
lean_dec(v_u_2213_);
lean_dec(v_v_2212_);
lean_dec_ref(v_a_2211_);
return v___x_2239_;
}
}
else
{
lean_dec(v_a_2236_);
lean_dec_ref(v_ret_2227_);
lean_dec_ref(v___f_2214_);
lean_dec(v_u_2213_);
lean_dec(v_v_2212_);
lean_dec_ref(v_a_2211_);
lean_dec_ref(v_dec_2208_);
return v___x_2237_;
}
}
else
{
lean_dec_ref(v_ret_2227_);
lean_dec_ref(v___f_2214_);
lean_dec(v_u_2213_);
lean_dec(v_v_2212_);
lean_dec_ref(v_a_2211_);
lean_dec_ref(v_doBlockResultType_2210_);
lean_dec_ref(v_dec_2208_);
return v___x_2235_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___boxed(lean_object** _args){
lean_object* v_returnsEarly_2291_ = _args[0];
lean_object* v_dec_2292_ = _args[1];
lean_object* v_a_2293_ = _args[2];
lean_object* v_doBlockResultType_2294_ = _args[3];
lean_object* v_a_2295_ = _args[4];
lean_object* v_v_2296_ = _args[5];
lean_object* v_u_2297_ = _args[6];
lean_object* v___f_2298_ = _args[7];
lean_object* v___y_2299_ = _args[8];
lean_object* v___x_2300_ = _args[9];
lean_object* v___x_2301_ = _args[10];
lean_object* v___y_2302_ = _args[11];
lean_object* v___y_2303_ = _args[12];
lean_object* v___y_2304_ = _args[13];
lean_object* v___y_2305_ = _args[14];
lean_object* v___y_2306_ = _args[15];
lean_object* v___y_2307_ = _args[16];
lean_object* v___y_2308_ = _args[17];
lean_object* v___y_2309_ = _args[18];
_start:
{
uint8_t v_returnsEarly_boxed_2310_; lean_object* v_res_2311_; 
v_returnsEarly_boxed_2310_ = lean_unbox(v_returnsEarly_2291_);
v_res_2311_ = l_Lean_Elab_Do_elabDoFor___lam__10(v_returnsEarly_boxed_2310_, v_dec_2292_, v_a_2293_, v_doBlockResultType_2294_, v_a_2295_, v_v_2296_, v_u_2297_, v___f_2298_, v___y_2299_, v___x_2300_, v___x_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec_ref(v___y_2302_);
lean_dec(v___x_2301_);
lean_dec(v___x_2300_);
lean_dec_ref(v___y_2299_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__11(lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___x_2314_, uint8_t v___x_2315_, lean_object* v_postS_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2325_ = l_Lean_Expr_fvarId_x21(v_postS_2316_);
v___x_2326_ = l_Lean_Elab_Do_bindMutVarsFromTuple(v___y_2312_, v___x_2325_, v___y_2313_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; uint8_t v___x_2330_; uint8_t v___x_2331_; lean_object* v___x_2332_; 
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_a_2327_);
lean_dec_ref(v___x_2326_);
v___x_2328_ = lean_mk_empty_array_with_capacity(v___x_2314_);
v___x_2329_ = lean_array_push(v___x_2328_, v_postS_2316_);
v___x_2330_ = 0;
v___x_2331_ = 1;
v___x_2332_ = l_Lean_Meta_mkLambdaFVars(v___x_2329_, v_a_2327_, v___x_2330_, v___x_2315_, v___x_2330_, v___x_2315_, v___x_2331_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
lean_dec_ref(v___x_2329_);
return v___x_2332_;
}
else
{
lean_dec_ref(v_postS_2316_);
return v___x_2326_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__11___boxed(lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___x_2335_, lean_object* v___x_2336_, lean_object* v_postS_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
uint8_t v___x_79221__boxed_2346_; lean_object* v_res_2347_; 
v___x_79221__boxed_2346_ = lean_unbox(v___x_2336_);
v_res_2347_ = l_Lean_Elab_Do_elabDoFor___lam__11(v___y_2333_, v___y_2334_, v___x_2335_, v___x_79221__boxed_2346_, v_postS_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec_ref(v___y_2338_);
lean_dec(v___x_2335_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__12(lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v___x_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_val_2358_, lean_object* v_a_2359_, lean_object* v_x_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2369_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__12___closed__2));
v___x_2370_ = lean_box(0);
v___x_2371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2371_, 0, v_a_2353_);
lean_ctor_set(v___x_2371_, 1, v___x_2370_);
v___x_2372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2372_, 0, v_a_2354_);
lean_ctor_set(v___x_2372_, 1, v___x_2371_);
v___x_2373_ = l_Lean_mkConst(v___x_2369_, v___x_2372_);
v___x_2374_ = l_Lean_instInhabitedExpr;
v___x_2375_ = lean_array_get_borrowed(v___x_2374_, v_x_2360_, v___x_2355_);
lean_inc(v___x_2375_);
v___x_2376_ = l_Lean_mkApp5(v___x_2373_, v_a_2356_, v_a_2357_, v_val_2358_, v_a_2359_, v___x_2375_);
v___x_2377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2376_);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__12___boxed(lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v___x_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_val_2383_, lean_object* v_a_2384_, lean_object* v_x_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_){
_start:
{
lean_object* v_res_2394_; 
v_res_2394_ = l_Lean_Elab_Do_elabDoFor___lam__12(v_a_2378_, v_a_2379_, v___x_2380_, v_a_2381_, v_a_2382_, v_val_2383_, v_a_2384_, v_x_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec_ref(v_x_2385_);
lean_dec(v___x_2380_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__0(lean_object* v___x_2395_, lean_object* v_a_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_77607__overap_2406_; lean_object* v___x_2407_; 
v___x_2405_ = l_Lean_instInhabitedExpr;
v___x_77607__overap_2406_ = l_instInhabitedOfMonad___redArg(v___x_2395_, v___x_2405_);
lean_inc(v___y_2403_);
lean_inc_ref(v___y_2402_);
lean_inc(v___y_2401_);
lean_inc_ref(v___y_2400_);
lean_inc(v___y_2399_);
lean_inc_ref(v___y_2398_);
lean_inc_ref(v___y_2397_);
v___x_2407_ = lean_apply_8(v___x_77607__overap_2406_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, lean_box(0));
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__0___boxed(lean_object* v___x_2408_, lean_object* v_a_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__0(v___x_2408_, v_a_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec_ref(v_a_2409_);
return v_res_2418_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2419_; 
v___x_2419_ = l_instMonadEIO(lean_box(0));
return v___x_2419_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1(void){
_start:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2420_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0);
v___x_2421_ = l_StateRefT_x27_instMonad___redArg(v___x_2420_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__1___boxed(lean_object* v_acc_2428_, lean_object* v_declInfos_2429_, lean_object* v_k_2430_, lean_object* v_kind_2431_, lean_object* v_x_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
uint8_t v_kind_boxed_2441_; lean_object* v_res_2442_; 
v_kind_boxed_2441_ = lean_unbox(v_kind_2431_);
v_res_2442_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__1(v_acc_2428_, v_declInfos_2429_, v_k_2430_, v_kind_boxed_2441_, v_x_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
lean_dec_ref(v___y_2433_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(lean_object* v_declInfos_2443_, lean_object* v_k_2444_, uint8_t v_kind_2445_, lean_object* v_acc_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v___x_2455_; lean_object* v_toApplicative_2456_; lean_object* v_toFunctor_2457_; lean_object* v_toSeq_2458_; lean_object* v_toSeqLeft_2459_; lean_object* v_toSeqRight_2460_; lean_object* v___f_2461_; lean_object* v___f_2462_; lean_object* v___f_2463_; lean_object* v___f_2464_; lean_object* v___x_2465_; lean_object* v___f_2466_; lean_object* v___f_2467_; lean_object* v___f_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v_toApplicative_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2552_; 
v___x_2455_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1);
v_toApplicative_2456_ = lean_ctor_get(v___x_2455_, 0);
v_toFunctor_2457_ = lean_ctor_get(v_toApplicative_2456_, 0);
v_toSeq_2458_ = lean_ctor_get(v_toApplicative_2456_, 2);
v_toSeqLeft_2459_ = lean_ctor_get(v_toApplicative_2456_, 3);
v_toSeqRight_2460_ = lean_ctor_get(v_toApplicative_2456_, 4);
v___f_2461_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__2));
v___f_2462_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__3));
lean_inc_ref_n(v_toFunctor_2457_, 2);
v___f_2463_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2463_, 0, v_toFunctor_2457_);
v___f_2464_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2464_, 0, v_toFunctor_2457_);
v___x_2465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___f_2463_);
lean_ctor_set(v___x_2465_, 1, v___f_2464_);
lean_inc(v_toSeqRight_2460_);
v___f_2466_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2466_, 0, v_toSeqRight_2460_);
lean_inc(v_toSeqLeft_2459_);
v___f_2467_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2467_, 0, v_toSeqLeft_2459_);
lean_inc(v_toSeq_2458_);
v___f_2468_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2468_, 0, v_toSeq_2458_);
v___x_2469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2465_);
lean_ctor_set(v___x_2469_, 1, v___f_2461_);
lean_ctor_set(v___x_2469_, 2, v___f_2468_);
lean_ctor_set(v___x_2469_, 3, v___f_2467_);
lean_ctor_set(v___x_2469_, 4, v___f_2466_);
v___x_2470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2469_);
lean_ctor_set(v___x_2470_, 1, v___f_2462_);
v___x_2471_ = l_StateRefT_x27_instMonad___redArg(v___x_2470_);
v_toApplicative_2472_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2552_ == 0)
{
lean_object* v_unused_2553_; 
v_unused_2553_ = lean_ctor_get(v___x_2471_, 1);
lean_dec(v_unused_2553_);
v___x_2474_ = v___x_2471_;
v_isShared_2475_ = v_isSharedCheck_2552_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_toApplicative_2472_);
lean_dec(v___x_2471_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2552_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v_toFunctor_2476_; lean_object* v_toSeq_2477_; lean_object* v_toSeqLeft_2478_; lean_object* v_toSeqRight_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2550_; 
v_toFunctor_2476_ = lean_ctor_get(v_toApplicative_2472_, 0);
v_toSeq_2477_ = lean_ctor_get(v_toApplicative_2472_, 2);
v_toSeqLeft_2478_ = lean_ctor_get(v_toApplicative_2472_, 3);
v_toSeqRight_2479_ = lean_ctor_get(v_toApplicative_2472_, 4);
v_isSharedCheck_2550_ = !lean_is_exclusive(v_toApplicative_2472_);
if (v_isSharedCheck_2550_ == 0)
{
lean_object* v_unused_2551_; 
v_unused_2551_ = lean_ctor_get(v_toApplicative_2472_, 1);
lean_dec(v_unused_2551_);
v___x_2481_ = v_toApplicative_2472_;
v_isShared_2482_ = v_isSharedCheck_2550_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_toSeqRight_2479_);
lean_inc(v_toSeqLeft_2478_);
lean_inc(v_toSeq_2477_);
lean_inc(v_toFunctor_2476_);
lean_dec(v_toApplicative_2472_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2550_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___f_2483_; lean_object* v___f_2484_; lean_object* v___f_2485_; lean_object* v___f_2486_; lean_object* v___x_2487_; lean_object* v___f_2488_; lean_object* v___f_2489_; lean_object* v___f_2490_; lean_object* v___x_2492_; 
v___f_2483_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__4));
v___f_2484_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__5));
lean_inc_ref(v_toFunctor_2476_);
v___f_2485_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2485_, 0, v_toFunctor_2476_);
v___f_2486_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2486_, 0, v_toFunctor_2476_);
v___x_2487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2487_, 0, v___f_2485_);
lean_ctor_set(v___x_2487_, 1, v___f_2486_);
v___f_2488_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2488_, 0, v_toSeqRight_2479_);
v___f_2489_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2489_, 0, v_toSeqLeft_2478_);
v___f_2490_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2490_, 0, v_toSeq_2477_);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 4, v___f_2488_);
lean_ctor_set(v___x_2481_, 3, v___f_2489_);
lean_ctor_set(v___x_2481_, 2, v___f_2490_);
lean_ctor_set(v___x_2481_, 1, v___f_2483_);
lean_ctor_set(v___x_2481_, 0, v___x_2487_);
v___x_2492_ = v___x_2481_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v___x_2487_);
lean_ctor_set(v_reuseFailAlloc_2549_, 1, v___f_2483_);
lean_ctor_set(v_reuseFailAlloc_2549_, 2, v___f_2490_);
lean_ctor_set(v_reuseFailAlloc_2549_, 3, v___f_2489_);
lean_ctor_set(v_reuseFailAlloc_2549_, 4, v___f_2488_);
v___x_2492_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
lean_object* v___x_2494_; 
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 1, v___f_2484_);
lean_ctor_set(v___x_2474_, 0, v___x_2492_);
v___x_2494_ = v___x_2474_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v___x_2492_);
lean_ctor_set(v_reuseFailAlloc_2548_, 1, v___f_2484_);
v___x_2494_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
lean_object* v___x_2495_; lean_object* v_toApplicative_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2546_; 
v___x_2495_ = l_StateRefT_x27_instMonad___redArg(v___x_2494_);
v_toApplicative_2496_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2546_ == 0)
{
lean_object* v_unused_2547_; 
v_unused_2547_ = lean_ctor_get(v___x_2495_, 1);
lean_dec(v_unused_2547_);
v___x_2498_ = v___x_2495_;
v_isShared_2499_ = v_isSharedCheck_2546_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_toApplicative_2496_);
lean_dec(v___x_2495_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2546_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v_toFunctor_2500_; lean_object* v_toSeq_2501_; lean_object* v_toSeqLeft_2502_; lean_object* v_toSeqRight_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2544_; 
v_toFunctor_2500_ = lean_ctor_get(v_toApplicative_2496_, 0);
v_toSeq_2501_ = lean_ctor_get(v_toApplicative_2496_, 2);
v_toSeqLeft_2502_ = lean_ctor_get(v_toApplicative_2496_, 3);
v_toSeqRight_2503_ = lean_ctor_get(v_toApplicative_2496_, 4);
v_isSharedCheck_2544_ = !lean_is_exclusive(v_toApplicative_2496_);
if (v_isSharedCheck_2544_ == 0)
{
lean_object* v_unused_2545_; 
v_unused_2545_ = lean_ctor_get(v_toApplicative_2496_, 1);
lean_dec(v_unused_2545_);
v___x_2505_ = v_toApplicative_2496_;
v_isShared_2506_ = v_isSharedCheck_2544_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_toSeqRight_2503_);
lean_inc(v_toSeqLeft_2502_);
lean_inc(v_toSeq_2501_);
lean_inc(v_toFunctor_2500_);
lean_dec(v_toApplicative_2496_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2544_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___f_2507_; lean_object* v___f_2508_; lean_object* v___f_2509_; lean_object* v___f_2510_; lean_object* v___x_2511_; lean_object* v___f_2512_; lean_object* v___f_2513_; lean_object* v___f_2514_; lean_object* v___x_2516_; 
v___f_2507_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__6));
v___f_2508_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__7));
lean_inc_ref(v_toFunctor_2500_);
v___f_2509_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2509_, 0, v_toFunctor_2500_);
v___f_2510_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2510_, 0, v_toFunctor_2500_);
v___x_2511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2511_, 0, v___f_2509_);
lean_ctor_set(v___x_2511_, 1, v___f_2510_);
v___f_2512_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2512_, 0, v_toSeqRight_2503_);
v___f_2513_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2513_, 0, v_toSeqLeft_2502_);
v___f_2514_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2514_, 0, v_toSeq_2501_);
if (v_isShared_2506_ == 0)
{
lean_ctor_set(v___x_2505_, 4, v___f_2512_);
lean_ctor_set(v___x_2505_, 3, v___f_2513_);
lean_ctor_set(v___x_2505_, 2, v___f_2514_);
lean_ctor_set(v___x_2505_, 1, v___f_2507_);
lean_ctor_set(v___x_2505_, 0, v___x_2511_);
v___x_2516_ = v___x_2505_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v___x_2511_);
lean_ctor_set(v_reuseFailAlloc_2543_, 1, v___f_2507_);
lean_ctor_set(v_reuseFailAlloc_2543_, 2, v___f_2514_);
lean_ctor_set(v_reuseFailAlloc_2543_, 3, v___f_2513_);
lean_ctor_set(v_reuseFailAlloc_2543_, 4, v___f_2512_);
v___x_2516_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
lean_object* v___x_2518_; 
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 1, v___f_2508_);
lean_ctor_set(v___x_2498_, 0, v___x_2516_);
v___x_2518_ = v___x_2498_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v___x_2516_);
lean_ctor_set(v_reuseFailAlloc_2542_, 1, v___f_2508_);
v___x_2518_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; uint8_t v___x_2522_; 
v___x_2519_ = l_ReaderT_instMonad___redArg(v___x_2518_);
v___x_2520_ = lean_array_get_size(v_acc_2446_);
v___x_2521_ = lean_array_get_size(v_declInfos_2443_);
v___x_2522_ = lean_nat_dec_lt(v___x_2520_, v___x_2521_);
if (v___x_2522_ == 0)
{
lean_object* v___x_2523_; 
lean_dec_ref(v___x_2519_);
lean_dec_ref(v_declInfos_2443_);
lean_inc(v___y_2453_);
lean_inc_ref(v___y_2452_);
lean_inc(v___y_2451_);
lean_inc_ref(v___y_2450_);
lean_inc(v___y_2449_);
lean_inc_ref(v___y_2448_);
lean_inc_ref(v___y_2447_);
v___x_2523_ = lean_apply_9(v_k_2444_, v_acc_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, lean_box(0));
return v___x_2523_;
}
else
{
lean_object* v___f_2524_; lean_object* v___x_2525_; uint8_t v___x_2526_; lean_object* v___f_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v_snd_2532_; lean_object* v_fst_2533_; lean_object* v_fst_2534_; lean_object* v_snd_2535_; lean_object* v___x_2536_; 
v___f_2524_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2524_, 0, v___x_2519_);
v___x_2525_ = lean_box(0);
v___x_2526_ = 0;
v___f_2527_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2527_, 0, v___f_2524_);
v___x_2528_ = lean_box(v___x_2526_);
v___x_2529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2528_);
lean_ctor_set(v___x_2529_, 1, v___f_2527_);
v___x_2530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2525_);
lean_ctor_set(v___x_2530_, 1, v___x_2529_);
v___x_2531_ = lean_array_get(v___x_2530_, v_declInfos_2443_, v___x_2520_);
lean_dec_ref(v___x_2530_);
v_snd_2532_ = lean_ctor_get(v___x_2531_, 1);
lean_inc(v_snd_2532_);
v_fst_2533_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_fst_2533_);
lean_dec(v___x_2531_);
v_fst_2534_ = lean_ctor_get(v_snd_2532_, 0);
lean_inc(v_fst_2534_);
v_snd_2535_ = lean_ctor_get(v_snd_2532_, 1);
lean_inc(v_snd_2535_);
lean_dec(v_snd_2532_);
lean_inc(v___y_2453_);
lean_inc_ref(v___y_2452_);
lean_inc(v___y_2451_);
lean_inc_ref(v___y_2450_);
lean_inc(v___y_2449_);
lean_inc_ref(v___y_2448_);
lean_inc_ref(v___y_2447_);
lean_inc_ref(v_acc_2446_);
v___x_2536_ = lean_apply_9(v_snd_2535_, v_acc_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, lean_box(0));
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_a_2537_; lean_object* v___x_2538_; lean_object* v___f_2539_; uint8_t v___x_2540_; lean_object* v___x_2541_; 
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc(v_a_2537_);
lean_dec_ref(v___x_2536_);
v___x_2538_ = lean_box(v_kind_2445_);
v___f_2539_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__1___boxed), 13, 4);
lean_closure_set(v___f_2539_, 0, v_acc_2446_);
lean_closure_set(v___f_2539_, 1, v_declInfos_2443_);
lean_closure_set(v___f_2539_, 2, v_k_2444_);
lean_closure_set(v___f_2539_, 3, v___x_2538_);
v___x_2540_ = lean_unbox(v_fst_2534_);
lean_dec(v_fst_2534_);
v___x_2541_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_fst_2533_, v___x_2540_, v_a_2537_, v___f_2539_, v_kind_2445_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
return v___x_2541_;
}
else
{
lean_dec(v_fst_2534_);
lean_dec(v_fst_2533_);
lean_dec_ref(v_acc_2446_);
lean_dec_ref(v_k_2444_);
lean_dec_ref(v_declInfos_2443_);
return v___x_2536_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__1(lean_object* v_acc_2554_, lean_object* v_declInfos_2555_, lean_object* v_k_2556_, uint8_t v_kind_2557_, lean_object* v_x_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2567_ = lean_array_push(v_acc_2554_, v_x_2558_);
v___x_2568_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(v_declInfos_2555_, v_k_2556_, v_kind_2557_, v___x_2567_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___boxed(lean_object* v_declInfos_2569_, lean_object* v_k_2570_, lean_object* v_kind_2571_, lean_object* v_acc_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
uint8_t v_kind_boxed_2581_; lean_object* v_res_2582_; 
v_kind_boxed_2581_ = lean_unbox(v_kind_2571_);
v_res_2582_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(v_declInfos_2569_, v_k_2570_, v_kind_boxed_2581_, v_acc_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec_ref(v___y_2573_);
return v_res_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7(lean_object* v_declInfos_2585_, lean_object* v_k_2586_, uint8_t v_kind_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2596_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___closed__0));
v___x_2597_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(v_declInfos_2585_, v_k_2586_, v_kind_2587_, v___x_2596_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___boxed(lean_object* v_declInfos_2598_, lean_object* v_k_2599_, lean_object* v_kind_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
uint8_t v_kind_boxed_2609_; lean_object* v_res_2610_; 
v_kind_boxed_2609_ = lean_unbox(v_kind_2600_);
v_res_2610_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7(v_declInfos_2598_, v_k_2599_, v_kind_boxed_2609_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec_ref(v___y_2601_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(size_t v_sz_2611_, size_t v_i_2612_, lean_object* v_bs_2613_){
_start:
{
uint8_t v___x_2614_; 
v___x_2614_ = lean_usize_dec_lt(v_i_2612_, v_sz_2611_);
if (v___x_2614_ == 0)
{
return v_bs_2613_;
}
else
{
lean_object* v_v_2615_; lean_object* v_fst_2616_; lean_object* v_snd_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2633_; 
v_v_2615_ = lean_array_uget(v_bs_2613_, v_i_2612_);
v_fst_2616_ = lean_ctor_get(v_v_2615_, 0);
v_snd_2617_ = lean_ctor_get(v_v_2615_, 1);
v_isSharedCheck_2633_ = !lean_is_exclusive(v_v_2615_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2619_ = v_v_2615_;
v_isShared_2620_ = v_isSharedCheck_2633_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_snd_2617_);
lean_inc(v_fst_2616_);
lean_dec(v_v_2615_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2633_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2621_; lean_object* v_bs_x27_2622_; uint8_t v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2626_; 
v___x_2621_ = lean_unsigned_to_nat(0u);
v_bs_x27_2622_ = lean_array_uset(v_bs_2613_, v_i_2612_, v___x_2621_);
v___x_2623_ = 0;
v___x_2624_ = lean_box(v___x_2623_);
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 0, v___x_2624_);
v___x_2626_ = v___x_2619_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v___x_2624_);
lean_ctor_set(v_reuseFailAlloc_2632_, 1, v_snd_2617_);
v___x_2626_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
lean_object* v___x_2627_; size_t v___x_2628_; size_t v___x_2629_; lean_object* v___x_2630_; 
v___x_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2627_, 0, v_fst_2616_);
lean_ctor_set(v___x_2627_, 1, v___x_2626_);
v___x_2628_ = ((size_t)1ULL);
v___x_2629_ = lean_usize_add(v_i_2612_, v___x_2628_);
v___x_2630_ = lean_array_uset(v_bs_x27_2622_, v_i_2612_, v___x_2627_);
v_i_2612_ = v___x_2629_;
v_bs_2613_ = v___x_2630_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6___boxed(lean_object* v_sz_2634_, lean_object* v_i_2635_, lean_object* v_bs_2636_){
_start:
{
size_t v_sz_boxed_2637_; size_t v_i_boxed_2638_; lean_object* v_res_2639_; 
v_sz_boxed_2637_ = lean_unbox_usize(v_sz_2634_);
lean_dec(v_sz_2634_);
v_i_boxed_2638_ = lean_unbox_usize(v_i_2635_);
lean_dec(v_i_2635_);
v_res_2639_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(v_sz_boxed_2637_, v_i_boxed_2638_, v_bs_2636_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(lean_object* v_declInfos_2640_, lean_object* v_k_2641_, uint8_t v_kind_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
size_t v_sz_2651_; size_t v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
v_sz_2651_ = lean_array_size(v_declInfos_2640_);
v___x_2652_ = ((size_t)0ULL);
v___x_2653_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(v_sz_2651_, v___x_2652_, v_declInfos_2640_);
v___x_2654_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7(v___x_2653_, v_k_2641_, v_kind_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4___boxed(lean_object* v_declInfos_2655_, lean_object* v_k_2656_, lean_object* v_kind_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
uint8_t v_kind_boxed_2666_; lean_object* v_res_2667_; 
v_kind_boxed_2666_ = lean_unbox(v_kind_2657_);
v_res_2667_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(v_declInfos_2655_, v_k_2656_, v_kind_boxed_2666_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec_ref(v___y_2658_);
return v_res_2667_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0(uint8_t v___y_2675_, uint8_t v_suppressElabErrors_2676_, lean_object* v_x_2677_){
_start:
{
if (lean_obj_tag(v_x_2677_) == 1)
{
lean_object* v_pre_2678_; 
v_pre_2678_ = lean_ctor_get(v_x_2677_, 0);
switch(lean_obj_tag(v_pre_2678_))
{
case 1:
{
lean_object* v_pre_2679_; 
v_pre_2679_ = lean_ctor_get(v_pre_2678_, 0);
switch(lean_obj_tag(v_pre_2679_))
{
case 0:
{
lean_object* v_str_2680_; lean_object* v_str_2681_; lean_object* v___x_2682_; uint8_t v___x_2683_; 
v_str_2680_ = lean_ctor_get(v_x_2677_, 1);
v_str_2681_ = lean_ctor_get(v_pre_2678_, 1);
v___x_2682_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65));
v___x_2683_ = lean_string_dec_eq(v_str_2681_, v___x_2682_);
if (v___x_2683_ == 0)
{
lean_object* v___x_2684_; uint8_t v___x_2685_; 
v___x_2684_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__0));
v___x_2685_ = lean_string_dec_eq(v_str_2681_, v___x_2684_);
if (v___x_2685_ == 0)
{
return v___y_2675_;
}
else
{
lean_object* v___x_2686_; uint8_t v___x_2687_; 
v___x_2686_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__1));
v___x_2687_ = lean_string_dec_eq(v_str_2680_, v___x_2686_);
if (v___x_2687_ == 0)
{
return v___y_2675_;
}
else
{
return v_suppressElabErrors_2676_;
}
}
}
else
{
lean_object* v___x_2688_; uint8_t v___x_2689_; 
v___x_2688_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__2));
v___x_2689_ = lean_string_dec_eq(v_str_2680_, v___x_2688_);
if (v___x_2689_ == 0)
{
return v___y_2675_;
}
else
{
return v_suppressElabErrors_2676_;
}
}
}
case 1:
{
lean_object* v_pre_2690_; 
v_pre_2690_ = lean_ctor_get(v_pre_2679_, 0);
if (lean_obj_tag(v_pre_2690_) == 0)
{
lean_object* v_str_2691_; lean_object* v_str_2692_; lean_object* v_str_2693_; lean_object* v___x_2694_; uint8_t v___x_2695_; 
v_str_2691_ = lean_ctor_get(v_x_2677_, 1);
v_str_2692_ = lean_ctor_get(v_pre_2678_, 1);
v_str_2693_ = lean_ctor_get(v_pre_2679_, 1);
v___x_2694_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__3));
v___x_2695_ = lean_string_dec_eq(v_str_2693_, v___x_2694_);
if (v___x_2695_ == 0)
{
return v___y_2675_;
}
else
{
lean_object* v___x_2696_; uint8_t v___x_2697_; 
v___x_2696_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__4));
v___x_2697_ = lean_string_dec_eq(v_str_2692_, v___x_2696_);
if (v___x_2697_ == 0)
{
return v___y_2675_;
}
else
{
lean_object* v___x_2698_; uint8_t v___x_2699_; 
v___x_2698_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__5));
v___x_2699_ = lean_string_dec_eq(v_str_2691_, v___x_2698_);
if (v___x_2699_ == 0)
{
return v___y_2675_;
}
else
{
return v_suppressElabErrors_2676_;
}
}
}
}
else
{
return v___y_2675_;
}
}
default: 
{
return v___y_2675_;
}
}
}
case 0:
{
lean_object* v_str_2700_; lean_object* v___x_2701_; uint8_t v___x_2702_; 
v_str_2700_ = lean_ctor_get(v_x_2677_, 1);
v___x_2701_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__6));
v___x_2702_ = lean_string_dec_eq(v_str_2700_, v___x_2701_);
if (v___x_2702_ == 0)
{
return v___y_2675_;
}
else
{
return v_suppressElabErrors_2676_;
}
}
default: 
{
return v___y_2675_;
}
}
}
else
{
return v___y_2675_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___boxed(lean_object* v___y_2703_, lean_object* v_suppressElabErrors_2704_, lean_object* v_x_2705_){
_start:
{
uint8_t v___y_79743__boxed_2706_; uint8_t v_suppressElabErrors_boxed_2707_; uint8_t v_res_2708_; lean_object* v_r_2709_; 
v___y_79743__boxed_2706_ = lean_unbox(v___y_2703_);
v_suppressElabErrors_boxed_2707_ = lean_unbox(v_suppressElabErrors_2704_);
v_res_2708_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0(v___y_79743__boxed_2706_, v_suppressElabErrors_boxed_2707_, v_x_2705_);
lean_dec(v_x_2705_);
v_r_2709_ = lean_box(v_res_2708_);
return v_r_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg(lean_object* v_ref_2710_, lean_object* v_msgData_2711_, uint8_t v_severity_2712_, uint8_t v_isSilent_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_){
_start:
{
uint8_t v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; uint8_t v___y_2724_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2756_; uint8_t v___y_2757_; lean_object* v___y_2758_; uint8_t v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; uint8_t v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2781_; uint8_t v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; uint8_t v___y_2785_; lean_object* v___y_2786_; uint8_t v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2792_; uint8_t v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v___y_2796_; uint8_t v___y_2797_; uint8_t v___y_2798_; uint8_t v___x_2803_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; uint8_t v___y_2809_; uint8_t v___y_2810_; uint8_t v___y_2811_; uint8_t v___y_2813_; uint8_t v___x_2828_; 
v___x_2803_ = 2;
v___x_2828_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2712_, v___x_2803_);
if (v___x_2828_ == 0)
{
v___y_2813_ = v___x_2828_;
goto v___jp_2812_;
}
else
{
uint8_t v___x_2829_; 
lean_inc_ref(v_msgData_2711_);
v___x_2829_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2711_);
v___y_2813_ = v___x_2829_;
goto v___jp_2812_;
}
v___jp_2719_:
{
lean_object* v___x_2729_; lean_object* v_currNamespace_2730_; lean_object* v_openDecls_2731_; lean_object* v_env_2732_; lean_object* v_nextMacroScope_2733_; lean_object* v_ngen_2734_; lean_object* v_auxDeclNGen_2735_; lean_object* v_traceState_2736_; lean_object* v_cache_2737_; lean_object* v_messages_2738_; lean_object* v_infoState_2739_; lean_object* v_snapshotTasks_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2754_; 
v___x_2729_ = lean_st_ref_take(v___y_2728_);
v_currNamespace_2730_ = lean_ctor_get(v___y_2727_, 6);
v_openDecls_2731_ = lean_ctor_get(v___y_2727_, 7);
v_env_2732_ = lean_ctor_get(v___x_2729_, 0);
v_nextMacroScope_2733_ = lean_ctor_get(v___x_2729_, 1);
v_ngen_2734_ = lean_ctor_get(v___x_2729_, 2);
v_auxDeclNGen_2735_ = lean_ctor_get(v___x_2729_, 3);
v_traceState_2736_ = lean_ctor_get(v___x_2729_, 4);
v_cache_2737_ = lean_ctor_get(v___x_2729_, 5);
v_messages_2738_ = lean_ctor_get(v___x_2729_, 6);
v_infoState_2739_ = lean_ctor_get(v___x_2729_, 7);
v_snapshotTasks_2740_ = lean_ctor_get(v___x_2729_, 8);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2742_ = v___x_2729_;
v_isShared_2743_ = v_isSharedCheck_2754_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_snapshotTasks_2740_);
lean_inc(v_infoState_2739_);
lean_inc(v_messages_2738_);
lean_inc(v_cache_2737_);
lean_inc(v_traceState_2736_);
lean_inc(v_auxDeclNGen_2735_);
lean_inc(v_ngen_2734_);
lean_inc(v_nextMacroScope_2733_);
lean_inc(v_env_2732_);
lean_dec(v___x_2729_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2754_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2749_; 
lean_inc(v_openDecls_2731_);
lean_inc(v_currNamespace_2730_);
v___x_2744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2744_, 0, v_currNamespace_2730_);
lean_ctor_set(v___x_2744_, 1, v_openDecls_2731_);
v___x_2745_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2744_);
lean_ctor_set(v___x_2745_, 1, v___y_2725_);
lean_inc_ref(v___y_2726_);
lean_inc_ref(v___y_2722_);
v___x_2746_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2746_, 0, v___y_2722_);
lean_ctor_set(v___x_2746_, 1, v___y_2723_);
lean_ctor_set(v___x_2746_, 2, v___y_2721_);
lean_ctor_set(v___x_2746_, 3, v___y_2726_);
lean_ctor_set(v___x_2746_, 4, v___x_2745_);
lean_ctor_set_uint8(v___x_2746_, sizeof(void*)*5, v___y_2720_);
lean_ctor_set_uint8(v___x_2746_, sizeof(void*)*5 + 1, v___y_2724_);
lean_ctor_set_uint8(v___x_2746_, sizeof(void*)*5 + 2, v_isSilent_2713_);
v___x_2747_ = l_Lean_MessageLog_add(v___x_2746_, v_messages_2738_);
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 6, v___x_2747_);
v___x_2749_ = v___x_2742_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_env_2732_);
lean_ctor_set(v_reuseFailAlloc_2753_, 1, v_nextMacroScope_2733_);
lean_ctor_set(v_reuseFailAlloc_2753_, 2, v_ngen_2734_);
lean_ctor_set(v_reuseFailAlloc_2753_, 3, v_auxDeclNGen_2735_);
lean_ctor_set(v_reuseFailAlloc_2753_, 4, v_traceState_2736_);
lean_ctor_set(v_reuseFailAlloc_2753_, 5, v_cache_2737_);
lean_ctor_set(v_reuseFailAlloc_2753_, 6, v___x_2747_);
lean_ctor_set(v_reuseFailAlloc_2753_, 7, v_infoState_2739_);
lean_ctor_set(v_reuseFailAlloc_2753_, 8, v_snapshotTasks_2740_);
v___x_2749_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2750_ = lean_st_ref_set(v___y_2728_, v___x_2749_);
v___x_2751_ = lean_box(0);
v___x_2752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2751_);
return v___x_2752_;
}
}
}
v___jp_2755_:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2779_; 
v___x_2764_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2711_);
v___x_2765_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(v___x_2764_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2768_ = v___x_2765_;
v_isShared_2769_ = v_isSharedCheck_2779_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v___x_2765_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2779_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
lean_inc_ref_n(v___y_2760_, 2);
v___x_2770_ = l_Lean_FileMap_toPosition(v___y_2760_, v___y_2761_);
lean_dec(v___y_2761_);
v___x_2771_ = l_Lean_FileMap_toPosition(v___y_2760_, v___y_2763_);
lean_dec(v___y_2763_);
v___x_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2771_);
v___x_2773_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__63));
if (v___y_2762_ == 0)
{
lean_del_object(v___x_2768_);
lean_dec_ref(v___y_2756_);
v___y_2720_ = v___y_2757_;
v___y_2721_ = v___x_2772_;
v___y_2722_ = v___y_2758_;
v___y_2723_ = v___x_2770_;
v___y_2724_ = v___y_2759_;
v___y_2725_ = v_a_2766_;
v___y_2726_ = v___x_2773_;
v___y_2727_ = v___y_2716_;
v___y_2728_ = v___y_2717_;
goto v___jp_2719_;
}
else
{
uint8_t v___x_2774_; 
lean_inc(v_a_2766_);
v___x_2774_ = l_Lean_MessageData_hasTag(v___y_2756_, v_a_2766_);
if (v___x_2774_ == 0)
{
lean_object* v___x_2775_; lean_object* v___x_2777_; 
lean_dec_ref(v___x_2772_);
lean_dec_ref(v___x_2770_);
lean_dec(v_a_2766_);
v___x_2775_ = lean_box(0);
if (v_isShared_2769_ == 0)
{
lean_ctor_set(v___x_2768_, 0, v___x_2775_);
v___x_2777_ = v___x_2768_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2775_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
else
{
lean_del_object(v___x_2768_);
v___y_2720_ = v___y_2757_;
v___y_2721_ = v___x_2772_;
v___y_2722_ = v___y_2758_;
v___y_2723_ = v___x_2770_;
v___y_2724_ = v___y_2759_;
v___y_2725_ = v_a_2766_;
v___y_2726_ = v___x_2773_;
v___y_2727_ = v___y_2716_;
v___y_2728_ = v___y_2717_;
goto v___jp_2719_;
}
}
}
}
v___jp_2780_:
{
lean_object* v___x_2789_; 
v___x_2789_ = l_Lean_Syntax_getTailPos_x3f(v___y_2786_, v___y_2782_);
lean_dec(v___y_2786_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_inc(v___y_2788_);
v___y_2756_ = v___y_2781_;
v___y_2757_ = v___y_2782_;
v___y_2758_ = v___y_2783_;
v___y_2759_ = v___y_2785_;
v___y_2760_ = v___y_2784_;
v___y_2761_ = v___y_2788_;
v___y_2762_ = v___y_2787_;
v___y_2763_ = v___y_2788_;
goto v___jp_2755_;
}
else
{
lean_object* v_val_2790_; 
v_val_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_val_2790_);
lean_dec_ref(v___x_2789_);
v___y_2756_ = v___y_2781_;
v___y_2757_ = v___y_2782_;
v___y_2758_ = v___y_2783_;
v___y_2759_ = v___y_2785_;
v___y_2760_ = v___y_2784_;
v___y_2761_ = v___y_2788_;
v___y_2762_ = v___y_2787_;
v___y_2763_ = v_val_2790_;
goto v___jp_2755_;
}
}
v___jp_2791_:
{
lean_object* v_ref_2799_; lean_object* v___x_2800_; 
v_ref_2799_ = l_Lean_replaceRef(v_ref_2710_, v___y_2795_);
v___x_2800_ = l_Lean_Syntax_getPos_x3f(v_ref_2799_, v___y_2793_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v___x_2801_; 
v___x_2801_ = lean_unsigned_to_nat(0u);
v___y_2781_ = v___y_2792_;
v___y_2782_ = v___y_2793_;
v___y_2783_ = v___y_2794_;
v___y_2784_ = v___y_2796_;
v___y_2785_ = v___y_2798_;
v___y_2786_ = v_ref_2799_;
v___y_2787_ = v___y_2797_;
v___y_2788_ = v___x_2801_;
goto v___jp_2780_;
}
else
{
lean_object* v_val_2802_; 
v_val_2802_ = lean_ctor_get(v___x_2800_, 0);
lean_inc(v_val_2802_);
lean_dec_ref(v___x_2800_);
v___y_2781_ = v___y_2792_;
v___y_2782_ = v___y_2793_;
v___y_2783_ = v___y_2794_;
v___y_2784_ = v___y_2796_;
v___y_2785_ = v___y_2798_;
v___y_2786_ = v_ref_2799_;
v___y_2787_ = v___y_2797_;
v___y_2788_ = v_val_2802_;
goto v___jp_2780_;
}
}
v___jp_2804_:
{
if (v___y_2811_ == 0)
{
v___y_2792_ = v___y_2808_;
v___y_2793_ = v___y_2810_;
v___y_2794_ = v___y_2805_;
v___y_2795_ = v___y_2806_;
v___y_2796_ = v___y_2807_;
v___y_2797_ = v___y_2809_;
v___y_2798_ = v_severity_2712_;
goto v___jp_2791_;
}
else
{
v___y_2792_ = v___y_2808_;
v___y_2793_ = v___y_2810_;
v___y_2794_ = v___y_2805_;
v___y_2795_ = v___y_2806_;
v___y_2796_ = v___y_2807_;
v___y_2797_ = v___y_2809_;
v___y_2798_ = v___x_2803_;
goto v___jp_2791_;
}
}
v___jp_2812_:
{
if (v___y_2813_ == 0)
{
lean_object* v_fileName_2814_; lean_object* v_fileMap_2815_; lean_object* v_options_2816_; lean_object* v_ref_2817_; uint8_t v_suppressElabErrors_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___f_2821_; uint8_t v___x_2822_; uint8_t v___x_2823_; 
v_fileName_2814_ = lean_ctor_get(v___y_2716_, 0);
v_fileMap_2815_ = lean_ctor_get(v___y_2716_, 1);
v_options_2816_ = lean_ctor_get(v___y_2716_, 2);
v_ref_2817_ = lean_ctor_get(v___y_2716_, 5);
v_suppressElabErrors_2818_ = lean_ctor_get_uint8(v___y_2716_, sizeof(void*)*14 + 1);
v___x_2819_ = lean_box(v___y_2813_);
v___x_2820_ = lean_box(v_suppressElabErrors_2818_);
v___f_2821_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2821_, 0, v___x_2819_);
lean_closure_set(v___f_2821_, 1, v___x_2820_);
v___x_2822_ = 1;
v___x_2823_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2712_, v___x_2822_);
if (v___x_2823_ == 0)
{
v___y_2805_ = v_fileName_2814_;
v___y_2806_ = v_ref_2817_;
v___y_2807_ = v_fileMap_2815_;
v___y_2808_ = v___f_2821_;
v___y_2809_ = v_suppressElabErrors_2818_;
v___y_2810_ = v___y_2813_;
v___y_2811_ = v___x_2823_;
goto v___jp_2804_;
}
else
{
lean_object* v___x_2824_; uint8_t v___x_2825_; 
v___x_2824_ = l_Lean_warningAsError;
v___x_2825_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5(v_options_2816_, v___x_2824_);
v___y_2805_ = v_fileName_2814_;
v___y_2806_ = v_ref_2817_;
v___y_2807_ = v_fileMap_2815_;
v___y_2808_ = v___f_2821_;
v___y_2809_ = v_suppressElabErrors_2818_;
v___y_2810_ = v___y_2813_;
v___y_2811_ = v___x_2825_;
goto v___jp_2804_;
}
}
else
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
lean_dec_ref(v_msgData_2711_);
v___x_2826_ = lean_box(0);
v___x_2827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2826_);
return v___x_2827_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___boxed(lean_object* v_ref_2830_, lean_object* v_msgData_2831_, lean_object* v_severity_2832_, lean_object* v_isSilent_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
uint8_t v_severity_boxed_2839_; uint8_t v_isSilent_boxed_2840_; lean_object* v_res_2841_; 
v_severity_boxed_2839_ = lean_unbox(v_severity_2832_);
v_isSilent_boxed_2840_ = lean_unbox(v_isSilent_2833_);
v_res_2841_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg(v_ref_2830_, v_msgData_2831_, v_severity_boxed_2839_, v_isSilent_boxed_2840_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v_ref_2830_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10(lean_object* v_msgData_2842_, uint8_t v_severity_2843_, uint8_t v_isSilent_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_){
_start:
{
lean_object* v_ref_2853_; lean_object* v___x_2854_; 
v_ref_2853_ = lean_ctor_get(v___y_2850_, 5);
v___x_2854_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg(v_ref_2853_, v_msgData_2842_, v_severity_2843_, v_isSilent_2844_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10___boxed(lean_object* v_msgData_2855_, lean_object* v_severity_2856_, lean_object* v_isSilent_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
uint8_t v_severity_boxed_2866_; uint8_t v_isSilent_boxed_2867_; lean_object* v_res_2868_; 
v_severity_boxed_2866_ = lean_unbox(v_severity_2856_);
v_isSilent_boxed_2867_ = lean_unbox(v_isSilent_2857_);
v_res_2868_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10(v_msgData_2855_, v_severity_boxed_2866_, v_isSilent_boxed_2867_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
lean_dec_ref(v___y_2858_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6(lean_object* v_msgData_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
uint8_t v___x_2878_; uint8_t v___x_2879_; lean_object* v___x_2880_; 
v___x_2878_ = 2;
v___x_2879_ = 0;
v___x_2880_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10(v_msgData_2869_, v___x_2878_, v___x_2879_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6___boxed(lean_object* v_msgData_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_){
_start:
{
lean_object* v_res_2890_; 
v_res_2890_ = l_Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6(v_msgData_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec_ref(v___y_2885_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
lean_dec_ref(v___y_2882_);
return v_res_2890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__8(lean_object* v_a_2891_, lean_object* v_as_2892_, size_t v_i_2893_, size_t v_stop_2894_, lean_object* v_b_2895_){
_start:
{
lean_object* v___y_2897_; uint8_t v___x_2901_; 
v___x_2901_ = lean_usize_dec_eq(v_i_2893_, v_stop_2894_);
if (v___x_2901_ == 0)
{
lean_object* v_reassigns_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; uint8_t v___x_2905_; 
v_reassigns_2902_ = lean_ctor_get(v_a_2891_, 1);
v___x_2903_ = lean_array_uget_borrowed(v_as_2892_, v_i_2893_);
v___x_2904_ = l_Lean_TSyntax_getId(v___x_2903_);
v___x_2905_ = l_Lean_NameSet_contains(v_reassigns_2902_, v___x_2904_);
lean_dec(v___x_2904_);
if (v___x_2905_ == 0)
{
v___y_2897_ = v_b_2895_;
goto v___jp_2896_;
}
else
{
lean_object* v___x_2906_; 
lean_inc(v___x_2903_);
v___x_2906_ = lean_array_push(v_b_2895_, v___x_2903_);
v___y_2897_ = v___x_2906_;
goto v___jp_2896_;
}
}
else
{
return v_b_2895_;
}
v___jp_2896_:
{
size_t v___x_2898_; size_t v___x_2899_; 
v___x_2898_ = ((size_t)1ULL);
v___x_2899_ = lean_usize_add(v_i_2893_, v___x_2898_);
v_i_2893_ = v___x_2899_;
v_b_2895_ = v___y_2897_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__8___boxed(lean_object* v_a_2907_, lean_object* v_as_2908_, lean_object* v_i_2909_, lean_object* v_stop_2910_, lean_object* v_b_2911_){
_start:
{
size_t v_i_boxed_2912_; size_t v_stop_boxed_2913_; lean_object* v_res_2914_; 
v_i_boxed_2912_ = lean_unbox_usize(v_i_2909_);
lean_dec(v_i_2909_);
v_stop_boxed_2913_ = lean_unbox_usize(v_stop_2910_);
lean_dec(v_stop_2910_);
v_res_2914_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__8(v_a_2907_, v_as_2908_, v_i_boxed_2912_, v_stop_boxed_2913_, v_b_2911_);
lean_dec_ref(v_as_2908_);
lean_dec_ref(v_a_2907_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__7(size_t v_sz_2915_, size_t v_i_2916_, lean_object* v_bs_2917_){
_start:
{
uint8_t v___x_2918_; 
v___x_2918_ = lean_usize_dec_lt(v_i_2916_, v_sz_2915_);
if (v___x_2918_ == 0)
{
return v_bs_2917_;
}
else
{
lean_object* v_v_2919_; lean_object* v___x_2920_; lean_object* v_bs_x27_2921_; lean_object* v___x_2922_; size_t v___x_2923_; size_t v___x_2924_; lean_object* v___x_2925_; 
v_v_2919_ = lean_array_uget(v_bs_2917_, v_i_2916_);
v___x_2920_ = lean_unsigned_to_nat(0u);
v_bs_x27_2921_ = lean_array_uset(v_bs_2917_, v_i_2916_, v___x_2920_);
v___x_2922_ = l_Lean_TSyntax_getId(v_v_2919_);
lean_dec(v_v_2919_);
v___x_2923_ = ((size_t)1ULL);
v___x_2924_ = lean_usize_add(v_i_2916_, v___x_2923_);
v___x_2925_ = lean_array_uset(v_bs_x27_2921_, v_i_2916_, v___x_2922_);
v_i_2916_ = v___x_2924_;
v_bs_2917_ = v___x_2925_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__7___boxed(lean_object* v_sz_2927_, lean_object* v_i_2928_, lean_object* v_bs_2929_){
_start:
{
size_t v_sz_boxed_2930_; size_t v_i_boxed_2931_; lean_object* v_res_2932_; 
v_sz_boxed_2930_ = lean_unbox_usize(v_sz_2927_);
lean_dec(v_sz_2927_);
v_i_boxed_2931_ = lean_unbox_usize(v_i_2928_);
lean_dec(v_i_2928_);
v_res_2932_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__7(v_sz_boxed_2930_, v_i_boxed_2931_, v_bs_2929_);
return v_res_2932_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___closed__12(void){
_start:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2953_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__11));
v___x_2954_ = l_Lean_stringToMessageData(v___x_2953_);
return v___x_2954_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___closed__14(void){
_start:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2956_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__13));
v___x_2957_ = l_Lean_stringToMessageData(v___x_2956_);
return v___x_2957_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___closed__16(void){
_start:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2959_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__15));
v___x_2960_ = l_Lean_stringToMessageData(v___x_2959_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor(lean_object* v_stx_2970_, lean_object* v_dec_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_){
_start:
{
lean_object* v___x_2980_; uint8_t v___x_2981_; 
v___x_2980_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
lean_inc(v_stx_2970_);
v___x_2981_ = l_Lean_Syntax_isOfKind(v_stx_2970_, v___x_2980_);
if (v___x_2981_ == 0)
{
lean_object* v___x_2982_; 
lean_dec_ref(v_dec_2971_);
lean_dec(v_stx_2970_);
v___x_2982_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_2982_;
}
else
{
lean_object* v___x_2983_; lean_object* v___x_2984_; uint8_t v___x_2985_; 
v___x_2983_ = lean_unsigned_to_nat(1u);
v___x_2984_ = l_Lean_Syntax_getArg(v_stx_2970_, v___x_2983_);
lean_inc(v___x_2984_);
v___x_2985_ = l_Lean_Syntax_matchesNull(v___x_2984_, v___x_2983_);
if (v___x_2985_ == 0)
{
lean_object* v___x_2986_; 
lean_dec(v___x_2984_);
lean_dec_ref(v_dec_2971_);
lean_dec(v_stx_2970_);
v___x_2986_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_2986_;
}
else
{
lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; uint8_t v___x_2990_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; uint8_t v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; lean_object* v___y_3007_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; uint8_t v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v_fst_3048_; lean_object* v_snd_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; uint8_t v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; uint8_t v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; uint8_t v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; uint8_t v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; uint8_t v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; uint8_t v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v_h_x3f_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; 
v___x_2987_ = lean_unsigned_to_nat(0u);
v___x_2988_ = l_Lean_Syntax_getArg(v___x_2984_, v___x_2987_);
lean_dec(v___x_2984_);
v___x_2989_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
lean_inc(v___x_2988_);
v___x_2990_ = l_Lean_Syntax_isOfKind(v___x_2988_, v___x_2989_);
if (v___x_2990_ == 0)
{
lean_object* v___x_3435_; 
lean_dec(v___x_2988_);
lean_dec_ref(v_dec_2971_);
lean_dec(v_stx_2970_);
v___x_3435_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_3435_;
}
else
{
lean_object* v___x_3436_; uint8_t v___x_3437_; 
v___x_3436_ = l_Lean_Syntax_getArg(v___x_2988_, v___x_2987_);
v___x_3437_ = l_Lean_Syntax_isNone(v___x_3436_);
if (v___x_3437_ == 0)
{
lean_object* v___x_3438_; uint8_t v___x_3439_; 
v___x_3438_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3436_);
v___x_3439_ = l_Lean_Syntax_matchesNull(v___x_3436_, v___x_3438_);
if (v___x_3439_ == 0)
{
lean_object* v___x_3440_; 
lean_dec(v___x_3436_);
lean_dec(v___x_2988_);
lean_dec_ref(v_dec_2971_);
lean_dec(v_stx_2970_);
v___x_3440_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_3440_;
}
else
{
lean_object* v_h_x3f_3441_; lean_object* v___x_3442_; 
v_h_x3f_3441_ = l_Lean_Syntax_getArg(v___x_3436_, v___x_2987_);
lean_dec(v___x_3436_);
v___x_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3442_, 0, v_h_x3f_3441_);
v_h_x3f_3313_ = v___x_3442_;
v___y_3314_ = v_a_2972_;
v___y_3315_ = v_a_2973_;
v___y_3316_ = v_a_2974_;
v___y_3317_ = v_a_2975_;
v___y_3318_ = v_a_2976_;
v___y_3319_ = v_a_2977_;
v___y_3320_ = v_a_2978_;
goto v___jp_3312_;
}
}
else
{
lean_object* v___x_3443_; 
lean_dec(v___x_3436_);
v___x_3443_ = lean_box(0);
v_h_x3f_3313_ = v___x_3443_;
v___y_3314_ = v_a_2972_;
v___y_3315_ = v_a_2973_;
v___y_3316_ = v_a_2974_;
v___y_3317_ = v_a_2975_;
v___y_3318_ = v_a_2976_;
v___y_3319_ = v_a_2977_;
v___y_3320_ = v_a_2978_;
goto v___jp_3312_;
}
}
v___jp_2991_:
{
uint8_t v___x_3012_; lean_object* v___x_3013_; 
v___x_3012_ = 0;
v___x_3013_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(v___y_3011_, v___y_3001_, v___x_3012_, v___y_3003_, v___y_3009_, v___y_3006_, v___y_3005_, v___y_3007_, v___y_3002_, v___y_3008_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v_a_3014_; lean_object* v_doBlockResultType_3015_; lean_object* v___x_3016_; lean_object* v___y_3017_; lean_object* v___x_3018_; lean_object* v___f_3019_; lean_object* v___x_3020_; 
v_a_3014_ = lean_ctor_get(v___x_3013_, 0);
lean_inc(v_a_3014_);
lean_dec_ref(v___x_3013_);
v_doBlockResultType_3015_ = lean_ctor_get(v___y_3003_, 3);
v___x_3016_ = lean_box(v___y_2996_);
lean_inc(v___y_2993_);
lean_inc_ref(v_doBlockResultType_3015_);
v___y_3017_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__10___boxed), 19, 11);
lean_closure_set(v___y_3017_, 0, v___x_3016_);
lean_closure_set(v___y_3017_, 1, v_dec_2971_);
lean_closure_set(v___y_3017_, 2, v___y_2992_);
lean_closure_set(v___y_3017_, 3, v_doBlockResultType_3015_);
lean_closure_set(v___y_3017_, 4, v___y_2995_);
lean_closure_set(v___y_3017_, 5, v___y_2993_);
lean_closure_set(v___y_3017_, 6, v___y_2994_);
lean_closure_set(v___y_3017_, 7, v___y_3000_);
lean_closure_set(v___y_3017_, 8, v___y_2998_);
lean_closure_set(v___y_3017_, 9, v___x_2987_);
lean_closure_set(v___y_3017_, 10, v___x_2983_);
v___x_3018_ = lean_box(v___x_2990_);
v___f_3019_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__11___boxed), 13, 4);
lean_closure_set(v___f_3019_, 0, v___y_2997_);
lean_closure_set(v___f_3019_, 1, v___y_3017_);
lean_closure_set(v___f_3019_, 2, v___x_2983_);
lean_closure_set(v___f_3019_, 3, v___x_3018_);
lean_inc_ref(v___y_3010_);
v___x_3020_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(v___y_2999_, v___y_3010_, v___f_3019_, v___y_3003_, v___y_3009_, v___y_3006_, v___y_3005_, v___y_3007_, v___y_3002_, v___y_3008_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v_a_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
lean_inc(v_a_3021_);
lean_dec_ref(v___x_3020_);
v___x_3022_ = l_Lean_Expr_app___override(v___y_3004_, v_a_3014_);
lean_inc_ref(v_doBlockResultType_3015_);
v___x_3023_ = l_Lean_Elab_Do_mkBindApp(v___y_3010_, v_doBlockResultType_3015_, v___x_3022_, v_a_3021_, v___y_3003_, v___y_3009_, v___y_3006_, v___y_3005_, v___y_3007_, v___y_3002_, v___y_3008_);
return v___x_3023_;
}
else
{
lean_dec(v_a_3014_);
lean_dec_ref(v___y_3010_);
lean_dec_ref(v___y_3004_);
return v___x_3020_;
}
}
else
{
lean_dec_ref(v___y_3010_);
lean_dec_ref(v___y_3004_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec(v___y_2997_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2994_);
lean_dec(v___y_2992_);
lean_dec_ref(v_dec_2971_);
return v___x_3013_;
}
}
v___jp_3024_:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3057_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17));
v___x_3058_ = l_Lean_Core_mkFreshUserName(v___x_3057_, v___y_3055_, v___y_3056_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; lean_object* v___x_3060_; lean_object* v___f_3061_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc_n(v_a_3059_, 2);
lean_dec_ref(v___x_3058_);
v___x_3060_ = lean_box(v___x_2990_);
lean_inc(v___y_3039_);
lean_inc_ref(v___y_3042_);
lean_inc(v___y_3031_);
lean_inc_ref(v___y_3032_);
v___f_3061_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__9___boxed), 20, 11);
lean_closure_set(v___f_3061_, 0, v___y_3032_);
lean_closure_set(v___f_3061_, 1, v___y_3031_);
lean_closure_set(v___f_3061_, 2, v___y_3042_);
lean_closure_set(v___f_3061_, 3, v___y_3027_);
lean_closure_set(v___f_3061_, 4, v___y_3036_);
lean_closure_set(v___f_3061_, 5, v___y_3026_);
lean_closure_set(v___f_3061_, 6, v___y_3034_);
lean_closure_set(v___f_3061_, 7, v___y_3037_);
lean_closure_set(v___f_3061_, 8, v___x_3060_);
lean_closure_set(v___f_3061_, 9, v___y_3039_);
lean_closure_set(v___f_3061_, 10, v_a_3059_);
if (lean_obj_tag(v___y_3045_) == 1)
{
if (lean_obj_tag(v_snd_3049_) == 1)
{
lean_object* v_val_3062_; lean_object* v_val_3063_; lean_object* v___f_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
lean_dec_ref(v___y_3044_);
v_val_3062_ = lean_ctor_get(v___y_3045_, 0);
lean_inc(v_val_3062_);
lean_dec_ref(v___y_3045_);
v_val_3063_ = lean_ctor_get(v_snd_3049_, 0);
lean_inc(v_val_3063_);
lean_dec_ref(v_snd_3049_);
v___f_3064_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__12___boxed), 16, 7);
lean_closure_set(v___f_3064_, 0, v___y_3041_);
lean_closure_set(v___f_3064_, 1, v___y_3028_);
lean_closure_set(v___f_3064_, 2, v___x_2987_);
lean_closure_set(v___f_3064_, 3, v___y_3030_);
lean_closure_set(v___f_3064_, 4, v___y_3035_);
lean_closure_set(v___f_3064_, 5, v_val_3063_);
lean_closure_set(v___f_3064_, 6, v___y_3029_);
v___x_3065_ = l_Lean_TSyntax_getId(v___y_3046_);
lean_dec(v___y_3046_);
v___x_3066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3065_);
lean_ctor_set(v___x_3066_, 1, v___y_3047_);
v___x_3067_ = l_Lean_TSyntax_getId(v_val_3062_);
lean_dec(v_val_3062_);
v___x_3068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3067_);
lean_ctor_set(v___x_3068_, 1, v___f_3064_);
v___x_3069_ = lean_unsigned_to_nat(2u);
v___x_3070_ = lean_mk_empty_array_with_capacity(v___x_3069_);
v___x_3071_ = lean_array_push(v___x_3070_, v___x_3066_);
v___x_3072_ = lean_array_push(v___x_3071_, v___x_3068_);
v___y_2992_ = v___y_3025_;
v___y_2993_ = v___y_3038_;
v___y_2994_ = v___y_3031_;
v___y_2995_ = v___y_3032_;
v___y_2996_ = v___y_3033_;
v___y_2997_ = v___y_3039_;
v___y_2998_ = v___y_3040_;
v___y_2999_ = v_a_3059_;
v___y_3000_ = v___y_3043_;
v___y_3001_ = v___f_3061_;
v___y_3002_ = v___y_3055_;
v___y_3003_ = v___y_3050_;
v___y_3004_ = v_fst_3048_;
v___y_3005_ = v___y_3053_;
v___y_3006_ = v___y_3052_;
v___y_3007_ = v___y_3054_;
v___y_3008_ = v___y_3056_;
v___y_3009_ = v___y_3051_;
v___y_3010_ = v___y_3042_;
v___y_3011_ = v___x_3072_;
goto v___jp_2991_;
}
else
{
lean_object* v___x_3073_; 
lean_dec_ref(v___y_3047_);
lean_dec(v___y_3046_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3035_);
lean_dec_ref(v___y_3030_);
lean_dec_ref(v___y_3029_);
lean_dec(v___y_3028_);
v___x_3073_ = lean_apply_2(v___y_3044_, v___y_3045_, v_snd_3049_);
v___y_2992_ = v___y_3025_;
v___y_2993_ = v___y_3038_;
v___y_2994_ = v___y_3031_;
v___y_2995_ = v___y_3032_;
v___y_2996_ = v___y_3033_;
v___y_2997_ = v___y_3039_;
v___y_2998_ = v___y_3040_;
v___y_2999_ = v_a_3059_;
v___y_3000_ = v___y_3043_;
v___y_3001_ = v___f_3061_;
v___y_3002_ = v___y_3055_;
v___y_3003_ = v___y_3050_;
v___y_3004_ = v_fst_3048_;
v___y_3005_ = v___y_3053_;
v___y_3006_ = v___y_3052_;
v___y_3007_ = v___y_3054_;
v___y_3008_ = v___y_3056_;
v___y_3009_ = v___y_3051_;
v___y_3010_ = v___y_3042_;
v___y_3011_ = v___x_3073_;
goto v___jp_2991_;
}
}
else
{
lean_object* v___x_3074_; 
lean_dec_ref(v___y_3047_);
lean_dec(v___y_3046_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3035_);
lean_dec_ref(v___y_3030_);
lean_dec_ref(v___y_3029_);
lean_dec(v___y_3028_);
v___x_3074_ = lean_apply_2(v___y_3044_, v___y_3045_, v_snd_3049_);
v___y_2992_ = v___y_3025_;
v___y_2993_ = v___y_3038_;
v___y_2994_ = v___y_3031_;
v___y_2995_ = v___y_3032_;
v___y_2996_ = v___y_3033_;
v___y_2997_ = v___y_3039_;
v___y_2998_ = v___y_3040_;
v___y_2999_ = v_a_3059_;
v___y_3000_ = v___y_3043_;
v___y_3001_ = v___f_3061_;
v___y_3002_ = v___y_3055_;
v___y_3003_ = v___y_3050_;
v___y_3004_ = v_fst_3048_;
v___y_3005_ = v___y_3053_;
v___y_3006_ = v___y_3052_;
v___y_3007_ = v___y_3054_;
v___y_3008_ = v___y_3056_;
v___y_3009_ = v___y_3051_;
v___y_3010_ = v___y_3042_;
v___y_3011_ = v___x_3074_;
goto v___jp_2991_;
}
}
else
{
lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3082_; 
lean_dec(v_snd_3049_);
lean_dec_ref(v_fst_3048_);
lean_dec_ref(v___y_3047_);
lean_dec(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec_ref(v___y_3043_);
lean_dec_ref(v___y_3042_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3040_);
lean_dec(v___y_3039_);
lean_dec(v___y_3037_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec_ref(v___y_3034_);
lean_dec_ref(v___y_3032_);
lean_dec(v___y_3031_);
lean_dec_ref(v___y_3030_);
lean_dec_ref(v___y_3029_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec(v___y_3026_);
lean_dec(v___y_3025_);
lean_dec_ref(v_dec_2971_);
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
v___jp_3083_:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___x_3118_ = lean_box(0);
lean_inc(v___y_3117_);
lean_inc_ref(v___y_3116_);
lean_inc(v___y_3115_);
lean_inc_ref(v___y_3114_);
lean_inc(v___y_3113_);
lean_inc_ref(v___y_3112_);
v___x_3119_ = lean_apply_8(v___y_3101_, v___x_3118_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, lean_box(0));
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_object* v_a_3120_; lean_object* v_m_3121_; lean_object* v_u_3122_; lean_object* v_v_3123_; lean_object* v___x_3124_; 
v_a_3120_ = lean_ctor_get(v___x_3119_, 0);
lean_inc(v_a_3120_);
lean_dec_ref(v___x_3119_);
v_m_3121_ = lean_ctor_get(v___y_3110_, 0);
v_u_3122_ = lean_ctor_get(v___y_3110_, 1);
v_v_3123_ = lean_ctor_get(v___y_3110_, 2);
lean_inc(v_u_3122_);
v___x_3124_ = l_Lean_Meta_mkProdMkN(v_a_3120_, v_u_3122_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
if (lean_obj_tag(v___x_3124_) == 0)
{
lean_object* v_a_3125_; 
v_a_3125_ = lean_ctor_get(v___x_3124_, 0);
lean_inc(v_a_3125_);
lean_dec_ref(v___x_3124_);
if (lean_obj_tag(v___y_3099_) == 0)
{
lean_object* v_fst_3126_; lean_object* v_snd_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3146_; 
v_fst_3126_ = lean_ctor_get(v_a_3125_, 0);
v_snd_3127_ = lean_ctor_get(v_a_3125_, 1);
v_isSharedCheck_3146_ = !lean_is_exclusive(v_a_3125_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3129_ = v_a_3125_;
v_isShared_3130_ = v_isSharedCheck_3146_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_snd_3127_);
lean_inc(v_fst_3126_);
lean_dec(v_a_3125_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3146_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3134_; 
v___x_3131_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__1));
v___x_3132_ = lean_box(0);
lean_inc(v_v_3123_);
if (v_isShared_3130_ == 0)
{
lean_ctor_set_tag(v___x_3129_, 1);
lean_ctor_set(v___x_3129_, 1, v___x_3132_);
lean_ctor_set(v___x_3129_, 0, v_v_3123_);
v___x_3134_ = v___x_3129_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_v_3123_);
lean_ctor_set(v_reuseFailAlloc_3145_, 1, v___x_3132_);
v___x_3134_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
lean_inc(v_u_3122_);
v___x_3135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3135_, 0, v_u_3122_);
lean_ctor_set(v___x_3135_, 1, v___x_3134_);
v___x_3136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3136_, 0, v___y_3102_);
lean_ctor_set(v___x_3136_, 1, v___x_3135_);
v___x_3137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3137_, 0, v___y_3108_);
lean_ctor_set(v___x_3137_, 1, v___x_3136_);
lean_inc_ref(v___x_3137_);
v___x_3138_ = l_Lean_mkConst(v___x_3131_, v___x_3137_);
lean_inc_ref(v___y_3104_);
lean_inc_ref(v___y_3109_);
lean_inc_ref(v_m_3121_);
v___x_3139_ = l_Lean_mkApp3(v___x_3138_, v_m_3121_, v___y_3109_, v___y_3104_);
v___x_3140_ = l_Lean_Elab_Term_mkInstMVar(v___x_3139_, v___x_3118_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v_a_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
lean_inc(v_a_3141_);
lean_dec_ref(v___x_3140_);
v___x_3142_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__3));
v___x_3143_ = l_Lean_mkConst(v___x_3142_, v___x_3137_);
lean_inc(v_snd_3127_);
lean_inc_ref(v_m_3121_);
v___x_3144_ = l_Lean_mkApp7(v___x_3143_, v_m_3121_, v___y_3109_, v___y_3104_, v_a_3141_, v_snd_3127_, v___y_3103_, v_fst_3126_);
lean_inc(v_u_3122_);
v___y_3025_ = v___y_3084_;
v___y_3026_ = v___y_3085_;
v___y_3027_ = v___y_3086_;
v___y_3028_ = v___y_3087_;
v___y_3029_ = v___y_3088_;
v___y_3030_ = v___y_3089_;
v___y_3031_ = v_u_3122_;
v___y_3032_ = v___y_3090_;
v___y_3033_ = v___y_3091_;
v___y_3034_ = v___y_3092_;
v___y_3035_ = v___y_3093_;
v___y_3036_ = v___x_3118_;
v___y_3037_ = v___y_3094_;
v___y_3038_ = v_v_3123_;
v___y_3039_ = v___y_3095_;
v___y_3040_ = v___y_3096_;
v___y_3041_ = v___y_3097_;
v___y_3042_ = v_snd_3127_;
v___y_3043_ = v___y_3098_;
v___y_3044_ = v___y_3100_;
v___y_3045_ = v___y_3099_;
v___y_3046_ = v___y_3106_;
v___y_3047_ = v___y_3107_;
v_fst_3048_ = v___x_3144_;
v_snd_3049_ = v___x_3118_;
v___y_3050_ = v___y_3111_;
v___y_3051_ = v___y_3112_;
v___y_3052_ = v___y_3113_;
v___y_3053_ = v___y_3114_;
v___y_3054_ = v___y_3115_;
v___y_3055_ = v___y_3116_;
v___y_3056_ = v___y_3117_;
goto v___jp_3024_;
}
else
{
lean_dec_ref(v___x_3137_);
lean_dec(v_snd_3127_);
lean_dec(v_fst_3126_);
lean_dec_ref(v___y_3109_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec_ref(v___y_3100_);
lean_dec_ref(v___y_3098_);
lean_dec(v___y_3097_);
lean_dec_ref(v___y_3096_);
lean_dec(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec_ref(v___y_3090_);
lean_dec_ref(v___y_3089_);
lean_dec_ref(v___y_3088_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
lean_dec(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v_dec_2971_);
return v___x_3140_;
}
}
}
}
else
{
lean_object* v_fst_3147_; lean_object* v_snd_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3183_; 
v_fst_3147_ = lean_ctor_get(v_a_3125_, 0);
v_snd_3148_ = lean_ctor_get(v_a_3125_, 1);
v_isSharedCheck_3183_ = !lean_is_exclusive(v_a_3125_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3150_ = v_a_3125_;
v_isShared_3151_ = v_isSharedCheck_3183_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_snd_3148_);
lean_inc(v_fst_3147_);
lean_dec(v_a_3125_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3183_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3155_; 
v___x_3152_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__4));
v___x_3153_ = lean_box(0);
lean_inc(v___y_3108_);
if (v_isShared_3151_ == 0)
{
lean_ctor_set_tag(v___x_3150_, 1);
lean_ctor_set(v___x_3150_, 1, v___x_3153_);
lean_ctor_set(v___x_3150_, 0, v___y_3108_);
v___x_3155_ = v___x_3150_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___y_3108_);
lean_ctor_set(v_reuseFailAlloc_3182_, 1, v___x_3153_);
v___x_3155_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
lean_inc(v___y_3102_);
v___x_3156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3156_, 0, v___y_3102_);
lean_ctor_set(v___x_3156_, 1, v___x_3155_);
v___x_3157_ = l_Lean_mkConst(v___x_3152_, v___x_3156_);
lean_inc_ref(v___y_3109_);
lean_inc_ref(v___y_3104_);
v___x_3158_ = l_Lean_mkAppB(v___x_3157_, v___y_3104_, v___y_3109_);
v___x_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3158_);
v___x_3160_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__6));
v___x_3161_ = l_Lean_Meta_mkFreshExprMVar(v___x_3159_, v___y_3105_, v___x_3160_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_object* v_a_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v_a_3162_ = lean_ctor_get(v___x_3161_, 0);
lean_inc_n(v_a_3162_, 2);
lean_dec_ref(v___x_3161_);
v___x_3163_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__8));
lean_inc(v_v_3123_);
v___x_3164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3164_, 0, v_v_3123_);
lean_ctor_set(v___x_3164_, 1, v___x_3153_);
lean_inc(v_u_3122_);
v___x_3165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3165_, 0, v_u_3122_);
lean_ctor_set(v___x_3165_, 1, v___x_3164_);
v___x_3166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___y_3102_);
lean_ctor_set(v___x_3166_, 1, v___x_3165_);
v___x_3167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3167_, 0, v___y_3108_);
lean_ctor_set(v___x_3167_, 1, v___x_3166_);
lean_inc_ref(v___x_3167_);
v___x_3168_ = l_Lean_mkConst(v___x_3163_, v___x_3167_);
lean_inc_ref(v___y_3104_);
lean_inc_ref(v___y_3109_);
lean_inc_ref(v_m_3121_);
v___x_3169_ = l_Lean_mkApp4(v___x_3168_, v_m_3121_, v___y_3109_, v___y_3104_, v_a_3162_);
v___x_3170_ = l_Lean_Elab_Term_mkInstMVar(v___x_3169_, v___x_3118_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
if (lean_obj_tag(v___x_3170_) == 0)
{
lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3181_; 
v_a_3171_ = lean_ctor_get(v___x_3170_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3170_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3173_ = v___x_3170_;
v_isShared_3174_ = v_isSharedCheck_3181_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_dec(v___x_3170_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3181_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3179_; 
v___x_3175_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__10));
v___x_3176_ = l_Lean_mkConst(v___x_3175_, v___x_3167_);
lean_inc(v_snd_3148_);
lean_inc(v_a_3162_);
lean_inc_ref(v_m_3121_);
v___x_3177_ = l_Lean_mkApp8(v___x_3176_, v_m_3121_, v___y_3109_, v___y_3104_, v_a_3162_, v_a_3171_, v_snd_3148_, v___y_3103_, v_fst_3147_);
if (v_isShared_3174_ == 0)
{
lean_ctor_set_tag(v___x_3173_, 1);
lean_ctor_set(v___x_3173_, 0, v_a_3162_);
v___x_3179_ = v___x_3173_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_a_3162_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
lean_inc(v_u_3122_);
v___y_3025_ = v___y_3084_;
v___y_3026_ = v___y_3085_;
v___y_3027_ = v___y_3086_;
v___y_3028_ = v___y_3087_;
v___y_3029_ = v___y_3088_;
v___y_3030_ = v___y_3089_;
v___y_3031_ = v_u_3122_;
v___y_3032_ = v___y_3090_;
v___y_3033_ = v___y_3091_;
v___y_3034_ = v___y_3092_;
v___y_3035_ = v___y_3093_;
v___y_3036_ = v___x_3118_;
v___y_3037_ = v___y_3094_;
v___y_3038_ = v_v_3123_;
v___y_3039_ = v___y_3095_;
v___y_3040_ = v___y_3096_;
v___y_3041_ = v___y_3097_;
v___y_3042_ = v_snd_3148_;
v___y_3043_ = v___y_3098_;
v___y_3044_ = v___y_3100_;
v___y_3045_ = v___y_3099_;
v___y_3046_ = v___y_3106_;
v___y_3047_ = v___y_3107_;
v_fst_3048_ = v___x_3177_;
v_snd_3049_ = v___x_3179_;
v___y_3050_ = v___y_3111_;
v___y_3051_ = v___y_3112_;
v___y_3052_ = v___y_3113_;
v___y_3053_ = v___y_3114_;
v___y_3054_ = v___y_3115_;
v___y_3055_ = v___y_3116_;
v___y_3056_ = v___y_3117_;
goto v___jp_3024_;
}
}
}
else
{
lean_dec_ref(v___x_3167_);
lean_dec(v_a_3162_);
lean_dec(v_snd_3148_);
lean_dec_ref(v___y_3099_);
lean_dec(v_fst_3147_);
lean_dec_ref(v___y_3109_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec_ref(v___y_3100_);
lean_dec_ref(v___y_3098_);
lean_dec(v___y_3097_);
lean_dec_ref(v___y_3096_);
lean_dec(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec_ref(v___y_3090_);
lean_dec_ref(v___y_3089_);
lean_dec_ref(v___y_3088_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
lean_dec(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v_dec_2971_);
return v___x_3170_;
}
}
else
{
lean_dec(v_snd_3148_);
lean_dec_ref(v___y_3099_);
lean_dec(v_fst_3147_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3100_);
lean_dec_ref(v___y_3098_);
lean_dec(v___y_3097_);
lean_dec_ref(v___y_3096_);
lean_dec(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec_ref(v___y_3090_);
lean_dec_ref(v___y_3089_);
lean_dec_ref(v___y_3088_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
lean_dec(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v_dec_2971_);
return v___x_3161_;
}
}
}
}
}
else
{
lean_object* v_a_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3191_; 
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3100_);
lean_dec(v___y_3099_);
lean_dec_ref(v___y_3098_);
lean_dec(v___y_3097_);
lean_dec_ref(v___y_3096_);
lean_dec(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec_ref(v___y_3090_);
lean_dec_ref(v___y_3089_);
lean_dec_ref(v___y_3088_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
lean_dec(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v_dec_2971_);
v_a_3184_ = lean_ctor_get(v___x_3124_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3124_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3186_ = v___x_3124_;
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_a_3184_);
lean_dec(v___x_3124_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3189_; 
if (v_isShared_3187_ == 0)
{
v___x_3189_ = v___x_3186_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_a_3184_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
}
}
else
{
lean_object* v_a_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3199_; 
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3100_);
lean_dec(v___y_3099_);
lean_dec_ref(v___y_3098_);
lean_dec(v___y_3097_);
lean_dec_ref(v___y_3096_);
lean_dec(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec_ref(v___y_3090_);
lean_dec_ref(v___y_3089_);
lean_dec_ref(v___y_3088_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
lean_dec(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v_dec_2971_);
v_a_3192_ = lean_ctor_get(v___x_3119_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3194_ = v___x_3119_;
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_a_3192_);
lean_dec(v___x_3119_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3197_; 
if (v_isShared_3195_ == 0)
{
v___x_3197_ = v___x_3194_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3192_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
}
v___jp_3200_:
{
lean_object* v___x_3232_; 
v___x_3232_ = l_Lean_Elab_Do_mkPUnit___redArg(v___y_3217_);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v_a_3233_; lean_object* v_resultName_3234_; lean_object* v_resultType_3235_; lean_object* v___x_3236_; 
v_a_3233_ = lean_ctor_get(v___x_3232_, 0);
lean_inc(v_a_3233_);
lean_dec_ref(v___x_3232_);
v_resultName_3234_ = lean_ctor_get(v_dec_2971_, 0);
v_resultType_3235_ = lean_ctor_get(v_dec_2971_, 1);
lean_inc_ref(v_resultType_3235_);
v___x_3236_ = l_Lean_Meta_isExprDefEq(v_resultType_3235_, v_a_3233_, v___y_3216_, v___y_3218_, v___y_3221_, v___y_3225_);
if (lean_obj_tag(v___x_3236_) == 0)
{
lean_object* v_a_3237_; uint8_t v___x_3238_; 
v_a_3237_ = lean_ctor_get(v___x_3236_, 0);
lean_inc(v_a_3237_);
lean_dec_ref(v___x_3236_);
v___x_3238_ = lean_unbox(v_a_3237_);
lean_dec(v_a_3237_);
if (v___x_3238_ == 0)
{
lean_object* v___x_3239_; 
v___x_3239_ = l_Lean_Elab_Do_mkPUnit___redArg(v___y_3217_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v_a_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
lean_inc(v_a_3240_);
lean_dec_ref(v___x_3239_);
v___x_3241_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___closed__12, &l_Lean_Elab_Do_elabDoFor___closed__12_once, _init_l_Lean_Elab_Do_elabDoFor___closed__12);
v___x_3242_ = l_Lean_MessageData_ofExpr(v_a_3240_);
v___x_3243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3243_, 0, v___x_3241_);
lean_ctor_set(v___x_3243_, 1, v___x_3242_);
v___x_3244_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___closed__14, &l_Lean_Elab_Do_elabDoFor___closed__14_once, _init_l_Lean_Elab_Do_elabDoFor___closed__14);
v___x_3245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3243_);
lean_ctor_set(v___x_3245_, 1, v___x_3244_);
lean_inc_ref(v_resultType_3235_);
v___x_3246_ = l_Lean_MessageData_ofExpr(v_resultType_3235_);
v___x_3247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3245_);
lean_ctor_set(v___x_3247_, 1, v___x_3246_);
v___x_3248_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___closed__16, &l_Lean_Elab_Do_elabDoFor___closed__16_once, _init_l_Lean_Elab_Do_elabDoFor___closed__16);
v___x_3249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3247_);
lean_ctor_set(v___x_3249_, 1, v___x_3248_);
v___x_3250_ = l_Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6(v___x_3249_, v___y_3217_, v___y_3228_, v___y_3227_, v___y_3216_, v___y_3218_, v___y_3221_, v___y_3225_);
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_dec_ref(v___x_3250_);
lean_inc_ref(v_resultType_3235_);
lean_inc_ref(v___y_3202_);
lean_inc(v_resultName_3234_);
v___y_3084_ = v___y_3201_;
v___y_3085_ = v_resultName_3234_;
v___y_3086_ = v___y_3202_;
v___y_3087_ = v___y_3204_;
v___y_3088_ = v___y_3206_;
v___y_3089_ = v___y_3205_;
v___y_3090_ = v___y_3207_;
v___y_3091_ = v___y_3208_;
v___y_3092_ = v_resultType_3235_;
v___y_3093_ = v___y_3211_;
v___y_3094_ = v___y_3203_;
v___y_3095_ = v___y_3231_;
v___y_3096_ = v___y_3209_;
v___y_3097_ = v___y_3210_;
v___y_3098_ = v___y_3212_;
v___y_3099_ = v___y_3222_;
v___y_3100_ = v___y_3223_;
v___y_3101_ = v___y_3202_;
v___y_3102_ = v___y_3213_;
v___y_3103_ = v___y_3214_;
v___y_3104_ = v___y_3215_;
v___y_3105_ = v___y_3224_;
v___y_3106_ = v___y_3226_;
v___y_3107_ = v___y_3229_;
v___y_3108_ = v___y_3230_;
v___y_3109_ = v___y_3220_;
v___y_3110_ = v___y_3219_;
v___y_3111_ = v___y_3217_;
v___y_3112_ = v___y_3228_;
v___y_3113_ = v___y_3227_;
v___y_3114_ = v___y_3216_;
v___y_3115_ = v___y_3218_;
v___y_3116_ = v___y_3221_;
v___y_3117_ = v___y_3225_;
goto v___jp_3083_;
}
else
{
lean_object* v_a_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3258_; 
lean_dec(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3220_);
lean_dec_ref(v___y_3215_);
lean_dec_ref(v___y_3214_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
lean_dec_ref(v___y_3211_);
lean_dec(v___y_3210_);
lean_dec_ref(v___y_3209_);
lean_dec_ref(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v___y_3204_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3201_);
lean_dec_ref(v_dec_2971_);
v_a_3251_ = lean_ctor_get(v___x_3250_, 0);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3253_ = v___x_3250_;
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_a_3251_);
lean_dec(v___x_3250_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3256_; 
if (v_isShared_3254_ == 0)
{
v___x_3256_ = v___x_3253_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_a_3251_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
}
}
else
{
lean_dec(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3220_);
lean_dec_ref(v___y_3215_);
lean_dec_ref(v___y_3214_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
lean_dec_ref(v___y_3211_);
lean_dec(v___y_3210_);
lean_dec_ref(v___y_3209_);
lean_dec_ref(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v___y_3204_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3201_);
lean_dec_ref(v_dec_2971_);
return v___x_3239_;
}
}
else
{
lean_inc_ref(v_resultType_3235_);
lean_inc_ref(v___y_3202_);
lean_inc(v_resultName_3234_);
v___y_3084_ = v___y_3201_;
v___y_3085_ = v_resultName_3234_;
v___y_3086_ = v___y_3202_;
v___y_3087_ = v___y_3204_;
v___y_3088_ = v___y_3206_;
v___y_3089_ = v___y_3205_;
v___y_3090_ = v___y_3207_;
v___y_3091_ = v___y_3208_;
v___y_3092_ = v_resultType_3235_;
v___y_3093_ = v___y_3211_;
v___y_3094_ = v___y_3203_;
v___y_3095_ = v___y_3231_;
v___y_3096_ = v___y_3209_;
v___y_3097_ = v___y_3210_;
v___y_3098_ = v___y_3212_;
v___y_3099_ = v___y_3222_;
v___y_3100_ = v___y_3223_;
v___y_3101_ = v___y_3202_;
v___y_3102_ = v___y_3213_;
v___y_3103_ = v___y_3214_;
v___y_3104_ = v___y_3215_;
v___y_3105_ = v___y_3224_;
v___y_3106_ = v___y_3226_;
v___y_3107_ = v___y_3229_;
v___y_3108_ = v___y_3230_;
v___y_3109_ = v___y_3220_;
v___y_3110_ = v___y_3219_;
v___y_3111_ = v___y_3217_;
v___y_3112_ = v___y_3228_;
v___y_3113_ = v___y_3227_;
v___y_3114_ = v___y_3216_;
v___y_3115_ = v___y_3218_;
v___y_3116_ = v___y_3221_;
v___y_3117_ = v___y_3225_;
goto v___jp_3083_;
}
}
else
{
lean_object* v_a_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3266_; 
lean_dec(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3220_);
lean_dec_ref(v___y_3215_);
lean_dec_ref(v___y_3214_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
lean_dec_ref(v___y_3211_);
lean_dec(v___y_3210_);
lean_dec_ref(v___y_3209_);
lean_dec_ref(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v___y_3204_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3201_);
lean_dec_ref(v_dec_2971_);
v_a_3259_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3261_ = v___x_3236_;
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_a_3259_);
lean_dec(v___x_3236_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3264_; 
if (v_isShared_3262_ == 0)
{
v___x_3264_ = v___x_3261_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_a_3259_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
}
else
{
lean_dec(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3220_);
lean_dec_ref(v___y_3215_);
lean_dec_ref(v___y_3214_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
lean_dec_ref(v___y_3211_);
lean_dec(v___y_3210_);
lean_dec_ref(v___y_3209_);
lean_dec_ref(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v___y_3204_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3201_);
lean_dec_ref(v_dec_2971_);
return v___x_3232_;
}
}
v___jp_3267_:
{
uint8_t v_returnsEarly_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___f_3302_; 
v_returnsEarly_3299_ = lean_ctor_get_uint8(v___y_3291_, sizeof(void*)*2 + 2);
lean_dec_ref(v___y_3291_);
v___x_3300_ = lean_box(v_returnsEarly_3299_);
v___x_3301_ = lean_box(v___y_3275_);
lean_inc_ref(v___y_3272_);
lean_inc_ref(v___y_3273_);
lean_inc_ref(v___y_3298_);
v___f_3302_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__2___boxed), 14, 6);
lean_closure_set(v___f_3302_, 0, v___y_3298_);
lean_closure_set(v___f_3302_, 1, v___y_3273_);
lean_closure_set(v___f_3302_, 2, v___x_3300_);
lean_closure_set(v___f_3302_, 3, v___x_2987_);
lean_closure_set(v___f_3302_, 4, v___y_3272_);
lean_closure_set(v___f_3302_, 5, v___x_3301_);
if (v_returnsEarly_3299_ == 0)
{
size_t v_sz_3303_; size_t v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; 
lean_dec(v___y_3281_);
v_sz_3303_ = lean_array_size(v___y_3298_);
v___x_3304_ = ((size_t)0ULL);
lean_inc_ref(v___y_3298_);
v___x_3305_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__7(v_sz_3303_, v___x_3304_, v___y_3298_);
v___x_3306_ = lean_array_to_list(v___x_3305_);
v___y_3201_ = v___y_3268_;
v___y_3202_ = v___f_3302_;
v___y_3203_ = v___y_3277_;
v___y_3204_ = v___y_3269_;
v___y_3205_ = v___y_3270_;
v___y_3206_ = v___y_3271_;
v___y_3207_ = v___y_3272_;
v___y_3208_ = v_returnsEarly_3299_;
v___y_3209_ = v___y_3298_;
v___y_3210_ = v___y_3279_;
v___y_3211_ = v___y_3274_;
v___y_3212_ = v___y_3280_;
v___y_3213_ = v___y_3282_;
v___y_3214_ = v___y_3283_;
v___y_3215_ = v___y_3284_;
v___y_3216_ = v___y_3285_;
v___y_3217_ = v___y_3286_;
v___y_3218_ = v___y_3287_;
v___y_3219_ = v___y_3273_;
v___y_3220_ = v___y_3288_;
v___y_3221_ = v___y_3289_;
v___y_3222_ = v___y_3290_;
v___y_3223_ = v___y_3276_;
v___y_3224_ = v___y_3292_;
v___y_3225_ = v___y_3294_;
v___y_3226_ = v___y_3293_;
v___y_3227_ = v___y_3296_;
v___y_3228_ = v___y_3295_;
v___y_3229_ = v___y_3278_;
v___y_3230_ = v___y_3297_;
v___y_3231_ = v___x_3306_;
goto v___jp_3200_;
}
else
{
size_t v_sz_3307_; size_t v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v_sz_3307_ = lean_array_size(v___y_3298_);
v___x_3308_ = ((size_t)0ULL);
lean_inc_ref(v___y_3298_);
v___x_3309_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__7(v_sz_3307_, v___x_3308_, v___y_3298_);
v___x_3310_ = lean_array_to_list(v___x_3309_);
v___x_3311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___y_3281_);
lean_ctor_set(v___x_3311_, 1, v___x_3310_);
v___y_3201_ = v___y_3268_;
v___y_3202_ = v___f_3302_;
v___y_3203_ = v___y_3277_;
v___y_3204_ = v___y_3269_;
v___y_3205_ = v___y_3270_;
v___y_3206_ = v___y_3271_;
v___y_3207_ = v___y_3272_;
v___y_3208_ = v_returnsEarly_3299_;
v___y_3209_ = v___y_3298_;
v___y_3210_ = v___y_3279_;
v___y_3211_ = v___y_3274_;
v___y_3212_ = v___y_3280_;
v___y_3213_ = v___y_3282_;
v___y_3214_ = v___y_3283_;
v___y_3215_ = v___y_3284_;
v___y_3216_ = v___y_3285_;
v___y_3217_ = v___y_3286_;
v___y_3218_ = v___y_3287_;
v___y_3219_ = v___y_3273_;
v___y_3220_ = v___y_3288_;
v___y_3221_ = v___y_3289_;
v___y_3222_ = v___y_3290_;
v___y_3223_ = v___y_3276_;
v___y_3224_ = v___y_3292_;
v___y_3225_ = v___y_3294_;
v___y_3226_ = v___y_3293_;
v___y_3227_ = v___y_3296_;
v___y_3228_ = v___y_3295_;
v___y_3229_ = v___y_3278_;
v___y_3230_ = v___y_3297_;
v___y_3231_ = v___x_3311_;
goto v___jp_3200_;
}
}
v___jp_3312_:
{
lean_object* v_x_3321_; lean_object* v___x_3322_; uint8_t v___x_3323_; 
v_x_3321_ = l_Lean_Syntax_getArg(v___x_2988_, v___x_2983_);
v___x_3322_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__16));
lean_inc(v_x_3321_);
v___x_3323_ = l_Lean_Syntax_isOfKind(v_x_3321_, v___x_3322_);
if (v___x_3323_ == 0)
{
lean_object* v___x_3324_; 
lean_dec(v_x_3321_);
lean_dec(v_h_x3f_3313_);
lean_dec(v___x_2988_);
lean_dec_ref(v_dec_2971_);
lean_dec(v_stx_2970_);
v___x_3324_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_3324_;
}
else
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; 
v___x_3325_ = lean_mk_empty_array_with_capacity(v___x_2983_);
lean_inc(v_x_3321_);
v___x_3326_ = lean_array_push(v___x_3325_, v_x_3321_);
v___x_3327_ = l_Lean_Elab_Do_checkMutVarsForShadowing(v___x_3326_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
lean_dec_ref(v___x_3326_);
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_object* v___x_3328_; 
lean_dec_ref(v___x_3327_);
v___x_3328_ = l_Lean_Meta_mkFreshLevelMVar(v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v_a_3329_; lean_object* v___x_3330_; 
v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
lean_inc(v_a_3329_);
lean_dec_ref(v___x_3328_);
v___x_3330_ = l_Lean_Meta_mkFreshLevelMVar(v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
if (lean_obj_tag(v___x_3330_) == 0)
{
lean_object* v_a_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; uint8_t v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; 
v_a_3331_ = lean_ctor_get(v___x_3330_, 0);
lean_inc(v_a_3331_);
lean_dec_ref(v___x_3330_);
lean_inc(v_a_3329_);
v___x_3332_ = l_Lean_Level_succ___override(v_a_3329_);
v___x_3333_ = l_Lean_mkSort(v___x_3332_);
v___x_3334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3333_);
v___x_3335_ = 0;
v___x_3336_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__18));
v___x_3337_ = l_Lean_Meta_mkFreshExprMVar(v___x_3334_, v___x_3335_, v___x_3336_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3410_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3340_ = v___x_3337_;
v_isShared_3341_ = v_isSharedCheck_3410_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3337_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3410_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3345_; 
lean_inc(v_a_3331_);
v___x_3342_ = l_Lean_Level_succ___override(v_a_3331_);
v___x_3343_ = l_Lean_mkSort(v___x_3342_);
if (v_isShared_3341_ == 0)
{
lean_ctor_set_tag(v___x_3340_, 1);
lean_ctor_set(v___x_3340_, 0, v___x_3343_);
v___x_3345_ = v___x_3340_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v___x_3343_);
v___x_3345_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3346_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__20));
v___x_3347_ = l_Lean_Meta_mkFreshExprMVar(v___x_3345_, v___x_3335_, v___x_3346_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v_a_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3408_; 
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3350_ = v___x_3347_;
v_isShared_3351_ = v_isSharedCheck_3408_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_a_3348_);
lean_dec(v___x_3347_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3408_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3355_; 
v___x_3352_ = lean_unsigned_to_nat(3u);
v___x_3353_ = l_Lean_Syntax_getArg(v___x_2988_, v___x_3352_);
lean_dec(v___x_2988_);
lean_inc(v_a_3348_);
if (v_isShared_3351_ == 0)
{
lean_ctor_set_tag(v___x_3350_, 1);
v___x_3355_ = v___x_3350_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_a_3348_);
v___x_3355_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3356_ = lean_box(0);
v___x_3357_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_3353_, v___x_3355_, v___x_2990_, v___x_2990_, v___x_3356_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v_a_3358_; lean_object* v_body_3359_; lean_object* v___x_3360_; 
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
lean_inc(v_a_3358_);
lean_dec_ref(v___x_3357_);
v_body_3359_ = l_Lean_Syntax_getArg(v_stx_2970_, v___x_3352_);
lean_dec(v_stx_2970_);
lean_inc(v_body_3359_);
v___x_3360_ = l_Lean_Elab_Do_inferControlInfoSeq(v_body_3359_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_object* v_a_3361_; lean_object* v___x_3362_; 
v_a_3361_ = lean_ctor_get(v___x_3360_, 0);
lean_inc(v_a_3361_);
lean_dec_ref(v___x_3360_);
v___x_3362_ = l_Lean_Elab_Do_getReturnCont___redArg(v___y_3314_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3363_);
lean_dec_ref(v___x_3362_);
v___x_3364_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__22));
v___x_3365_ = l_Lean_Core_mkFreshUserName(v___x_3364_, v___y_3319_, v___y_3320_);
if (lean_obj_tag(v___x_3365_) == 0)
{
lean_object* v_a_3366_; lean_object* v_monadInfo_3367_; lean_object* v_mutVars_3368_; lean_object* v___f_3369_; lean_object* v___f_3370_; lean_object* v___x_3371_; lean_object* v___f_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; uint8_t v___x_3375_; 
v_a_3366_ = lean_ctor_get(v___x_3365_, 0);
lean_inc(v_a_3366_);
lean_dec_ref(v___x_3365_);
v_monadInfo_3367_ = lean_ctor_get(v___y_3314_, 0);
v_mutVars_3368_ = lean_ctor_get(v___y_3314_, 1);
lean_inc(v_a_3338_);
v___f_3369_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__0___boxed), 10, 1);
lean_closure_set(v___f_3369_, 0, v_a_3338_);
lean_inc_ref(v___f_3369_);
lean_inc(v_x_3321_);
v___f_3370_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__1___boxed), 5, 3);
lean_closure_set(v___f_3370_, 0, v_x_3321_);
lean_closure_set(v___f_3370_, 1, v___f_3369_);
lean_closure_set(v___f_3370_, 2, v___x_2983_);
v___x_3371_ = lean_box(v___x_2990_);
lean_inc(v_a_3363_);
v___f_3372_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__3___boxed), 12, 3);
lean_closure_set(v___f_3372_, 0, v_a_3363_);
lean_closure_set(v___f_3372_, 1, v___x_2983_);
lean_closure_set(v___f_3372_, 2, v___x_3371_);
v___x_3373_ = lean_array_get_size(v_mutVars_3368_);
v___x_3374_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_3375_ = lean_nat_dec_lt(v___x_2987_, v___x_3373_);
if (v___x_3375_ == 0)
{
lean_inc(v_a_3331_);
lean_inc(v_a_3348_);
lean_inc(v_a_3358_);
lean_inc(v_a_3338_);
lean_inc(v_a_3329_);
lean_inc(v_a_3366_);
v___y_3268_ = v_a_3366_;
v___y_3269_ = v_a_3329_;
v___y_3270_ = v_a_3338_;
v___y_3271_ = v_a_3358_;
v___y_3272_ = v_a_3363_;
v___y_3273_ = v_monadInfo_3367_;
v___y_3274_ = v_a_3348_;
v___y_3275_ = v___x_3323_;
v___y_3276_ = v___f_3370_;
v___y_3277_ = v_body_3359_;
v___y_3278_ = v___f_3369_;
v___y_3279_ = v_a_3331_;
v___y_3280_ = v___f_3372_;
v___y_3281_ = v_a_3366_;
v___y_3282_ = v_a_3329_;
v___y_3283_ = v_a_3358_;
v___y_3284_ = v_a_3338_;
v___y_3285_ = v___y_3317_;
v___y_3286_ = v___y_3314_;
v___y_3287_ = v___y_3318_;
v___y_3288_ = v_a_3348_;
v___y_3289_ = v___y_3319_;
v___y_3290_ = v_h_x3f_3313_;
v___y_3291_ = v_a_3361_;
v___y_3292_ = v___x_3335_;
v___y_3293_ = v_x_3321_;
v___y_3294_ = v___y_3320_;
v___y_3295_ = v___y_3315_;
v___y_3296_ = v___y_3316_;
v___y_3297_ = v_a_3331_;
v___y_3298_ = v___x_3374_;
goto v___jp_3267_;
}
else
{
uint8_t v___x_3376_; 
v___x_3376_ = lean_nat_dec_le(v___x_3373_, v___x_3373_);
if (v___x_3376_ == 0)
{
if (v___x_3375_ == 0)
{
lean_inc(v_a_3331_);
lean_inc(v_a_3348_);
lean_inc(v_a_3358_);
lean_inc(v_a_3338_);
lean_inc(v_a_3329_);
lean_inc(v_a_3366_);
v___y_3268_ = v_a_3366_;
v___y_3269_ = v_a_3329_;
v___y_3270_ = v_a_3338_;
v___y_3271_ = v_a_3358_;
v___y_3272_ = v_a_3363_;
v___y_3273_ = v_monadInfo_3367_;
v___y_3274_ = v_a_3348_;
v___y_3275_ = v___x_3323_;
v___y_3276_ = v___f_3370_;
v___y_3277_ = v_body_3359_;
v___y_3278_ = v___f_3369_;
v___y_3279_ = v_a_3331_;
v___y_3280_ = v___f_3372_;
v___y_3281_ = v_a_3366_;
v___y_3282_ = v_a_3329_;
v___y_3283_ = v_a_3358_;
v___y_3284_ = v_a_3338_;
v___y_3285_ = v___y_3317_;
v___y_3286_ = v___y_3314_;
v___y_3287_ = v___y_3318_;
v___y_3288_ = v_a_3348_;
v___y_3289_ = v___y_3319_;
v___y_3290_ = v_h_x3f_3313_;
v___y_3291_ = v_a_3361_;
v___y_3292_ = v___x_3335_;
v___y_3293_ = v_x_3321_;
v___y_3294_ = v___y_3320_;
v___y_3295_ = v___y_3315_;
v___y_3296_ = v___y_3316_;
v___y_3297_ = v_a_3331_;
v___y_3298_ = v___x_3374_;
goto v___jp_3267_;
}
else
{
size_t v___x_3377_; size_t v___x_3378_; lean_object* v___x_3379_; 
v___x_3377_ = ((size_t)0ULL);
v___x_3378_ = lean_usize_of_nat(v___x_3373_);
v___x_3379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__8(v_a_3361_, v_mutVars_3368_, v___x_3377_, v___x_3378_, v___x_3374_);
lean_inc(v_a_3331_);
lean_inc(v_a_3348_);
lean_inc(v_a_3358_);
lean_inc(v_a_3338_);
lean_inc(v_a_3329_);
lean_inc(v_a_3366_);
v___y_3268_ = v_a_3366_;
v___y_3269_ = v_a_3329_;
v___y_3270_ = v_a_3338_;
v___y_3271_ = v_a_3358_;
v___y_3272_ = v_a_3363_;
v___y_3273_ = v_monadInfo_3367_;
v___y_3274_ = v_a_3348_;
v___y_3275_ = v___x_3323_;
v___y_3276_ = v___f_3370_;
v___y_3277_ = v_body_3359_;
v___y_3278_ = v___f_3369_;
v___y_3279_ = v_a_3331_;
v___y_3280_ = v___f_3372_;
v___y_3281_ = v_a_3366_;
v___y_3282_ = v_a_3329_;
v___y_3283_ = v_a_3358_;
v___y_3284_ = v_a_3338_;
v___y_3285_ = v___y_3317_;
v___y_3286_ = v___y_3314_;
v___y_3287_ = v___y_3318_;
v___y_3288_ = v_a_3348_;
v___y_3289_ = v___y_3319_;
v___y_3290_ = v_h_x3f_3313_;
v___y_3291_ = v_a_3361_;
v___y_3292_ = v___x_3335_;
v___y_3293_ = v_x_3321_;
v___y_3294_ = v___y_3320_;
v___y_3295_ = v___y_3315_;
v___y_3296_ = v___y_3316_;
v___y_3297_ = v_a_3331_;
v___y_3298_ = v___x_3379_;
goto v___jp_3267_;
}
}
else
{
size_t v___x_3380_; size_t v___x_3381_; lean_object* v___x_3382_; 
v___x_3380_ = ((size_t)0ULL);
v___x_3381_ = lean_usize_of_nat(v___x_3373_);
v___x_3382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__8(v_a_3361_, v_mutVars_3368_, v___x_3380_, v___x_3381_, v___x_3374_);
lean_inc(v_a_3331_);
lean_inc(v_a_3348_);
lean_inc(v_a_3358_);
lean_inc(v_a_3338_);
lean_inc(v_a_3329_);
lean_inc(v_a_3366_);
v___y_3268_ = v_a_3366_;
v___y_3269_ = v_a_3329_;
v___y_3270_ = v_a_3338_;
v___y_3271_ = v_a_3358_;
v___y_3272_ = v_a_3363_;
v___y_3273_ = v_monadInfo_3367_;
v___y_3274_ = v_a_3348_;
v___y_3275_ = v___x_3323_;
v___y_3276_ = v___f_3370_;
v___y_3277_ = v_body_3359_;
v___y_3278_ = v___f_3369_;
v___y_3279_ = v_a_3331_;
v___y_3280_ = v___f_3372_;
v___y_3281_ = v_a_3366_;
v___y_3282_ = v_a_3329_;
v___y_3283_ = v_a_3358_;
v___y_3284_ = v_a_3338_;
v___y_3285_ = v___y_3317_;
v___y_3286_ = v___y_3314_;
v___y_3287_ = v___y_3318_;
v___y_3288_ = v_a_3348_;
v___y_3289_ = v___y_3319_;
v___y_3290_ = v_h_x3f_3313_;
v___y_3291_ = v_a_3361_;
v___y_3292_ = v___x_3335_;
v___y_3293_ = v_x_3321_;
v___y_3294_ = v___y_3320_;
v___y_3295_ = v___y_3315_;
v___y_3296_ = v___y_3316_;
v___y_3297_ = v_a_3331_;
v___y_3298_ = v___x_3382_;
goto v___jp_3267_;
}
}
}
else
{
lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3390_; 
lean_dec(v_a_3363_);
lean_dec(v_a_3361_);
lean_dec(v_body_3359_);
lean_dec(v_a_3358_);
lean_dec(v_a_3348_);
lean_dec(v_a_3338_);
lean_dec(v_a_3331_);
lean_dec(v_a_3329_);
lean_dec(v_x_3321_);
lean_dec(v_h_x3f_3313_);
lean_dec_ref(v_dec_2971_);
v_a_3383_ = lean_ctor_get(v___x_3365_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3365_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3385_ = v___x_3365_;
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_dec(v___x_3365_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3388_; 
if (v_isShared_3386_ == 0)
{
v___x_3388_ = v___x_3385_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3383_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
}
else
{
lean_object* v_a_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3398_; 
lean_dec(v_a_3361_);
lean_dec(v_body_3359_);
lean_dec(v_a_3358_);
lean_dec(v_a_3348_);
lean_dec(v_a_3338_);
lean_dec(v_a_3331_);
lean_dec(v_a_3329_);
lean_dec(v_x_3321_);
lean_dec(v_h_x3f_3313_);
lean_dec_ref(v_dec_2971_);
v_a_3391_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3393_ = v___x_3362_;
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_a_3391_);
lean_dec(v___x_3362_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3396_; 
if (v_isShared_3394_ == 0)
{
v___x_3396_ = v___x_3393_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_a_3391_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
}
else
{
lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3406_; 
lean_dec(v_body_3359_);
lean_dec(v_a_3358_);
lean_dec(v_a_3348_);
lean_dec(v_a_3338_);
lean_dec(v_a_3331_);
lean_dec(v_a_3329_);
lean_dec(v_x_3321_);
lean_dec(v_h_x3f_3313_);
lean_dec_ref(v_dec_2971_);
v_a_3399_ = lean_ctor_get(v___x_3360_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3360_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3401_ = v___x_3360_;
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3399_);
lean_dec(v___x_3360_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3404_; 
if (v_isShared_3402_ == 0)
{
v___x_3404_ = v___x_3401_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_a_3399_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
}
else
{
lean_dec(v_a_3348_);
lean_dec(v_a_3338_);
lean_dec(v_a_3331_);
lean_dec(v_a_3329_);
lean_dec(v_x_3321_);
lean_dec(v_h_x3f_3313_);
lean_dec_ref(v_dec_2971_);
lean_dec(v_stx_2970_);
return v___x_3357_;
}
}
}
}
else
{
lean_dec(v_a_3338_);
lean_dec(v_a_3331_);
lean_dec(v_a_3329_);
lean_dec(v_x_3321_);
lean_dec(v_h_x3f_3313_);
lean_dec(v___x_2988_);
lean_dec_ref(v_dec_2971_);
lean_dec(v_stx_2970_);
return v___x_3347_;
}
}
}
}
else
{
lean_dec(v_a_3331_);
lean_dec(v_a_3329_);
lean_dec(v_x_3321_);
lean_dec(v_h_x3f_3313_);
lean_dec(v___x_2988_);
lean_dec_ref(v_dec_2971_);
lean_dec(v_stx_2970_);
return v___x_3337_;
}
}
else
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
lean_dec(v_a_3329_);
lean_dec(v_x_3321_);
lean_dec(v_h_x3f_3313_);
lean_dec(v___x_2988_);
lean_dec_ref(v_dec_2971_);
lean_dec(v_stx_2970_);
v_a_3411_ = lean_ctor_get(v___x_3330_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3330_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3330_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3330_);
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
lean_dec(v_x_3321_);
lean_dec(v_h_x3f_3313_);
lean_dec(v___x_2988_);
lean_dec_ref(v_dec_2971_);
lean_dec(v_stx_2970_);
v_a_3419_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3421_ = v___x_3328_;
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3328_);
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
lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3434_; 
lean_dec(v_x_3321_);
lean_dec(v_h_x3f_3313_);
lean_dec(v___x_2988_);
lean_dec_ref(v_dec_2971_);
lean_dec(v_stx_2970_);
v_a_3427_ = lean_ctor_get(v___x_3327_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3327_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3429_ = v___x_3327_;
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___x_3327_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3432_; 
if (v_isShared_3430_ == 0)
{
v___x_3432_ = v___x_3429_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_a_3427_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___boxed(lean_object* v_stx_3444_, lean_object* v_dec_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_){
_start:
{
lean_object* v_res_3454_; 
v_res_3454_ = l_Lean_Elab_Do_elabDoFor(v_stx_3444_, v_dec_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_);
lean_dec(v_a_3452_);
lean_dec_ref(v_a_3451_);
lean_dec(v_a_3450_);
lean_dec_ref(v_a_3449_);
lean_dec(v_a_3448_);
lean_dec_ref(v_a_3447_);
lean_dec_ref(v_a_3446_);
return v_res_3454_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2(lean_object* v_00_u03b1_3455_, lean_object* v_msg_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_){
_start:
{
lean_object* v___x_3464_; 
v___x_3464_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v_msg_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_);
return v___x_3464_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___boxed(lean_object* v_00_u03b1_3465_, lean_object* v_msg_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_){
_start:
{
lean_object* v_res_3474_; 
v_res_3474_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2(v_00_u03b1_3465_, v_msg_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
lean_dec(v___y_3468_);
lean_dec_ref(v___y_3467_);
return v_res_3474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5(lean_object* v_00_u03b1_3475_, lean_object* v_name_3476_, lean_object* v_type_3477_, lean_object* v_k_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_){
_start:
{
lean_object* v___x_3487_; 
v___x_3487_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(v_name_3476_, v_type_3477_, v_k_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___boxed(lean_object* v_00_u03b1_3488_, lean_object* v_name_3489_, lean_object* v_type_3490_, lean_object* v_k_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
lean_object* v_res_3500_; 
v_res_3500_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5(v_00_u03b1_3488_, v_name_3489_, v_type_3490_, v_k_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
lean_dec(v___y_3496_);
lean_dec_ref(v___y_3495_);
lean_dec(v___y_3494_);
lean_dec_ref(v___y_3493_);
lean_dec_ref(v___y_3492_);
return v_res_3500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3(lean_object* v_msgData_3501_, lean_object* v_macroStack_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_){
_start:
{
lean_object* v___x_3510_; 
v___x_3510_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(v_msgData_3501_, v_macroStack_3502_, v___y_3507_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___boxed(lean_object* v_msgData_3511_, lean_object* v_macroStack_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3(v_msgData_3511_, v_macroStack_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14(lean_object* v_ref_3521_, lean_object* v_msgData_3522_, uint8_t v_severity_3523_, uint8_t v_isSilent_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_){
_start:
{
lean_object* v___x_3533_; 
v___x_3533_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg(v_ref_3521_, v_msgData_3522_, v_severity_3523_, v_isSilent_3524_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_);
return v___x_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___boxed(lean_object* v_ref_3534_, lean_object* v_msgData_3535_, lean_object* v_severity_3536_, lean_object* v_isSilent_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_){
_start:
{
uint8_t v_severity_boxed_3546_; uint8_t v_isSilent_boxed_3547_; lean_object* v_res_3548_; 
v_severity_boxed_3546_ = lean_unbox(v_severity_3536_);
v_isSilent_boxed_3547_ = lean_unbox(v_isSilent_3537_);
v_res_3548_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14(v_ref_3534_, v_msgData_3535_, v_severity_boxed_3546_, v_isSilent_boxed_3547_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_);
lean_dec(v___y_3544_);
lean_dec_ref(v___y_3543_);
lean_dec(v___y_3542_);
lean_dec_ref(v___y_3541_);
lean_dec(v___y_3540_);
lean_dec_ref(v___y_3539_);
lean_dec_ref(v___y_3538_);
lean_dec(v_ref_3534_);
return v_res_3548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1(){
_start:
{
lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3556_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_3557_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
v___x_3558_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1));
v___x_3559_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___boxed), 10, 0);
v___x_3560_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3556_, v___x_3557_, v___x_3558_, v___x_3559_);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___boxed(lean_object* v_a_3561_){
_start:
{
lean_object* v_res_3562_; 
v_res_3562_ = l_Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1();
return v_res_3562_;
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
