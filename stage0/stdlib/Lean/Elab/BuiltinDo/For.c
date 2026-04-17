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
lean_object* l_String_toRawSubstring_x27(lean_object*);
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
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSome(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_mkSort(lean_object*);
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
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letConfig"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__22 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__22_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__24 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__24_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letIdDecl"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "letId"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__26 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__26_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__27 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__27_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doMatch"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "matchDiscr"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Std.Stream.next\?"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__32 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__32_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Stream"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__34 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__34_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "next\?"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__35 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__35_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(131, 33, 225, 197, 4, 77, 215, 237)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(223, 69, 181, 194, 149, 37, 29, 54)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__37 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__37_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__37_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43_value),LEAN_SCALAR_PTR_LITERAL(73, 239, 30, 105, 8, 60, 178, 241)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__45 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__45_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__46 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__46_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__46_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43_value),LEAN_SCALAR_PTR_LITERAL(149, 114, 34, 228, 75, 195, 143, 131)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__48 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__48_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__48_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doBreak"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__51 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__51_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "break"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__52 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__52_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "some"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53_value),LEAN_SCALAR_PTR_LITERAL(37, 202, 7, 33, 103, 74, 114, 212)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__55 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__55_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__46_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53_value),LEAN_SCALAR_PTR_LITERAL(89, 148, 40, 55, 221, 242, 231, 67)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__57 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__57_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__57_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__58 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__58_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "tuple"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__59 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__59_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__60 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__60_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__61 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__61_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__62 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__62_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__62_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__63 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__63_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__64 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__64_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__68 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__68_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "s'"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69_value),LEAN_SCALAR_PTR_LITERAL(203, 110, 194, 112, 150, 40, 11, 92)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__71 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__71_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__72 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__72_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doReassign"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__73 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__73_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "letIdDeclNoBinders"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__74 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__74_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doNested"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "The proof annotation here has not been implemented yet."};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__77 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__77_value;
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
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75_value),LEAN_SCALAR_PTR_LITERAL(220, 154, 41, 109, 103, 76, 110, 63)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__3 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
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
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__11_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29_value),LEAN_SCALAR_PTR_LITERAL(29, 50, 175, 23, 122, 111, 148, 60)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__11 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31_value),LEAN_SCALAR_PTR_LITERAL(99, 51, 127, 238, 206, 239, 57, 130)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__12 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__13 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__14 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__14_value;
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__15 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__15_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__16 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "expandDoFor"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 157, 21, 52, 135, 185, 36, 254)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "elabDoFor"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(41, 135, 12, 29, 130, 81, 226, 183)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___boxed(lean_object*);
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
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23(void){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Array_mkArray0(lean_box(0));
return v___x_81_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__32));
v___x_92_ = l_String_toRawSubstring_x27(v___x_91_);
return v___x_92_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43));
v___x_111_ = l_String_toRawSubstring_x27(v___x_110_);
return v___x_111_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53));
v___x_129_ = l_String_toRawSubstring_x27(v___x_128_);
return v___x_129_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__64));
v___x_149_ = l_String_toRawSubstring_x27(v___x_148_);
return v___x_149_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69));
v___x_155_ = l_String_toRawSubstring_x27(v___x_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(lean_object* v___x_164_, lean_object* v___x_165_, lean_object* v___x_166_, uint8_t v___x_167_, lean_object* v___x_168_, lean_object* v___x_169_, lean_object* v___x_170_, lean_object* v___f_171_, lean_object* v_fst_172_, lean_object* v___x_173_, lean_object* v_snd_174_, lean_object* v_x_175_, lean_object* v_h_x3f_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___y_182_; 
v___x_179_ = l_Lean_Syntax_getArg(v___x_164_, v___x_165_);
v___x_180_ = l_Lean_Syntax_getArg(v___x_164_, v___x_166_);
if (lean_obj_tag(v_h_x3f_176_) == 1)
{
lean_object* v_val_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v_val_400_ = lean_ctor_get(v_h_x3f_176_, 0);
v___x_401_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__77));
v___x_402_ = l_Lean_Macro_throwErrorAt___redArg(v_val_400_, v___x_401_, v___y_177_, v___y_178_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; 
v_a_403_ = lean_ctor_get(v___x_402_, 1);
lean_inc(v_a_403_);
lean_dec_ref(v___x_402_);
v___y_182_ = v_a_403_;
goto v___jp_181_;
}
else
{
lean_object* v_a_404_; lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_dec(v___x_180_);
lean_dec(v___x_179_);
lean_dec(v_snd_174_);
lean_dec_ref(v___x_173_);
lean_dec(v_fst_172_);
lean_dec_ref(v___f_171_);
lean_dec_ref(v___x_170_);
lean_dec_ref(v___x_169_);
lean_dec_ref(v___x_168_);
v_a_404_ = lean_ctor_get(v___x_402_, 0);
v_a_405_ = lean_ctor_get(v___x_402_, 1);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_402_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_inc(v_a_404_);
lean_dec(v___x_402_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_404_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
else
{
v___y_182_ = v___y_178_;
goto v___jp_181_;
}
v___jp_181_:
{
lean_object* v_quotContext_183_; lean_object* v_currMacroScope_184_; lean_object* v_ref_185_; lean_object* v_ref_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v_macroScope_208_; lean_object* v_traceMsgs_209_; lean_object* v_expandedMacroDecls_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_399_; 
v_quotContext_183_ = lean_ctor_get(v___y_177_, 1);
v_currMacroScope_184_ = lean_ctor_get(v___y_177_, 2);
v_ref_185_ = lean_ctor_get(v___y_177_, 5);
v_ref_186_ = l_Lean_replaceRef(v___x_180_, v_ref_185_);
v___x_187_ = l_Lean_SourceInfo_fromRef(v_ref_186_, v___x_167_);
lean_dec(v_ref_186_);
v___x_188_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__0));
lean_inc_ref_n(v___x_170_, 3);
lean_inc_ref_n(v___x_169_, 3);
lean_inc_ref_n(v___x_168_, 3);
v___x_189_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_188_);
v___x_190_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__1));
v___x_191_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_190_);
v___x_192_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__2));
lean_inc_n(v___x_187_, 6);
v___x_193_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_187_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
v___x_194_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4);
v___x_195_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7));
lean_inc(v_currMacroScope_184_);
lean_inc(v_quotContext_183_);
v___x_196_ = l_Lean_addMacroScope(v_quotContext_183_, v___x_195_, v_currMacroScope_184_);
v___x_197_ = lean_box(0);
v___x_198_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__11));
v___x_199_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_199_, 0, v___x_187_);
lean_ctor_set(v___x_199_, 1, v___x_194_);
lean_ctor_set(v___x_199_, 2, v___x_196_);
lean_ctor_set(v___x_199_, 3, v___x_198_);
lean_inc(v___x_191_);
v___x_200_ = l_Lean_Syntax_node2(v___x_187_, v___x_191_, v___x_193_, v___x_199_);
v___x_201_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_202_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__14));
v___x_203_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_202_);
v___x_204_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15));
v___x_205_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_187_);
lean_ctor_set(v___x_205_, 1, v___x_204_);
lean_inc(v___x_203_);
v___x_206_ = l_Lean_Syntax_node1(v___x_187_, v___x_203_, v___x_205_);
lean_inc(v___x_180_);
lean_inc_n(v___x_206_, 2);
v___x_207_ = l_Lean_Syntax_node4(v___x_187_, v___x_201_, v___x_206_, v___x_206_, v___x_206_, v___x_180_);
v_macroScope_208_ = lean_ctor_get(v___y_182_, 0);
v_traceMsgs_209_ = lean_ctor_get(v___y_182_, 1);
v_expandedMacroDecls_210_ = lean_ctor_get(v___y_182_, 2);
v_isSharedCheck_399_ = !lean_is_exclusive(v___y_182_);
if (v_isSharedCheck_399_ == 0)
{
v___x_212_ = v___y_182_;
v_isShared_213_ = v_isSharedCheck_399_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_expandedMacroDecls_210_);
lean_inc(v_traceMsgs_209_);
lean_inc(v_macroScope_208_);
lean_dec(v___y_182_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_399_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_214_; lean_object* v___x_216_; 
v___x_214_ = lean_nat_add(v_macroScope_208_, v___x_165_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 0, v___x_214_);
v___x_216_ = v___x_212_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_214_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_traceMsgs_209_);
lean_ctor_set(v_reuseFailAlloc_398_, 2, v_expandedMacroDecls_210_);
v___x_216_ = v_reuseFailAlloc_398_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
lean_object* v___x_217_; 
lean_inc_ref(v___f_171_);
lean_inc_ref(v___y_177_);
lean_inc(v_ref_185_);
v___x_217_ = lean_apply_3(v___f_171_, v_ref_185_, v___y_177_, v___x_216_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_218_; lean_object* v_a_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v_a_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc_n(v_a_218_, 9);
v_a_219_ = lean_ctor_get(v___x_217_, 1);
lean_inc(v_a_219_);
lean_dec_ref(v___x_217_);
lean_inc(v___x_189_);
v___x_220_ = l_Lean_Syntax_node2(v___x_187_, v___x_189_, v___x_200_, v___x_207_);
v___x_221_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17));
lean_inc(v_quotContext_183_);
v___x_222_ = l_Lean_addMacroScope(v_quotContext_183_, v___x_221_, v_macroScope_208_);
v___x_223_ = l_Lean_mkIdentFrom(v___x_180_, v___x_222_, v___x_167_);
lean_dec(v___x_180_);
v___x_224_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__18));
lean_inc_ref_n(v___x_170_, 6);
lean_inc_ref_n(v___x_169_, 6);
lean_inc_ref_n(v___x_168_, 6);
v___x_225_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_224_);
v___x_226_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__19));
v___x_227_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_226_);
v___x_228_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__20));
v___x_229_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_229_, 0, v_a_218_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__21));
v___x_231_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_231_, 0, v_a_218_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
v___x_232_ = l_Lean_Syntax_node1(v_a_218_, v___x_201_, v___x_231_);
v___x_233_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__22));
v___x_234_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_233_);
v___x_235_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_236_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_236_, 0, v_a_218_);
lean_ctor_set(v___x_236_, 1, v___x_201_);
lean_ctor_set(v___x_236_, 2, v___x_235_);
lean_inc_ref_n(v___x_236_, 3);
v___x_237_ = l_Lean_Syntax_node1(v_a_218_, v___x_234_, v___x_236_);
v___x_238_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__24));
v___x_239_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_238_);
v___x_240_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25));
v___x_241_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_240_);
v___x_242_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__26));
v___x_243_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_242_);
lean_inc(v___x_223_);
lean_inc(v___x_243_);
v___x_244_ = l_Lean_Syntax_node1(v_a_218_, v___x_243_, v___x_223_);
v___x_245_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__27));
v___x_246_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_246_, 0, v_a_218_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
v___x_247_ = l_Lean_Syntax_node5(v_a_218_, v___x_241_, v___x_244_, v___x_236_, v___x_236_, v___x_246_, v___x_220_);
lean_inc_ref(v___y_177_);
lean_inc(v_ref_185_);
v___x_248_ = lean_apply_3(v___f_171_, v_ref_185_, v___y_177_, v_a_219_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_379_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
v_a_250_ = lean_ctor_get(v___x_248_, 1);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_379_ == 0)
{
v___x_252_ = v___x_248_;
v_isShared_253_ = v_isSharedCheck_379_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_inc(v_a_249_);
lean_dec(v___x_248_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_379_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_377_; 
lean_inc_n(v_a_218_, 2);
v___x_254_ = l_Lean_Syntax_node1(v_a_218_, v___x_239_, v___x_247_);
v___x_255_ = l_Lean_Syntax_node4(v_a_218_, v___x_227_, v___x_229_, v___x_232_, v___x_237_, v___x_254_);
lean_inc_n(v___x_225_, 4);
v___x_256_ = l_Lean_Syntax_node2(v_a_218_, v___x_225_, v___x_255_, v___x_236_);
v___x_257_ = lean_array_push(v_fst_172_, v___x_256_);
v___x_258_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28));
lean_inc_ref_n(v___x_170_, 11);
lean_inc_ref_n(v___x_169_, 11);
lean_inc_ref_n(v___x_168_, 13);
v___x_259_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_258_);
v___x_260_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29));
v___x_261_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_260_);
v___x_262_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_n(v_a_249_, 54);
v___x_263_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_263_, 0, v_a_249_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
v___x_264_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_264_, 0, v_a_249_);
lean_ctor_set(v___x_264_, 1, v___x_201_);
lean_ctor_set(v___x_264_, 2, v___x_235_);
v___x_265_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31));
v___x_266_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_265_);
v___x_267_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_267_, 0, v_a_249_);
lean_ctor_set(v___x_267_, 1, v___x_192_);
v___x_268_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33);
v___x_269_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36));
lean_inc_n(v_currMacroScope_184_, 5);
lean_inc_n(v_quotContext_183_, 5);
v___x_270_ = l_Lean_addMacroScope(v_quotContext_183_, v___x_269_, v_currMacroScope_184_);
v___x_271_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38));
v___x_272_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_272_, 0, v_a_249_);
lean_ctor_set(v___x_272_, 1, v___x_268_);
lean_ctor_set(v___x_272_, 2, v___x_270_);
lean_ctor_set(v___x_272_, 3, v___x_271_);
v___x_273_ = l_Lean_Syntax_node2(v_a_249_, v___x_191_, v___x_267_, v___x_272_);
v___x_274_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_274_, 0, v_a_249_);
lean_ctor_set(v___x_274_, 1, v___x_204_);
v___x_275_ = l_Lean_Syntax_node1(v_a_249_, v___x_203_, v___x_274_);
lean_inc(v___x_223_);
lean_inc_n(v___x_275_, 2);
v___x_276_ = l_Lean_Syntax_node4(v_a_249_, v___x_201_, v___x_275_, v___x_275_, v___x_275_, v___x_223_);
lean_inc(v___x_189_);
v___x_277_ = l_Lean_Syntax_node2(v_a_249_, v___x_189_, v___x_273_, v___x_276_);
lean_inc_ref_n(v___x_264_, 9);
v___x_278_ = l_Lean_Syntax_node2(v_a_249_, v___x_266_, v___x_264_, v___x_277_);
v___x_279_ = l_Lean_Syntax_node1(v_a_249_, v___x_201_, v___x_278_);
v___x_280_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_281_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_281_, 0, v_a_249_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
v___x_282_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40));
v___x_283_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_282_);
v___x_284_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41));
v___x_285_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_284_);
v___x_286_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_287_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_287_, 0, v_a_249_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44);
v___x_289_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__45));
v___x_290_ = l_Lean_addMacroScope(v_quotContext_183_, v___x_289_, v_currMacroScope_184_);
v___x_291_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49));
v___x_292_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_292_, 0, v_a_249_);
lean_ctor_set(v___x_292_, 1, v___x_288_);
lean_ctor_set(v___x_292_, 2, v___x_290_);
lean_ctor_set(v___x_292_, 3, v___x_291_);
v___x_293_ = l_Lean_Syntax_node1(v_a_249_, v___x_201_, v___x_292_);
v___x_294_ = l_Lean_Syntax_node1(v_a_249_, v___x_201_, v___x_293_);
v___x_295_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_296_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_296_, 0, v_a_249_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__51));
v___x_298_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_297_);
v___x_299_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__52));
v___x_300_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_300_, 0, v_a_249_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = l_Lean_Syntax_node1(v_a_249_, v___x_298_, v___x_300_);
v___x_302_ = l_Lean_Syntax_node2(v_a_249_, v___x_225_, v___x_301_, v___x_264_);
v___x_303_ = l_Lean_Syntax_node1(v_a_249_, v___x_201_, v___x_302_);
lean_inc_n(v___x_259_, 2);
v___x_304_ = l_Lean_Syntax_node1(v_a_249_, v___x_259_, v___x_303_);
lean_inc_ref(v___x_296_);
lean_inc_ref(v___x_287_);
lean_inc(v___x_285_);
v___x_305_ = l_Lean_Syntax_node4(v_a_249_, v___x_285_, v___x_287_, v___x_294_, v___x_296_, v___x_304_);
v___x_306_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54);
v___x_307_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__55));
v___x_308_ = l_Lean_addMacroScope(v_quotContext_183_, v___x_307_, v_currMacroScope_184_);
v___x_309_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__58));
v___x_310_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_310_, 0, v_a_249_);
lean_ctor_set(v___x_310_, 1, v___x_306_);
lean_ctor_set(v___x_310_, 2, v___x_308_);
lean_ctor_set(v___x_310_, 3, v___x_309_);
v___x_311_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__59));
v___x_312_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_311_);
v___x_313_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__60));
v___x_314_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_313_);
v___x_315_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__61));
v___x_316_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_316_, 0, v_a_249_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
v___x_317_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__63));
v___x_318_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65);
v___x_319_ = lean_box(0);
v___x_320_ = l_Lean_addMacroScope(v_quotContext_183_, v___x_319_, v_currMacroScope_184_);
v___x_321_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66));
v___x_322_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67));
v___x_323_ = l_Lean_Name_mkStr3(v___x_168_, v___x_321_, v___x_322_);
v___x_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
v___x_325_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__68));
v___x_326_ = l_Lean_Name_mkStr2(v___x_168_, v___x_325_);
v___x_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
v___x_328_ = l_Lean_Name_mkStr3(v___x_168_, v___x_169_, v___x_170_);
v___x_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
v___x_330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v___x_197_);
v___x_331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_327_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v___x_332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_324_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_333_, 0, v_a_249_);
lean_ctor_set(v___x_333_, 1, v___x_318_);
lean_ctor_set(v___x_333_, 2, v___x_320_);
lean_ctor_set(v___x_333_, 3, v___x_332_);
v___x_334_ = l_Lean_Syntax_node1(v_a_249_, v___x_317_, v___x_333_);
v___x_335_ = l_Lean_Syntax_node2(v_a_249_, v___x_314_, v___x_316_, v___x_334_);
v___x_336_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_336_, 0, v_a_249_);
lean_ctor_set(v___x_336_, 1, v___x_173_);
v___x_337_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70);
v___x_338_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__71));
v___x_339_ = l_Lean_addMacroScope(v_quotContext_183_, v___x_338_, v_currMacroScope_184_);
v___x_340_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_340_, 0, v_a_249_);
lean_ctor_set(v___x_340_, 1, v___x_337_);
lean_ctor_set(v___x_340_, 2, v___x_339_);
lean_ctor_set(v___x_340_, 3, v___x_197_);
lean_inc_ref(v___x_340_);
v___x_341_ = l_Lean_Syntax_node1(v_a_249_, v___x_201_, v___x_340_);
v___x_342_ = l_Lean_Syntax_node3(v_a_249_, v___x_201_, v___x_179_, v___x_336_, v___x_341_);
v___x_343_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__72));
v___x_344_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_344_, 0, v_a_249_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = l_Lean_Syntax_node3(v_a_249_, v___x_312_, v___x_335_, v___x_342_, v___x_344_);
v___x_346_ = l_Lean_Syntax_node1(v_a_249_, v___x_201_, v___x_345_);
v___x_347_ = l_Lean_Syntax_node2(v_a_249_, v___x_189_, v___x_310_, v___x_346_);
v___x_348_ = l_Lean_Syntax_node1(v_a_249_, v___x_201_, v___x_347_);
v___x_349_ = l_Lean_Syntax_node1(v_a_249_, v___x_201_, v___x_348_);
v___x_350_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__73));
v___x_351_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_350_);
v___x_352_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__74));
v___x_353_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_352_);
v___x_354_ = l_Lean_Syntax_node1(v_a_249_, v___x_243_, v___x_223_);
v___x_355_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_355_, 0, v_a_249_);
lean_ctor_set(v___x_355_, 1, v___x_245_);
v___x_356_ = l_Lean_Syntax_node5(v_a_249_, v___x_353_, v___x_354_, v___x_264_, v___x_264_, v___x_355_, v___x_340_);
v___x_357_ = l_Lean_Syntax_node1(v_a_249_, v___x_351_, v___x_356_);
v___x_358_ = l_Lean_Syntax_node2(v_a_249_, v___x_225_, v___x_357_, v___x_264_);
v___x_359_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75));
v___x_360_ = l_Lean_Name_mkStr4(v___x_168_, v___x_169_, v___x_170_, v___x_359_);
v___x_361_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_362_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_362_, 0, v_a_249_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = l_Lean_Syntax_node2(v_a_249_, v___x_360_, v___x_362_, v_snd_174_);
v___x_364_ = l_Lean_Syntax_node2(v_a_249_, v___x_225_, v___x_363_, v___x_264_);
v___x_365_ = l_Lean_Syntax_node2(v_a_249_, v___x_201_, v___x_358_, v___x_364_);
v___x_366_ = l_Lean_Syntax_node1(v_a_249_, v___x_259_, v___x_365_);
v___x_367_ = l_Lean_Syntax_node4(v_a_249_, v___x_285_, v___x_287_, v___x_349_, v___x_296_, v___x_366_);
v___x_368_ = l_Lean_Syntax_node2(v_a_249_, v___x_201_, v___x_305_, v___x_367_);
v___x_369_ = l_Lean_Syntax_node1(v_a_249_, v___x_283_, v___x_368_);
v___x_370_ = l_Lean_Syntax_node7(v_a_249_, v___x_261_, v___x_263_, v___x_264_, v___x_264_, v___x_264_, v___x_279_, v___x_281_, v___x_369_);
v___x_371_ = l_Lean_Syntax_node2(v_a_249_, v___x_225_, v___x_370_, v___x_264_);
v___x_372_ = l_Lean_Syntax_node1(v_a_249_, v___x_201_, v___x_371_);
v___x_373_ = l_Lean_Syntax_node1(v_a_249_, v___x_259_, v___x_372_);
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_257_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
v___x_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 0, v___x_375_);
v___x_377_ = v___x_252_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_a_250_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
else
{
lean_object* v_a_380_; lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
lean_dec(v___x_247_);
lean_dec(v___x_243_);
lean_dec(v___x_239_);
lean_dec(v___x_237_);
lean_dec_ref(v___x_236_);
lean_dec(v___x_232_);
lean_dec_ref(v___x_229_);
lean_dec(v___x_227_);
lean_dec(v___x_225_);
lean_dec(v___x_223_);
lean_dec(v_a_218_);
lean_dec(v___x_203_);
lean_dec(v___x_191_);
lean_dec(v___x_189_);
lean_dec(v___x_179_);
lean_dec(v_snd_174_);
lean_dec_ref(v___x_173_);
lean_dec(v_fst_172_);
lean_dec_ref(v___x_170_);
lean_dec_ref(v___x_169_);
lean_dec_ref(v___x_168_);
v_a_380_ = lean_ctor_get(v___x_248_, 0);
v_a_381_ = lean_ctor_get(v___x_248_, 1);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_248_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_inc(v_a_380_);
lean_dec(v___x_248_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_380_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v_a_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
else
{
lean_object* v_a_389_; lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
lean_dec(v_macroScope_208_);
lean_dec(v___x_207_);
lean_dec(v___x_203_);
lean_dec(v___x_200_);
lean_dec(v___x_191_);
lean_dec(v___x_189_);
lean_dec(v___x_187_);
lean_dec(v___x_180_);
lean_dec(v___x_179_);
lean_dec(v_snd_174_);
lean_dec_ref(v___x_173_);
lean_dec(v_fst_172_);
lean_dec_ref(v___f_171_);
lean_dec_ref(v___x_170_);
lean_dec_ref(v___x_169_);
lean_dec_ref(v___x_168_);
v_a_389_ = lean_ctor_get(v___x_217_, 0);
v_a_390_ = lean_ctor_get(v___x_217_, 1);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_397_ == 0)
{
v___x_392_ = v___x_217_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_inc(v_a_389_);
lean_dec(v___x_217_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_389_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v_a_390_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___boxed(lean_object* v___x_413_, lean_object* v___x_414_, lean_object* v___x_415_, lean_object* v___x_416_, lean_object* v___x_417_, lean_object* v___x_418_, lean_object* v___x_419_, lean_object* v___f_420_, lean_object* v_fst_421_, lean_object* v___x_422_, lean_object* v_snd_423_, lean_object* v_x_424_, lean_object* v_h_x3f_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
uint8_t v___x_145958__boxed_428_; lean_object* v_res_429_; 
v___x_145958__boxed_428_ = lean_unbox(v___x_416_);
v_res_429_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(v___x_413_, v___x_414_, v___x_415_, v___x_145958__boxed_428_, v___x_417_, v___x_418_, v___x_419_, v___f_420_, v_fst_421_, v___x_422_, v_snd_423_, v_x_424_, v_h_x3f_425_, v___y_426_, v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v_h_x3f_425_);
lean_dec(v___x_415_);
lean_dec(v___x_414_);
lean_dec(v___x_413_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0(uint8_t v___x_430_, lean_object* v_____do__lift_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = l_Lean_SourceInfo_fromRef(v_____do__lift_431_, v___x_430_);
v___x_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
lean_ctor_set(v___x_435_, 1, v___y_433_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0___boxed(lean_object* v___x_436_, lean_object* v_____do__lift_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
uint8_t v___x_146564__boxed_440_; lean_object* v_res_441_; 
v___x_146564__boxed_440_ = lean_unbox(v___x_436_);
v_res_441_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0(v___x_146564__boxed_440_, v_____do__lift_437_, v___y_438_, v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v_____do__lift_437_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(uint8_t v___x_452_, lean_object* v_a_453_, lean_object* v_b_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_array_457_; lean_object* v_start_458_; lean_object* v_stop_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_553_; 
v_array_457_ = lean_ctor_get(v_a_453_, 0);
v_start_458_ = lean_ctor_get(v_a_453_, 1);
v_stop_459_ = lean_ctor_get(v_a_453_, 2);
v_isSharedCheck_553_ = !lean_is_exclusive(v_a_453_);
if (v_isSharedCheck_553_ == 0)
{
v___x_461_ = v_a_453_;
v_isShared_462_ = v_isSharedCheck_553_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_stop_459_);
lean_inc(v_start_458_);
lean_inc(v_array_457_);
lean_dec(v_a_453_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_553_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
uint8_t v___x_463_; 
v___x_463_ = lean_nat_dec_lt(v_start_458_, v_stop_459_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; 
lean_del_object(v___x_461_);
lean_dec(v_stop_459_);
lean_dec(v_start_458_);
lean_dec_ref(v_array_457_);
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v_b_454_);
lean_ctor_set(v___x_464_, 1, v___y_456_);
return v___x_464_;
}
else
{
lean_object* v_fst_465_; lean_object* v_snd_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_552_; 
v_fst_465_ = lean_ctor_get(v_b_454_, 0);
v_snd_466_ = lean_ctor_get(v_b_454_, 1);
v_isSharedCheck_552_ = !lean_is_exclusive(v_b_454_);
if (v_isSharedCheck_552_ == 0)
{
v___x_468_ = v_b_454_;
v_isShared_469_ = v_isSharedCheck_552_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_snd_466_);
lean_inc(v_fst_465_);
lean_dec(v_b_454_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_552_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_470_ = lean_unsigned_to_nat(1u);
v___x_471_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0));
v___x_472_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1));
v___x_473_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2));
v___x_474_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
v___x_475_ = lean_nat_add(v_start_458_, v___x_470_);
lean_inc_ref(v_array_457_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 1, v___x_475_);
v___x_477_ = v___x_461_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_array_457_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_551_, 2, v_stop_459_);
v___x_477_ = v_reuseFailAlloc_551_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v___y_479_; lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_503_ = lean_array_fget(v_array_457_, v_start_458_);
lean_dec(v_start_458_);
lean_dec_ref(v_array_457_);
lean_inc(v___x_503_);
v___x_504_ = l_Lean_Syntax_isOfKind(v___x_503_, v___x_474_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; 
lean_dec(v___x_503_);
v___x_505_ = l_Lean_Macro_throwUnsupported___redArg(v___y_456_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_508_; 
v_a_506_ = lean_ctor_get(v___x_505_, 1);
lean_inc(v_a_506_);
lean_dec_ref(v___x_505_);
if (v_isShared_469_ == 0)
{
v___x_508_ = v___x_468_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_fst_465_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_snd_466_);
v___x_508_ = v_reuseFailAlloc_510_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
v_a_453_ = v___x_477_;
v_b_454_ = v___x_508_;
v___y_456_ = v_a_506_;
goto _start;
}
}
else
{
lean_object* v_a_511_; lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
lean_dec_ref(v___x_477_);
lean_del_object(v___x_468_);
lean_dec(v_snd_466_);
lean_dec(v_fst_465_);
v_a_511_ = lean_ctor_get(v___x_505_, 0);
v_a_512_ = lean_ctor_get(v___x_505_, 1);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_505_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_inc(v_a_511_);
lean_dec(v___x_505_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_511_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_a_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
else
{
lean_object* v___x_520_; lean_object* v___f_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_520_ = lean_box(v___x_452_);
v___f_521_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_521_, 0, v___x_520_);
v___x_522_ = lean_unsigned_to_nat(3u);
v___x_523_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__5));
v___x_524_ = lean_unsigned_to_nat(0u);
v___x_525_ = l_Lean_Syntax_getArg(v___x_503_, v___x_524_);
v___x_526_ = l_Lean_Syntax_isNone(v___x_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_527_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_525_);
v___x_528_ = l_Lean_Syntax_matchesNull(v___x_525_, v___x_527_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; 
lean_dec(v___x_525_);
lean_dec_ref(v___f_521_);
lean_dec(v___x_503_);
v___x_529_ = l_Lean_Macro_throwUnsupported___redArg(v___y_456_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; lean_object* v___x_532_; 
v_a_530_ = lean_ctor_get(v___x_529_, 1);
lean_inc(v_a_530_);
lean_dec_ref(v___x_529_);
if (v_isShared_469_ == 0)
{
v___x_532_ = v___x_468_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_fst_465_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v_snd_466_);
v___x_532_ = v_reuseFailAlloc_534_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
v_a_453_ = v___x_477_;
v_b_454_ = v___x_532_;
v___y_456_ = v_a_530_;
goto _start;
}
}
else
{
lean_object* v_a_535_; lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
lean_dec_ref(v___x_477_);
lean_del_object(v___x_468_);
lean_dec(v_snd_466_);
lean_dec(v_fst_465_);
v_a_535_ = lean_ctor_get(v___x_529_, 0);
v_a_536_ = lean_ctor_get(v___x_529_, 1);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_543_ == 0)
{
v___x_538_ = v___x_529_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_inc(v_a_535_);
lean_dec(v___x_529_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_535_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_a_536_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
else
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
lean_del_object(v___x_468_);
v___x_544_ = l_Lean_Syntax_getArg(v___x_525_, v___x_524_);
lean_dec(v___x_525_);
v___x_545_ = lean_box(0);
v___x_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_544_);
v___x_547_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(v___x_503_, v___x_470_, v___x_522_, v___x_452_, v___x_471_, v___x_472_, v___x_473_, v___f_521_, v_fst_465_, v___x_523_, v_snd_466_, v___x_545_, v___x_546_, v___y_455_, v___y_456_);
lean_dec_ref(v___x_546_);
lean_dec(v___x_503_);
v___y_479_ = v___x_547_;
goto v___jp_478_;
}
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
lean_dec(v___x_525_);
lean_del_object(v___x_468_);
v___x_548_ = lean_box(0);
v___x_549_ = lean_box(0);
v___x_550_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(v___x_503_, v___x_470_, v___x_522_, v___x_452_, v___x_471_, v___x_472_, v___x_473_, v___f_521_, v_fst_465_, v___x_523_, v_snd_466_, v___x_548_, v___x_549_, v___y_455_, v___y_456_);
lean_dec(v___x_503_);
v___y_479_ = v___x_550_;
goto v___jp_478_;
}
}
v___jp_478_:
{
if (lean_obj_tag(v___y_479_) == 0)
{
lean_object* v_a_480_; 
v_a_480_ = lean_ctor_get(v___y_479_, 0);
lean_inc(v_a_480_);
if (lean_obj_tag(v_a_480_) == 0)
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_489_; 
lean_dec_ref(v___x_477_);
v_a_481_ = lean_ctor_get(v___y_479_, 1);
v_isSharedCheck_489_ = !lean_is_exclusive(v___y_479_);
if (v_isSharedCheck_489_ == 0)
{
lean_object* v_unused_490_; 
v_unused_490_ = lean_ctor_get(v___y_479_, 0);
lean_dec(v_unused_490_);
v___x_483_ = v___y_479_;
v_isShared_484_ = v_isSharedCheck_489_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___y_479_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_489_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v_a_485_; lean_object* v___x_487_; 
v_a_485_ = lean_ctor_get(v_a_480_, 0);
lean_inc(v_a_485_);
lean_dec_ref(v_a_480_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v_a_485_);
v___x_487_ = v___x_483_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_485_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v_a_481_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
else
{
lean_object* v_a_491_; lean_object* v_a_492_; 
v_a_491_ = lean_ctor_get(v___y_479_, 1);
lean_inc(v_a_491_);
lean_dec_ref(v___y_479_);
v_a_492_ = lean_ctor_get(v_a_480_, 0);
lean_inc(v_a_492_);
lean_dec_ref(v_a_480_);
v_a_453_ = v___x_477_;
v_b_454_ = v_a_492_;
v___y_456_ = v_a_491_;
goto _start;
}
}
else
{
lean_object* v_a_494_; lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
lean_dec_ref(v___x_477_);
v_a_494_ = lean_ctor_get(v___y_479_, 0);
v_a_495_ = lean_ctor_get(v___y_479_, 1);
v_isSharedCheck_502_ = !lean_is_exclusive(v___y_479_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___y_479_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_inc(v_a_494_);
lean_dec(v___y_479_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_494_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v_a_495_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___boxed(lean_object* v___x_554_, lean_object* v_a_555_, lean_object* v_b_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
uint8_t v___x_146600__boxed_559_; lean_object* v_res_560_; 
v___x_146600__boxed_559_ = lean_unbox(v___x_554_);
v_res_560_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_146600__boxed_559_, v_a_555_, v_b_556_, v___y_557_, v___y_558_);
lean_dec_ref(v___y_557_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor(lean_object* v_stx_617_, lean_object* v_a_618_, lean_object* v_a_619_){
_start:
{
lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_620_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
lean_inc(v_stx_617_);
v___x_621_ = l_Lean_Syntax_isOfKind(v_stx_617_, v___x_620_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; 
lean_dec(v_stx_617_);
v___x_622_ = l_Lean_Macro_throwUnsupported___redArg(v_a_619_);
return v___x_622_;
}
else
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v___x_623_ = lean_unsigned_to_nat(0u);
v___x_624_ = lean_unsigned_to_nat(1u);
v___x_625_ = l_Lean_Syntax_getArg(v_stx_617_, v___x_624_);
lean_inc(v___x_625_);
v___x_626_ = l_Lean_Syntax_matchesNull(v___x_625_, v___x_624_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v_decls_659_; lean_object* v_decls_660_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v_x_665_; lean_object* v_body_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_627_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
v_decls_659_ = l_Lean_Syntax_getArgs(v___x_625_);
lean_dec(v___x_625_);
v_decls_660_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_659_);
lean_dec_ref(v_decls_659_);
v___x_704_ = lean_box(0);
v___x_705_ = lean_array_get(v___x_704_, v_decls_660_, v___x_623_);
lean_inc(v___x_705_);
v___x_706_ = l_Lean_Syntax_isOfKind(v___x_705_, v___x_627_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; 
lean_dec(v___x_705_);
lean_dec_ref(v_decls_660_);
lean_dec(v_stx_617_);
v___x_707_ = l_Lean_Macro_throwUnsupported___redArg(v_a_619_);
return v___x_707_;
}
else
{
lean_object* v___x_708_; lean_object* v_body_709_; lean_object* v_h_x3f_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_708_ = lean_unsigned_to_nat(3u);
v_body_709_ = l_Lean_Syntax_getArg(v_stx_617_, v___x_708_);
lean_dec(v_stx_617_);
v___x_774_ = l_Lean_Syntax_getArg(v___x_705_, v___x_623_);
v___x_775_ = l_Lean_Syntax_isNone(v___x_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; uint8_t v___x_777_; 
v___x_776_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_774_);
v___x_777_ = l_Lean_Syntax_matchesNull(v___x_774_, v___x_776_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; 
lean_dec(v___x_774_);
lean_dec(v_body_709_);
lean_dec(v___x_705_);
lean_dec_ref(v_decls_660_);
v___x_778_ = l_Lean_Macro_throwUnsupported___redArg(v_a_619_);
return v___x_778_;
}
else
{
lean_object* v_h_x3f_779_; lean_object* v___x_780_; 
v_h_x3f_779_ = l_Lean_Syntax_getArg(v___x_774_, v___x_623_);
lean_dec(v___x_774_);
v___x_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_780_, 0, v_h_x3f_779_);
v_h_x3f_711_ = v___x_780_;
v___y_712_ = v_a_618_;
v___y_713_ = v_a_619_;
goto v___jp_710_;
}
}
else
{
lean_object* v___x_781_; 
lean_dec(v___x_774_);
v___x_781_ = lean_box(0);
v_h_x3f_711_ = v___x_781_;
v___y_712_ = v_a_618_;
v___y_713_ = v_a_619_;
goto v___jp_710_;
}
v___jp_710_:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v_doElems_716_; uint8_t v___x_717_; 
v___x_714_ = l_Lean_Syntax_getArg(v___x_705_, v___x_624_);
v___x_715_ = l_Lean_Syntax_getArg(v___x_705_, v___x_708_);
lean_dec(v___x_705_);
v_doElems_716_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_717_ = l_Lean_Syntax_isIdent(v___x_714_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_718_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_714_);
v___x_719_ = l_Lean_Syntax_isOfKind(v___x_714_, v___x_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_714_, v___x_719_, v___y_712_, v___y_713_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; lean_object* v_a_722_; lean_object* v_ref_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc_n(v_a_721_, 2);
v_a_722_ = lean_ctor_get(v___x_720_, 1);
lean_inc(v_a_722_);
lean_dec_ref(v___x_720_);
v_ref_723_ = lean_ctor_get(v___y_712_, 5);
v___x_724_ = l_Lean_SourceInfo_fromRef(v_ref_723_, v___x_719_);
v___x_725_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_726_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_727_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_728_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_729_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_n(v___x_724_, 15);
v___x_730_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_724_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_732_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_732_, 0, v___x_724_);
lean_ctor_set(v___x_732_, 1, v___x_726_);
lean_ctor_set(v___x_732_, 2, v___x_731_);
v___x_733_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_732_, 4);
v___x_734_ = l_Lean_Syntax_node2(v___x_724_, v___x_733_, v___x_732_, v_a_721_);
v___x_735_ = l_Lean_Syntax_node1(v___x_724_, v___x_726_, v___x_734_);
v___x_736_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_737_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_724_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
v___x_738_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_739_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_740_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_741_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_724_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = l_Lean_Syntax_node1(v___x_724_, v___x_726_, v___x_714_);
v___x_743_ = l_Lean_Syntax_node1(v___x_724_, v___x_726_, v___x_742_);
v___x_744_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_745_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_724_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = l_Lean_Syntax_node4(v___x_724_, v___x_739_, v___x_741_, v___x_743_, v___x_745_, v_body_709_);
v___x_747_ = l_Lean_Syntax_node1(v___x_724_, v___x_726_, v___x_746_);
v___x_748_ = l_Lean_Syntax_node1(v___x_724_, v___x_738_, v___x_747_);
v___x_749_ = l_Lean_Syntax_node7(v___x_724_, v___x_728_, v___x_730_, v___x_732_, v___x_732_, v___x_732_, v___x_735_, v___x_737_, v___x_748_);
v___x_750_ = l_Lean_Syntax_node2(v___x_724_, v___x_727_, v___x_749_, v___x_732_);
v___x_751_ = l_Lean_Syntax_node1(v___x_724_, v___x_726_, v___x_750_);
v___x_752_ = l_Lean_Syntax_node1(v___x_724_, v___x_725_, v___x_751_);
v___y_662_ = v_h_x3f_711_;
v___y_663_ = v_doElems_716_;
v___y_664_ = v___x_715_;
v_x_665_ = v_a_721_;
v_body_666_ = v___x_752_;
v___y_667_ = v___y_712_;
v___y_668_ = v_a_722_;
goto v___jp_661_;
}
else
{
lean_object* v_a_753_; lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec(v___x_715_);
lean_dec(v___x_714_);
lean_dec(v_h_x3f_711_);
lean_dec(v_body_709_);
lean_dec_ref(v_decls_660_);
v_a_753_ = lean_ctor_get(v___x_720_, 0);
v_a_754_ = lean_ctor_get(v___x_720_, 1);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_720_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_inc(v_a_753_);
lean_dec(v___x_720_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_753_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
else
{
lean_object* v___x_762_; 
v___x_762_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_714_, v___x_717_, v___y_712_, v___y_713_);
lean_dec(v___x_714_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v_a_764_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_a_763_);
v_a_764_ = lean_ctor_get(v___x_762_, 1);
lean_inc(v_a_764_);
lean_dec_ref(v___x_762_);
v___y_662_ = v_h_x3f_711_;
v___y_663_ = v_doElems_716_;
v___y_664_ = v___x_715_;
v_x_665_ = v_a_763_;
v_body_666_ = v_body_709_;
v___y_667_ = v___y_712_;
v___y_668_ = v_a_764_;
goto v___jp_661_;
}
else
{
lean_object* v_a_765_; lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec(v___x_715_);
lean_dec(v_h_x3f_711_);
lean_dec(v_body_709_);
lean_dec_ref(v_decls_660_);
v_a_765_ = lean_ctor_get(v___x_762_, 0);
v_a_766_ = lean_ctor_get(v___x_762_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_762_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_inc(v_a_765_);
lean_dec(v___x_762_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_765_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
else
{
v___y_662_ = v_h_x3f_711_;
v___y_663_ = v_doElems_716_;
v___y_664_ = v___x_715_;
v_x_665_ = v___x_714_;
v_body_666_ = v_body_709_;
v___y_667_ = v___y_712_;
v___y_668_ = v___y_713_;
goto v___jp_661_;
}
}
}
v___jp_628_:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
lean_inc_ref_n(v___y_635_, 3);
v___x_640_ = l_Array_append___redArg(v___y_635_, v___y_639_);
lean_dec_ref(v___y_639_);
lean_inc_n(v___y_638_, 4);
lean_inc_n(v___y_634_, 10);
v___x_641_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_641_, 0, v___y_634_);
lean_ctor_set(v___x_641_, 1, v___y_638_);
lean_ctor_set(v___x_641_, 2, v___x_640_);
v___x_642_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_643_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_643_, 0, v___y_634_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
v___x_644_ = l_Lean_Syntax_node4(v___y_634_, v___x_627_, v___x_641_, v___y_631_, v___x_643_, v___y_637_);
v___x_645_ = l_Lean_Syntax_node1(v___y_634_, v___y_638_, v___x_644_);
v___x_646_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_647_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_647_, 0, v___y_634_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
lean_inc_ref(v___x_647_);
v___x_648_ = l_Lean_Syntax_node4(v___y_634_, v___x_620_, v___y_633_, v___x_645_, v___x_647_, v___y_630_);
v___x_649_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_649_, 0, v___y_634_);
lean_ctor_set(v___x_649_, 1, v___y_638_);
lean_ctor_set(v___x_649_, 2, v___y_635_);
lean_inc(v___y_629_);
v___x_650_ = l_Lean_Syntax_node2(v___y_634_, v___y_629_, v___x_648_, v___x_649_);
v___x_651_ = lean_array_push(v___y_632_, v___x_650_);
v___x_652_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_653_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_654_ = l_Array_append___redArg(v___y_635_, v___x_651_);
lean_dec_ref(v___x_651_);
v___x_655_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_655_, 0, v___y_634_);
lean_ctor_set(v___x_655_, 1, v___y_638_);
lean_ctor_set(v___x_655_, 2, v___x_654_);
v___x_656_ = l_Lean_Syntax_node1(v___y_634_, v___x_653_, v___x_655_);
v___x_657_ = l_Lean_Syntax_node2(v___y_634_, v___x_652_, v___x_647_, v___x_656_);
v___x_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
lean_ctor_set(v___x_658_, 1, v___y_636_);
return v___x_658_;
}
v___jp_661_:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_669_ = lean_array_get_size(v_decls_660_);
v___x_670_ = l_Array_toSubarray___redArg(v_decls_660_, v___x_624_, v___x_669_);
lean_inc_ref(v___y_663_);
v___x_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_671_, 0, v___y_663_);
lean_ctor_set(v___x_671_, 1, v_body_666_);
v___x_672_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_626_, v___x_670_, v___x_671_, v___y_667_, v___y_668_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v_a_674_; lean_object* v_fst_675_; lean_object* v_snd_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_694_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_a_673_);
v_a_674_ = lean_ctor_get(v___x_672_, 1);
lean_inc(v_a_674_);
lean_dec_ref(v___x_672_);
v_fst_675_ = lean_ctor_get(v_a_673_, 0);
v_snd_676_ = lean_ctor_get(v_a_673_, 1);
v_isSharedCheck_694_ = !lean_is_exclusive(v_a_673_);
if (v_isSharedCheck_694_ == 0)
{
v___x_678_ = v_a_673_;
v_isShared_679_ = v_isSharedCheck_694_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_snd_676_);
lean_inc(v_fst_675_);
lean_dec(v_a_673_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_694_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v_ref_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_685_; 
v_ref_680_ = lean_ctor_get(v___y_667_, 5);
v___x_681_ = l_Lean_SourceInfo_fromRef(v_ref_680_, v___x_626_);
v___x_682_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_683_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
lean_inc(v___x_681_);
if (v_isShared_679_ == 0)
{
lean_ctor_set_tag(v___x_678_, 2);
lean_ctor_set(v___x_678_, 1, v___x_683_);
lean_ctor_set(v___x_678_, 0, v___x_681_);
v___x_685_ = v___x_678_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_681_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v___x_683_);
v___x_685_ = v_reuseFailAlloc_693_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_687_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
if (lean_obj_tag(v___y_662_) == 1)
{
lean_object* v_val_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v_val_688_ = lean_ctor_get(v___y_662_, 0);
lean_inc(v_val_688_);
lean_dec_ref(v___y_662_);
v___x_689_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
lean_inc(v___x_681_);
v___x_690_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_681_);
lean_ctor_set(v___x_690_, 1, v___x_689_);
v___x_691_ = l_Array_mkArray2___redArg(v_val_688_, v___x_690_);
v___y_629_ = v___x_682_;
v___y_630_ = v_snd_676_;
v___y_631_ = v_x_665_;
v___y_632_ = v_fst_675_;
v___y_633_ = v___x_685_;
v___y_634_ = v___x_681_;
v___y_635_ = v___x_687_;
v___y_636_ = v_a_674_;
v___y_637_ = v___y_664_;
v___y_638_ = v___x_686_;
v___y_639_ = v___x_691_;
goto v___jp_628_;
}
else
{
lean_object* v___x_692_; 
lean_dec(v___y_662_);
v___x_692_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
v___y_629_ = v___x_682_;
v___y_630_ = v_snd_676_;
v___y_631_ = v_x_665_;
v___y_632_ = v_fst_675_;
v___y_633_ = v___x_685_;
v___y_634_ = v___x_681_;
v___y_635_ = v___x_687_;
v___y_636_ = v_a_674_;
v___y_637_ = v___y_664_;
v___y_638_ = v___x_686_;
v___y_639_ = v___x_692_;
goto v___jp_628_;
}
}
}
}
else
{
lean_object* v_a_695_; lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
lean_dec(v_x_665_);
lean_dec(v___y_664_);
lean_dec(v___y_662_);
v_a_695_ = lean_ctor_get(v___x_672_, 0);
v_a_696_ = lean_ctor_get(v___x_672_, 1);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_672_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_inc(v_a_695_);
lean_dec(v___x_672_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_695_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
}
else
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; uint8_t v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v_x_852_; lean_object* v_body_853_; lean_object* v___y_854_; lean_object* v___y_855_; uint8_t v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v_h_x3f_897_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; uint8_t v___x_1014_; 
v___x_782_ = l_Lean_Syntax_getArg(v___x_625_, v___x_623_);
v___x_783_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
lean_inc(v___x_782_);
v___x_1014_ = l_Lean_Syntax_isOfKind(v___x_782_, v___x_783_);
if (v___x_1014_ == 0)
{
lean_object* v_decls_1015_; lean_object* v_decls_1016_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v_x_1021_; lean_object* v_body_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___x_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; 
lean_dec(v___x_782_);
v_decls_1015_ = l_Lean_Syntax_getArgs(v___x_625_);
lean_dec(v___x_625_);
v_decls_1016_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_1015_);
lean_dec_ref(v_decls_1015_);
v___x_1060_ = lean_box(0);
v___x_1061_ = lean_array_get(v___x_1060_, v_decls_1016_, v___x_623_);
lean_inc(v___x_1061_);
v___x_1062_ = l_Lean_Syntax_isOfKind(v___x_1061_, v___x_783_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1063_; 
lean_dec(v___x_1061_);
lean_dec_ref(v_decls_1016_);
lean_dec(v_stx_617_);
v___x_1063_ = l_Lean_Macro_throwUnsupported___redArg(v_a_619_);
return v___x_1063_;
}
else
{
lean_object* v___x_1064_; lean_object* v_body_1065_; lean_object* v_h_x3f_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___x_1130_; uint8_t v___x_1131_; 
v___x_1064_ = lean_unsigned_to_nat(3u);
v_body_1065_ = l_Lean_Syntax_getArg(v_stx_617_, v___x_1064_);
lean_dec(v_stx_617_);
v___x_1130_ = l_Lean_Syntax_getArg(v___x_1061_, v___x_623_);
v___x_1131_ = l_Lean_Syntax_isNone(v___x_1130_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; uint8_t v___x_1133_; 
v___x_1132_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1130_);
v___x_1133_ = l_Lean_Syntax_matchesNull(v___x_1130_, v___x_1132_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; 
lean_dec(v___x_1130_);
lean_dec(v_body_1065_);
lean_dec(v___x_1061_);
lean_dec_ref(v_decls_1016_);
v___x_1134_ = l_Lean_Macro_throwUnsupported___redArg(v_a_619_);
return v___x_1134_;
}
else
{
lean_object* v_h_x3f_1135_; lean_object* v___x_1136_; 
v_h_x3f_1135_ = l_Lean_Syntax_getArg(v___x_1130_, v___x_623_);
lean_dec(v___x_1130_);
v___x_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1136_, 0, v_h_x3f_1135_);
v_h_x3f_1067_ = v___x_1136_;
v___y_1068_ = v_a_618_;
v___y_1069_ = v_a_619_;
goto v___jp_1066_;
}
}
else
{
lean_object* v___x_1137_; 
lean_dec(v___x_1130_);
v___x_1137_ = lean_box(0);
v_h_x3f_1067_ = v___x_1137_;
v___y_1068_ = v_a_618_;
v___y_1069_ = v_a_619_;
goto v___jp_1066_;
}
v___jp_1066_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v_doElems_1072_; uint8_t v___x_1073_; 
v___x_1070_ = l_Lean_Syntax_getArg(v___x_1061_, v___x_624_);
v___x_1071_ = l_Lean_Syntax_getArg(v___x_1061_, v___x_1064_);
lean_dec(v___x_1061_);
v_doElems_1072_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_1073_ = l_Lean_Syntax_isIdent(v___x_1070_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; uint8_t v___x_1075_; 
v___x_1074_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_1070_);
v___x_1075_ = l_Lean_Syntax_isOfKind(v___x_1070_, v___x_1074_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1070_, v___x_1075_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v_a_1078_; lean_object* v_ref_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc_n(v_a_1077_, 2);
v_a_1078_ = lean_ctor_get(v___x_1076_, 1);
lean_inc(v_a_1078_);
lean_dec_ref(v___x_1076_);
v_ref_1079_ = lean_ctor_get(v___y_1068_, 5);
v___x_1080_ = l_Lean_SourceInfo_fromRef(v_ref_1079_, v___x_1075_);
v___x_1081_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_1082_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1083_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_1084_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_1085_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_n(v___x_1080_, 15);
v___x_1086_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1080_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_1088_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1080_);
lean_ctor_set(v___x_1088_, 1, v___x_1082_);
lean_ctor_set(v___x_1088_, 2, v___x_1087_);
v___x_1089_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_1088_, 4);
v___x_1090_ = l_Lean_Syntax_node2(v___x_1080_, v___x_1089_, v___x_1088_, v_a_1077_);
v___x_1091_ = l_Lean_Syntax_node1(v___x_1080_, v___x_1082_, v___x_1090_);
v___x_1092_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_1093_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1080_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_1095_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_1096_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_1097_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1080_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = l_Lean_Syntax_node1(v___x_1080_, v___x_1082_, v___x_1070_);
v___x_1099_ = l_Lean_Syntax_node1(v___x_1080_, v___x_1082_, v___x_1098_);
v___x_1100_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_1101_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1080_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
v___x_1102_ = l_Lean_Syntax_node4(v___x_1080_, v___x_1095_, v___x_1097_, v___x_1099_, v___x_1101_, v_body_1065_);
v___x_1103_ = l_Lean_Syntax_node1(v___x_1080_, v___x_1082_, v___x_1102_);
v___x_1104_ = l_Lean_Syntax_node1(v___x_1080_, v___x_1094_, v___x_1103_);
v___x_1105_ = l_Lean_Syntax_node7(v___x_1080_, v___x_1084_, v___x_1086_, v___x_1088_, v___x_1088_, v___x_1088_, v___x_1091_, v___x_1093_, v___x_1104_);
v___x_1106_ = l_Lean_Syntax_node2(v___x_1080_, v___x_1083_, v___x_1105_, v___x_1088_);
v___x_1107_ = l_Lean_Syntax_node1(v___x_1080_, v___x_1082_, v___x_1106_);
v___x_1108_ = l_Lean_Syntax_node1(v___x_1080_, v___x_1081_, v___x_1107_);
v___y_1018_ = v_h_x3f_1067_;
v___y_1019_ = v_doElems_1072_;
v___y_1020_ = v___x_1071_;
v_x_1021_ = v_a_1077_;
v_body_1022_ = v___x_1108_;
v___y_1023_ = v___y_1068_;
v___y_1024_ = v_a_1078_;
goto v___jp_1017_;
}
else
{
lean_object* v_a_1109_; lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
lean_dec(v___x_1071_);
lean_dec(v___x_1070_);
lean_dec(v_h_x3f_1067_);
lean_dec(v_body_1065_);
lean_dec_ref(v_decls_1016_);
v_a_1109_ = lean_ctor_get(v___x_1076_, 0);
v_a_1110_ = lean_ctor_get(v___x_1076_, 1);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1112_ = v___x_1076_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_inc(v_a_1109_);
lean_dec(v___x_1076_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1109_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v_a_1110_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
else
{
lean_object* v___x_1118_; 
v___x_1118_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1070_, v___x_1073_, v___y_1068_, v___y_1069_);
lean_dec(v___x_1070_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v_a_1120_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_a_1119_);
v_a_1120_ = lean_ctor_get(v___x_1118_, 1);
lean_inc(v_a_1120_);
lean_dec_ref(v___x_1118_);
v___y_1018_ = v_h_x3f_1067_;
v___y_1019_ = v_doElems_1072_;
v___y_1020_ = v___x_1071_;
v_x_1021_ = v_a_1119_;
v_body_1022_ = v_body_1065_;
v___y_1023_ = v___y_1068_;
v___y_1024_ = v_a_1120_;
goto v___jp_1017_;
}
else
{
lean_object* v_a_1121_; lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
lean_dec(v___x_1071_);
lean_dec(v_h_x3f_1067_);
lean_dec(v_body_1065_);
lean_dec_ref(v_decls_1016_);
v_a_1121_ = lean_ctor_get(v___x_1118_, 0);
v_a_1122_ = lean_ctor_get(v___x_1118_, 1);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1118_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_inc(v_a_1121_);
lean_dec(v___x_1118_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1121_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
}
else
{
v___y_1018_ = v_h_x3f_1067_;
v___y_1019_ = v_doElems_1072_;
v___y_1020_ = v___x_1071_;
v_x_1021_ = v___x_1070_;
v_body_1022_ = v_body_1065_;
v___y_1023_ = v___y_1068_;
v___y_1024_ = v___y_1069_;
goto v___jp_1017_;
}
}
}
v___jp_1017_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1025_ = lean_array_get_size(v_decls_1016_);
v___x_1026_ = l_Array_toSubarray___redArg(v_decls_1016_, v___x_624_, v___x_1025_);
lean_inc_ref(v___y_1019_);
v___x_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___y_1019_);
lean_ctor_set(v___x_1027_, 1, v_body_1022_);
v___x_1028_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_1014_, v___x_1026_, v___x_1027_, v___y_1023_, v___y_1024_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; lean_object* v_a_1030_; lean_object* v_fst_1031_; lean_object* v_snd_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1050_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_a_1029_);
v_a_1030_ = lean_ctor_get(v___x_1028_, 1);
lean_inc(v_a_1030_);
lean_dec_ref(v___x_1028_);
v_fst_1031_ = lean_ctor_get(v_a_1029_, 0);
v_snd_1032_ = lean_ctor_get(v_a_1029_, 1);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_a_1029_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1034_ = v_a_1029_;
v_isShared_1035_ = v_isSharedCheck_1050_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_snd_1032_);
lean_inc(v_fst_1031_);
lean_dec(v_a_1029_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1050_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v_ref_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; 
v_ref_1036_ = lean_ctor_get(v___y_1023_, 5);
v___x_1037_ = l_Lean_SourceInfo_fromRef(v_ref_1036_, v___x_1014_);
v___x_1038_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_1039_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
lean_inc(v___x_1037_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set_tag(v___x_1034_, 2);
lean_ctor_set(v___x_1034_, 1, v___x_1039_);
lean_ctor_set(v___x_1034_, 0, v___x_1037_);
v___x_1041_ = v___x_1034_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1043_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
if (lean_obj_tag(v___y_1018_) == 1)
{
lean_object* v_val_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v_val_1044_ = lean_ctor_get(v___y_1018_, 0);
lean_inc(v_val_1044_);
lean_dec_ref(v___y_1018_);
v___x_1045_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
lean_inc(v___x_1037_);
v___x_1046_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1037_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = l_Array_mkArray2___redArg(v_val_1044_, v___x_1046_);
v___y_984_ = v___x_1037_;
v___y_985_ = v___x_1041_;
v___y_986_ = v_x_1021_;
v___y_987_ = v___x_1043_;
v___y_988_ = v_fst_1031_;
v___y_989_ = v___x_1038_;
v___y_990_ = v_snd_1032_;
v___y_991_ = v___x_1042_;
v___y_992_ = v_a_1030_;
v___y_993_ = v___y_1020_;
v___y_994_ = v___x_1047_;
goto v___jp_983_;
}
else
{
lean_object* v___x_1048_; 
lean_dec(v___y_1018_);
v___x_1048_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
v___y_984_ = v___x_1037_;
v___y_985_ = v___x_1041_;
v___y_986_ = v_x_1021_;
v___y_987_ = v___x_1043_;
v___y_988_ = v_fst_1031_;
v___y_989_ = v___x_1038_;
v___y_990_ = v_snd_1032_;
v___y_991_ = v___x_1042_;
v___y_992_ = v_a_1030_;
v___y_993_ = v___y_1020_;
v___y_994_ = v___x_1048_;
goto v___jp_983_;
}
}
}
}
else
{
lean_object* v_a_1051_; lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_dec(v_x_1021_);
lean_dec(v___y_1020_);
lean_dec(v___y_1018_);
v_a_1051_ = lean_ctor_get(v___x_1028_, 0);
v_a_1052_ = lean_ctor_get(v___x_1028_, 1);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1028_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_inc(v_a_1051_);
lean_dec(v___x_1028_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1051_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
else
{
lean_object* v___x_1138_; uint8_t v___x_1139_; 
v___x_1138_ = l_Lean_Syntax_getArg(v___x_782_, v___x_623_);
v___x_1139_ = l_Lean_Syntax_isNone(v___x_1138_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; uint8_t v___x_1141_; 
v___x_1140_ = lean_unsigned_to_nat(2u);
v___x_1141_ = l_Lean_Syntax_matchesNull(v___x_1138_, v___x_1140_);
if (v___x_1141_ == 0)
{
lean_object* v_decls_1142_; lean_object* v_decls_1143_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v_x_1148_; lean_object* v_body_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___x_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; 
lean_dec(v___x_782_);
v_decls_1142_ = l_Lean_Syntax_getArgs(v___x_625_);
lean_dec(v___x_625_);
v_decls_1143_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_1142_);
lean_dec_ref(v_decls_1142_);
v___x_1187_ = lean_box(0);
v___x_1188_ = lean_array_get(v___x_1187_, v_decls_1143_, v___x_623_);
lean_inc(v___x_1188_);
v___x_1189_ = l_Lean_Syntax_isOfKind(v___x_1188_, v___x_783_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; 
lean_dec(v___x_1188_);
lean_dec_ref(v_decls_1143_);
lean_dec(v_stx_617_);
v___x_1190_ = l_Lean_Macro_throwUnsupported___redArg(v_a_619_);
return v___x_1190_;
}
else
{
lean_object* v___x_1191_; lean_object* v_body_1192_; lean_object* v_h_x3f_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___x_1257_; uint8_t v___x_1258_; 
v___x_1191_ = lean_unsigned_to_nat(3u);
v_body_1192_ = l_Lean_Syntax_getArg(v_stx_617_, v___x_1191_);
lean_dec(v_stx_617_);
v___x_1257_ = l_Lean_Syntax_getArg(v___x_1188_, v___x_623_);
v___x_1258_ = l_Lean_Syntax_isNone(v___x_1257_);
if (v___x_1258_ == 0)
{
uint8_t v___x_1259_; 
lean_inc(v___x_1257_);
v___x_1259_ = l_Lean_Syntax_matchesNull(v___x_1257_, v___x_1140_);
if (v___x_1259_ == 0)
{
lean_object* v___x_1260_; 
lean_dec(v___x_1257_);
lean_dec(v_body_1192_);
lean_dec(v___x_1188_);
lean_dec_ref(v_decls_1143_);
v___x_1260_ = l_Lean_Macro_throwUnsupported___redArg(v_a_619_);
return v___x_1260_;
}
else
{
lean_object* v_h_x3f_1261_; lean_object* v___x_1262_; 
v_h_x3f_1261_ = l_Lean_Syntax_getArg(v___x_1257_, v___x_623_);
lean_dec(v___x_1257_);
v___x_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1262_, 0, v_h_x3f_1261_);
v_h_x3f_1194_ = v___x_1262_;
v___y_1195_ = v_a_618_;
v___y_1196_ = v_a_619_;
goto v___jp_1193_;
}
}
else
{
lean_object* v___x_1263_; 
lean_dec(v___x_1257_);
v___x_1263_ = lean_box(0);
v_h_x3f_1194_ = v___x_1263_;
v___y_1195_ = v_a_618_;
v___y_1196_ = v_a_619_;
goto v___jp_1193_;
}
v___jp_1193_:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v_doElems_1199_; uint8_t v___x_1200_; 
v___x_1197_ = l_Lean_Syntax_getArg(v___x_1188_, v___x_624_);
v___x_1198_ = l_Lean_Syntax_getArg(v___x_1188_, v___x_1191_);
lean_dec(v___x_1188_);
v_doElems_1199_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_1200_ = l_Lean_Syntax_isIdent(v___x_1197_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; uint8_t v___x_1202_; 
v___x_1201_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_1197_);
v___x_1202_ = l_Lean_Syntax_isOfKind(v___x_1197_, v___x_1201_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1197_, v___x_1202_, v___y_1195_, v___y_1196_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_a_1204_; lean_object* v_a_1205_; lean_object* v_ref_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
lean_inc_n(v_a_1204_, 2);
v_a_1205_ = lean_ctor_get(v___x_1203_, 1);
lean_inc(v_a_1205_);
lean_dec_ref(v___x_1203_);
v_ref_1206_ = lean_ctor_get(v___y_1195_, 5);
v___x_1207_ = l_Lean_SourceInfo_fromRef(v_ref_1206_, v___x_1202_);
v___x_1208_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_1209_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1210_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_1211_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_1212_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_n(v___x_1207_, 15);
v___x_1213_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1207_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
v___x_1214_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_1215_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1207_);
lean_ctor_set(v___x_1215_, 1, v___x_1209_);
lean_ctor_set(v___x_1215_, 2, v___x_1214_);
v___x_1216_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_1215_, 4);
v___x_1217_ = l_Lean_Syntax_node2(v___x_1207_, v___x_1216_, v___x_1215_, v_a_1204_);
v___x_1218_ = l_Lean_Syntax_node1(v___x_1207_, v___x_1209_, v___x_1217_);
v___x_1219_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_1220_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1207_);
lean_ctor_set(v___x_1220_, 1, v___x_1219_);
v___x_1221_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_1222_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_1223_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_1224_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1207_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v___x_1225_ = l_Lean_Syntax_node1(v___x_1207_, v___x_1209_, v___x_1197_);
v___x_1226_ = l_Lean_Syntax_node1(v___x_1207_, v___x_1209_, v___x_1225_);
v___x_1227_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_1228_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1207_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
v___x_1229_ = l_Lean_Syntax_node4(v___x_1207_, v___x_1222_, v___x_1224_, v___x_1226_, v___x_1228_, v_body_1192_);
v___x_1230_ = l_Lean_Syntax_node1(v___x_1207_, v___x_1209_, v___x_1229_);
v___x_1231_ = l_Lean_Syntax_node1(v___x_1207_, v___x_1221_, v___x_1230_);
v___x_1232_ = l_Lean_Syntax_node7(v___x_1207_, v___x_1211_, v___x_1213_, v___x_1215_, v___x_1215_, v___x_1215_, v___x_1218_, v___x_1220_, v___x_1231_);
v___x_1233_ = l_Lean_Syntax_node2(v___x_1207_, v___x_1210_, v___x_1232_, v___x_1215_);
v___x_1234_ = l_Lean_Syntax_node1(v___x_1207_, v___x_1209_, v___x_1233_);
v___x_1235_ = l_Lean_Syntax_node1(v___x_1207_, v___x_1208_, v___x_1234_);
v___y_1145_ = v_h_x3f_1194_;
v___y_1146_ = v___x_1198_;
v___y_1147_ = v_doElems_1199_;
v_x_1148_ = v_a_1204_;
v_body_1149_ = v___x_1235_;
v___y_1150_ = v___y_1195_;
v___y_1151_ = v_a_1205_;
goto v___jp_1144_;
}
else
{
lean_object* v_a_1236_; lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
lean_dec(v___x_1198_);
lean_dec(v___x_1197_);
lean_dec(v_h_x3f_1194_);
lean_dec(v_body_1192_);
lean_dec_ref(v_decls_1143_);
v_a_1236_ = lean_ctor_get(v___x_1203_, 0);
v_a_1237_ = lean_ctor_get(v___x_1203_, 1);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1203_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_inc(v_a_1236_);
lean_dec(v___x_1203_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1236_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_a_1237_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
else
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1197_, v___x_1200_, v___y_1195_, v___y_1196_);
lean_dec(v___x_1197_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; lean_object* v_a_1247_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_a_1246_);
v_a_1247_ = lean_ctor_get(v___x_1245_, 1);
lean_inc(v_a_1247_);
lean_dec_ref(v___x_1245_);
v___y_1145_ = v_h_x3f_1194_;
v___y_1146_ = v___x_1198_;
v___y_1147_ = v_doElems_1199_;
v_x_1148_ = v_a_1246_;
v_body_1149_ = v_body_1192_;
v___y_1150_ = v___y_1195_;
v___y_1151_ = v_a_1247_;
goto v___jp_1144_;
}
else
{
lean_object* v_a_1248_; lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
lean_dec(v___x_1198_);
lean_dec(v_h_x3f_1194_);
lean_dec(v_body_1192_);
lean_dec_ref(v_decls_1143_);
v_a_1248_ = lean_ctor_get(v___x_1245_, 0);
v_a_1249_ = lean_ctor_get(v___x_1245_, 1);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v___x_1245_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_inc(v_a_1248_);
lean_dec(v___x_1245_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1248_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v_a_1249_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
}
else
{
v___y_1145_ = v_h_x3f_1194_;
v___y_1146_ = v___x_1198_;
v___y_1147_ = v_doElems_1199_;
v_x_1148_ = v___x_1197_;
v_body_1149_ = v_body_1192_;
v___y_1150_ = v___y_1195_;
v___y_1151_ = v___y_1196_;
goto v___jp_1144_;
}
}
}
v___jp_1144_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1152_ = lean_array_get_size(v_decls_1143_);
v___x_1153_ = l_Array_toSubarray___redArg(v_decls_1143_, v___x_624_, v___x_1152_);
lean_inc_ref(v___y_1147_);
v___x_1154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___y_1147_);
lean_ctor_set(v___x_1154_, 1, v_body_1149_);
v___x_1155_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_1141_, v___x_1153_, v___x_1154_, v___y_1150_, v___y_1151_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_a_1156_; lean_object* v_a_1157_; lean_object* v_fst_1158_; lean_object* v_snd_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1177_; 
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_a_1156_);
v_a_1157_ = lean_ctor_get(v___x_1155_, 1);
lean_inc(v_a_1157_);
lean_dec_ref(v___x_1155_);
v_fst_1158_ = lean_ctor_get(v_a_1156_, 0);
v_snd_1159_ = lean_ctor_get(v_a_1156_, 1);
v_isSharedCheck_1177_ = !lean_is_exclusive(v_a_1156_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1161_ = v_a_1156_;
v_isShared_1162_ = v_isSharedCheck_1177_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_snd_1159_);
lean_inc(v_fst_1158_);
lean_dec(v_a_1156_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1177_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v_ref_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1168_; 
v_ref_1163_ = lean_ctor_get(v___y_1150_, 5);
v___x_1164_ = l_Lean_SourceInfo_fromRef(v_ref_1163_, v___x_1141_);
v___x_1165_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_1166_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
lean_inc(v___x_1164_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set_tag(v___x_1161_, 2);
lean_ctor_set(v___x_1161_, 1, v___x_1166_);
lean_ctor_set(v___x_1161_, 0, v___x_1164_);
v___x_1168_ = v___x_1161_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1164_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1170_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
if (lean_obj_tag(v___y_1145_) == 1)
{
lean_object* v_val_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v_val_1171_ = lean_ctor_get(v___y_1145_, 0);
lean_inc(v_val_1171_);
lean_dec_ref(v___y_1145_);
v___x_1172_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
lean_inc(v___x_1164_);
v___x_1173_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1164_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
v___x_1174_ = l_Array_mkArray2___redArg(v_val_1171_, v___x_1173_);
v___y_785_ = v___y_1146_;
v___y_786_ = v___x_1169_;
v___y_787_ = v_snd_1159_;
v___y_788_ = v___x_1164_;
v___y_789_ = v___x_1165_;
v___y_790_ = v___x_1170_;
v___y_791_ = v_x_1148_;
v___y_792_ = v_a_1157_;
v___y_793_ = v_fst_1158_;
v___y_794_ = v___x_1168_;
v___y_795_ = v___x_1174_;
goto v___jp_784_;
}
else
{
lean_object* v___x_1175_; 
lean_dec(v___y_1145_);
v___x_1175_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
v___y_785_ = v___y_1146_;
v___y_786_ = v___x_1169_;
v___y_787_ = v_snd_1159_;
v___y_788_ = v___x_1164_;
v___y_789_ = v___x_1165_;
v___y_790_ = v___x_1170_;
v___y_791_ = v_x_1148_;
v___y_792_ = v_a_1157_;
v___y_793_ = v_fst_1158_;
v___y_794_ = v___x_1168_;
v___y_795_ = v___x_1175_;
goto v___jp_784_;
}
}
}
}
else
{
lean_object* v_a_1178_; lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
lean_dec(v_x_1148_);
lean_dec(v___y_1146_);
lean_dec(v___y_1145_);
v_a_1178_ = lean_ctor_get(v___x_1155_, 0);
v_a_1179_ = lean_ctor_get(v___x_1155_, 1);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_1155_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_inc(v_a_1178_);
lean_dec(v___x_1155_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1178_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
}
else
{
v___y_961_ = v_a_618_;
v___y_962_ = v_a_619_;
goto v___jp_960_;
}
}
else
{
lean_dec(v___x_1138_);
v___y_961_ = v_a_618_;
v___y_962_ = v_a_619_;
goto v___jp_960_;
}
}
v___jp_784_:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
lean_inc_ref_n(v___y_790_, 3);
v___x_796_ = l_Array_append___redArg(v___y_790_, v___y_795_);
lean_dec_ref(v___y_795_);
lean_inc_n(v___y_786_, 4);
lean_inc_n(v___y_788_, 10);
v___x_797_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_797_, 0, v___y_788_);
lean_ctor_set(v___x_797_, 1, v___y_786_);
lean_ctor_set(v___x_797_, 2, v___x_796_);
v___x_798_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_799_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_799_, 0, v___y_788_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
v___x_800_ = l_Lean_Syntax_node4(v___y_788_, v___x_783_, v___x_797_, v___y_791_, v___x_799_, v___y_785_);
v___x_801_ = l_Lean_Syntax_node1(v___y_788_, v___y_786_, v___x_800_);
v___x_802_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_803_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_803_, 0, v___y_788_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
lean_inc_ref(v___x_803_);
v___x_804_ = l_Lean_Syntax_node4(v___y_788_, v___x_620_, v___y_794_, v___x_801_, v___x_803_, v___y_787_);
v___x_805_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_805_, 0, v___y_788_);
lean_ctor_set(v___x_805_, 1, v___y_786_);
lean_ctor_set(v___x_805_, 2, v___y_790_);
lean_inc(v___y_789_);
v___x_806_ = l_Lean_Syntax_node2(v___y_788_, v___y_789_, v___x_804_, v___x_805_);
v___x_807_ = lean_array_push(v___y_793_, v___x_806_);
v___x_808_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_809_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_810_ = l_Array_append___redArg(v___y_790_, v___x_807_);
lean_dec_ref(v___x_807_);
v___x_811_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_811_, 0, v___y_788_);
lean_ctor_set(v___x_811_, 1, v___y_786_);
lean_ctor_set(v___x_811_, 2, v___x_810_);
v___x_812_ = l_Lean_Syntax_node1(v___y_788_, v___x_809_, v___x_811_);
v___x_813_ = l_Lean_Syntax_node2(v___y_788_, v___x_808_, v___x_803_, v___x_812_);
v___x_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
lean_ctor_set(v___x_814_, 1, v___y_792_);
return v___x_814_;
}
v___jp_815_:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
lean_inc_ref_n(v___y_822_, 3);
v___x_827_ = l_Array_append___redArg(v___y_822_, v___y_826_);
lean_dec_ref(v___y_826_);
lean_inc_n(v___y_816_, 4);
lean_inc_n(v___y_817_, 10);
v___x_828_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_828_, 0, v___y_817_);
lean_ctor_set(v___x_828_, 1, v___y_816_);
lean_ctor_set(v___x_828_, 2, v___x_827_);
v___x_829_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_830_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_830_, 0, v___y_817_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
v___x_831_ = l_Lean_Syntax_node4(v___y_817_, v___x_783_, v___x_828_, v___y_820_, v___x_830_, v___y_823_);
v___x_832_ = l_Lean_Syntax_node1(v___y_817_, v___y_816_, v___x_831_);
v___x_833_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_834_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_834_, 0, v___y_817_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
lean_inc_ref(v___x_834_);
v___x_835_ = l_Lean_Syntax_node4(v___y_817_, v___x_620_, v___y_825_, v___x_832_, v___x_834_, v___y_824_);
v___x_836_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_836_, 0, v___y_817_);
lean_ctor_set(v___x_836_, 1, v___y_816_);
lean_ctor_set(v___x_836_, 2, v___y_822_);
lean_inc(v___y_818_);
v___x_837_ = l_Lean_Syntax_node2(v___y_817_, v___y_818_, v___x_835_, v___x_836_);
v___x_838_ = lean_array_push(v___y_821_, v___x_837_);
v___x_839_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_840_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_841_ = l_Array_append___redArg(v___y_822_, v___x_838_);
lean_dec_ref(v___x_838_);
v___x_842_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_842_, 0, v___y_817_);
lean_ctor_set(v___x_842_, 1, v___y_816_);
lean_ctor_set(v___x_842_, 2, v___x_841_);
v___x_843_ = l_Lean_Syntax_node1(v___y_817_, v___x_840_, v___x_842_);
v___x_844_ = l_Lean_Syntax_node2(v___y_817_, v___x_839_, v___x_834_, v___x_843_);
v___x_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
lean_ctor_set(v___x_845_, 1, v___y_819_);
return v___x_845_;
}
v___jp_846_:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_856_ = lean_array_get_size(v___y_850_);
v___x_857_ = l_Array_toSubarray___redArg(v___y_850_, v___x_624_, v___x_856_);
lean_inc_ref(v___y_849_);
v___x_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_858_, 0, v___y_849_);
lean_ctor_set(v___x_858_, 1, v_body_853_);
v___x_859_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___y_847_, v___x_857_, v___x_858_, v___y_854_, v___y_855_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v_a_861_; lean_object* v_fst_862_; lean_object* v_snd_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_881_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_860_);
v_a_861_ = lean_ctor_get(v___x_859_, 1);
lean_inc(v_a_861_);
lean_dec_ref(v___x_859_);
v_fst_862_ = lean_ctor_get(v_a_860_, 0);
v_snd_863_ = lean_ctor_get(v_a_860_, 1);
v_isSharedCheck_881_ = !lean_is_exclusive(v_a_860_);
if (v_isSharedCheck_881_ == 0)
{
v___x_865_ = v_a_860_;
v_isShared_866_ = v_isSharedCheck_881_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_snd_863_);
lean_inc(v_fst_862_);
lean_dec(v_a_860_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_881_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v_ref_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_872_; 
v_ref_867_ = lean_ctor_get(v___y_854_, 5);
v___x_868_ = l_Lean_SourceInfo_fromRef(v_ref_867_, v___y_847_);
v___x_869_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_870_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
lean_inc(v___x_868_);
if (v_isShared_866_ == 0)
{
lean_ctor_set_tag(v___x_865_, 2);
lean_ctor_set(v___x_865_, 1, v___x_870_);
lean_ctor_set(v___x_865_, 0, v___x_868_);
v___x_872_ = v___x_865_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_868_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v___x_870_);
v___x_872_ = v_reuseFailAlloc_880_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_874_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
if (lean_obj_tag(v___y_848_) == 1)
{
lean_object* v_val_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v_val_875_ = lean_ctor_get(v___y_848_, 0);
lean_inc(v_val_875_);
lean_dec_ref(v___y_848_);
v___x_876_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
lean_inc(v___x_868_);
v___x_877_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_868_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = l_Array_mkArray2___redArg(v_val_875_, v___x_877_);
v___y_816_ = v___x_873_;
v___y_817_ = v___x_868_;
v___y_818_ = v___x_869_;
v___y_819_ = v_a_861_;
v___y_820_ = v_x_852_;
v___y_821_ = v_fst_862_;
v___y_822_ = v___x_874_;
v___y_823_ = v___y_851_;
v___y_824_ = v_snd_863_;
v___y_825_ = v___x_872_;
v___y_826_ = v___x_878_;
goto v___jp_815_;
}
else
{
lean_object* v___x_879_; 
lean_dec(v___y_848_);
v___x_879_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
v___y_816_ = v___x_873_;
v___y_817_ = v___x_868_;
v___y_818_ = v___x_869_;
v___y_819_ = v_a_861_;
v___y_820_ = v_x_852_;
v___y_821_ = v_fst_862_;
v___y_822_ = v___x_874_;
v___y_823_ = v___y_851_;
v___y_824_ = v_snd_863_;
v___y_825_ = v___x_872_;
v___y_826_ = v___x_879_;
goto v___jp_815_;
}
}
}
}
else
{
lean_object* v_a_882_; lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
lean_dec(v_x_852_);
lean_dec(v___y_851_);
lean_dec(v___y_848_);
v_a_882_ = lean_ctor_get(v___x_859_, 0);
v_a_883_ = lean_ctor_get(v___x_859_, 1);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_859_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_inc(v_a_882_);
lean_dec(v___x_859_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_882_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
v___jp_891_:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v_doElems_902_; uint8_t v___x_903_; 
v___x_900_ = l_Lean_Syntax_getArg(v___y_893_, v___x_624_);
v___x_901_ = l_Lean_Syntax_getArg(v___y_893_, v___y_894_);
lean_dec(v___y_893_);
v_doElems_902_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_903_ = l_Lean_Syntax_isIdent(v___x_900_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_904_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_900_);
v___x_905_ = l_Lean_Syntax_isOfKind(v___x_900_, v___x_904_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; 
v___x_906_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_900_, v___y_892_, v___y_898_, v___y_899_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_a_907_; lean_object* v_a_908_; lean_object* v_ref_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v_a_907_ = lean_ctor_get(v___x_906_, 0);
lean_inc_n(v_a_907_, 2);
v_a_908_ = lean_ctor_get(v___x_906_, 1);
lean_inc(v_a_908_);
lean_dec_ref(v___x_906_);
v_ref_909_ = lean_ctor_get(v___y_898_, 5);
v___x_910_ = l_Lean_SourceInfo_fromRef(v_ref_909_, v___y_892_);
v___x_911_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_912_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_913_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_914_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_915_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_n(v___x_910_, 15);
v___x_916_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_910_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_918_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_918_, 0, v___x_910_);
lean_ctor_set(v___x_918_, 1, v___x_912_);
lean_ctor_set(v___x_918_, 2, v___x_917_);
v___x_919_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_918_, 4);
v___x_920_ = l_Lean_Syntax_node2(v___x_910_, v___x_919_, v___x_918_, v_a_907_);
v___x_921_ = l_Lean_Syntax_node1(v___x_910_, v___x_912_, v___x_920_);
v___x_922_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_923_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_910_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
v___x_924_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_925_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_926_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_927_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_910_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = l_Lean_Syntax_node1(v___x_910_, v___x_912_, v___x_900_);
v___x_929_ = l_Lean_Syntax_node1(v___x_910_, v___x_912_, v___x_928_);
v___x_930_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_931_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_910_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = l_Lean_Syntax_node4(v___x_910_, v___x_925_, v___x_927_, v___x_929_, v___x_931_, v___y_895_);
v___x_933_ = l_Lean_Syntax_node1(v___x_910_, v___x_912_, v___x_932_);
v___x_934_ = l_Lean_Syntax_node1(v___x_910_, v___x_924_, v___x_933_);
v___x_935_ = l_Lean_Syntax_node7(v___x_910_, v___x_914_, v___x_916_, v___x_918_, v___x_918_, v___x_918_, v___x_921_, v___x_923_, v___x_934_);
v___x_936_ = l_Lean_Syntax_node2(v___x_910_, v___x_913_, v___x_935_, v___x_918_);
v___x_937_ = l_Lean_Syntax_node1(v___x_910_, v___x_912_, v___x_936_);
v___x_938_ = l_Lean_Syntax_node1(v___x_910_, v___x_911_, v___x_937_);
v___y_847_ = v___y_892_;
v___y_848_ = v_h_x3f_897_;
v___y_849_ = v_doElems_902_;
v___y_850_ = v___y_896_;
v___y_851_ = v___x_901_;
v_x_852_ = v_a_907_;
v_body_853_ = v___x_938_;
v___y_854_ = v___y_898_;
v___y_855_ = v_a_908_;
goto v___jp_846_;
}
else
{
lean_object* v_a_939_; lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec(v___x_901_);
lean_dec(v___x_900_);
lean_dec(v_h_x3f_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
v_a_939_ = lean_ctor_get(v___x_906_, 0);
v_a_940_ = lean_ctor_get(v___x_906_, 1);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_906_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_inc(v_a_939_);
lean_dec(v___x_906_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_939_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
else
{
lean_object* v___x_948_; 
v___x_948_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_900_, v___y_892_, v___y_898_, v___y_899_);
lean_dec(v___x_900_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v_a_950_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_a_949_);
v_a_950_ = lean_ctor_get(v___x_948_, 1);
lean_inc(v_a_950_);
lean_dec_ref(v___x_948_);
v___y_847_ = v___y_892_;
v___y_848_ = v_h_x3f_897_;
v___y_849_ = v_doElems_902_;
v___y_850_ = v___y_896_;
v___y_851_ = v___x_901_;
v_x_852_ = v_a_949_;
v_body_853_ = v___y_895_;
v___y_854_ = v___y_898_;
v___y_855_ = v_a_950_;
goto v___jp_846_;
}
else
{
lean_object* v_a_951_; lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
lean_dec(v___x_901_);
lean_dec(v_h_x3f_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
v_a_951_ = lean_ctor_get(v___x_948_, 0);
v_a_952_ = lean_ctor_get(v___x_948_, 1);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_948_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_inc(v_a_951_);
lean_dec(v___x_948_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_951_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_a_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
else
{
v___y_847_ = v___y_892_;
v___y_848_ = v_h_x3f_897_;
v___y_849_ = v_doElems_902_;
v___y_850_ = v___y_896_;
v___y_851_ = v___x_901_;
v_x_852_ = v___x_900_;
v_body_853_ = v___y_895_;
v___y_854_ = v___y_898_;
v___y_855_ = v___y_899_;
goto v___jp_846_;
}
}
v___jp_960_:
{
lean_object* v___x_963_; lean_object* v___x_964_; uint8_t v___x_965_; 
v___x_963_ = l_Lean_Syntax_getArg(v___x_782_, v___x_624_);
lean_dec(v___x_782_);
v___x_964_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__16));
v___x_965_ = l_Lean_Syntax_isOfKind(v___x_963_, v___x_964_);
if (v___x_965_ == 0)
{
lean_object* v_decls_966_; lean_object* v_decls_967_; lean_object* v___x_968_; lean_object* v___x_969_; uint8_t v___x_970_; 
v_decls_966_ = l_Lean_Syntax_getArgs(v___x_625_);
lean_dec(v___x_625_);
v_decls_967_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_966_);
lean_dec_ref(v_decls_966_);
v___x_968_ = lean_box(0);
v___x_969_ = lean_array_get(v___x_968_, v_decls_967_, v___x_623_);
lean_inc(v___x_969_);
v___x_970_ = l_Lean_Syntax_isOfKind(v___x_969_, v___x_783_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; 
lean_dec(v___x_969_);
lean_dec_ref(v_decls_967_);
lean_dec(v_stx_617_);
v___x_971_ = l_Lean_Macro_throwUnsupported___redArg(v___y_962_);
return v___x_971_;
}
else
{
lean_object* v___x_972_; lean_object* v_body_973_; lean_object* v___x_974_; uint8_t v___x_975_; 
v___x_972_ = lean_unsigned_to_nat(3u);
v_body_973_ = l_Lean_Syntax_getArg(v_stx_617_, v___x_972_);
lean_dec(v_stx_617_);
v___x_974_ = l_Lean_Syntax_getArg(v___x_969_, v___x_623_);
v___x_975_ = l_Lean_Syntax_isNone(v___x_974_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; uint8_t v___x_977_; 
v___x_976_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_974_);
v___x_977_ = l_Lean_Syntax_matchesNull(v___x_974_, v___x_976_);
if (v___x_977_ == 0)
{
lean_object* v___x_978_; 
lean_dec(v___x_974_);
lean_dec(v_body_973_);
lean_dec(v___x_969_);
lean_dec_ref(v_decls_967_);
v___x_978_ = l_Lean_Macro_throwUnsupported___redArg(v___y_962_);
return v___x_978_;
}
else
{
lean_object* v_h_x3f_979_; lean_object* v___x_980_; 
v_h_x3f_979_ = l_Lean_Syntax_getArg(v___x_974_, v___x_623_);
lean_dec(v___x_974_);
v___x_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_980_, 0, v_h_x3f_979_);
v___y_892_ = v___x_965_;
v___y_893_ = v___x_969_;
v___y_894_ = v___x_972_;
v___y_895_ = v_body_973_;
v___y_896_ = v_decls_967_;
v_h_x3f_897_ = v___x_980_;
v___y_898_ = v___y_961_;
v___y_899_ = v___y_962_;
goto v___jp_891_;
}
}
else
{
lean_object* v___x_981_; 
lean_dec(v___x_974_);
v___x_981_ = lean_box(0);
v___y_892_ = v___x_965_;
v___y_893_ = v___x_969_;
v___y_894_ = v___x_972_;
v___y_895_ = v_body_973_;
v___y_896_ = v_decls_967_;
v_h_x3f_897_ = v___x_981_;
v___y_898_ = v___y_961_;
v___y_899_ = v___y_962_;
goto v___jp_891_;
}
}
}
else
{
lean_object* v___x_982_; 
lean_dec(v___x_625_);
lean_dec(v_stx_617_);
v___x_982_ = l_Lean_Macro_throwUnsupported___redArg(v___y_962_);
return v___x_982_;
}
}
v___jp_983_:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
lean_inc_ref_n(v___y_987_, 3);
v___x_995_ = l_Array_append___redArg(v___y_987_, v___y_994_);
lean_dec_ref(v___y_994_);
lean_inc_n(v___y_991_, 4);
lean_inc_n(v___y_984_, 10);
v___x_996_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_996_, 0, v___y_984_);
lean_ctor_set(v___x_996_, 1, v___y_991_);
lean_ctor_set(v___x_996_, 2, v___x_995_);
v___x_997_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_998_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_998_, 0, v___y_984_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v___x_999_ = l_Lean_Syntax_node4(v___y_984_, v___x_783_, v___x_996_, v___y_986_, v___x_998_, v___y_993_);
v___x_1000_ = l_Lean_Syntax_node1(v___y_984_, v___y_991_, v___x_999_);
v___x_1001_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_1002_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___y_984_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
lean_inc_ref(v___x_1002_);
v___x_1003_ = l_Lean_Syntax_node4(v___y_984_, v___x_620_, v___y_985_, v___x_1000_, v___x_1002_, v___y_990_);
v___x_1004_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1004_, 0, v___y_984_);
lean_ctor_set(v___x_1004_, 1, v___y_991_);
lean_ctor_set(v___x_1004_, 2, v___y_987_);
lean_inc(v___y_989_);
v___x_1005_ = l_Lean_Syntax_node2(v___y_984_, v___y_989_, v___x_1003_, v___x_1004_);
v___x_1006_ = lean_array_push(v___y_988_, v___x_1005_);
v___x_1007_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_1008_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_1009_ = l_Array_append___redArg(v___y_987_, v___x_1006_);
lean_dec_ref(v___x_1006_);
v___x_1010_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1010_, 0, v___y_984_);
lean_ctor_set(v___x_1010_, 1, v___y_991_);
lean_ctor_set(v___x_1010_, 2, v___x_1009_);
v___x_1011_ = l_Lean_Syntax_node1(v___y_984_, v___x_1008_, v___x_1010_);
v___x_1012_ = l_Lean_Syntax_node2(v___y_984_, v___x_1007_, v___x_1002_, v___x_1011_);
v___x_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
lean_ctor_set(v___x_1013_, 1, v___y_992_);
return v___x_1013_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor___boxed(lean_object* v_stx_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_Elab_Do_expandDoFor(v_stx_1264_, v_a_1265_, v_a_1266_);
lean_dec_ref(v_a_1265_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0(uint8_t v___x_1268_, lean_object* v_inst_1269_, lean_object* v_R_1270_, lean_object* v_a_1271_, lean_object* v_b_1272_, lean_object* v_c_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_1268_, v_a_1271_, v_b_1272_, v___y_1274_, v___y_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___boxed(lean_object* v___x_1277_, lean_object* v_inst_1278_, lean_object* v_R_1279_, lean_object* v_a_1280_, lean_object* v_b_1281_, lean_object* v_c_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
uint8_t v___x_148450__boxed_1285_; lean_object* v_res_1286_; 
v___x_148450__boxed_1285_ = lean_unbox(v___x_1277_);
v_res_1286_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0(v___x_148450__boxed_1285_, v_inst_1278_, v_R_1279_, v_a_1280_, v_b_1281_, v_c_1282_, v___y_1283_, v___y_1284_);
lean_dec_ref(v___y_1283_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1(){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1294_ = l_Lean_Elab_macroAttribute;
v___x_1295_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
v___x_1296_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1));
v___x_1297_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_expandDoFor___boxed), 3, 0);
v___x_1298_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1294_, v___x_1295_, v___x_1296_, v___x_1297_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___boxed(lean_object* v_a_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1();
return v_res_1300_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1301_ = lean_box(0);
v___x_1302_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1302_);
lean_ctor_set(v___x_1303_, 1, v___x_1301_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg(){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0);
v___x_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___boxed(lean_object* v___y_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0(lean_object* v_00_u03b1_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v___x_1318_; 
v___x_1318_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___boxed(lean_object* v_00_u03b1_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0(v_00_u03b1_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec_ref(v___y_1320_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0(lean_object* v_k_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v_b_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
lean_object* v___x_1339_; 
lean_inc(v___y_1337_);
lean_inc_ref(v___y_1336_);
lean_inc(v___y_1335_);
lean_inc_ref(v___y_1334_);
lean_inc(v___y_1332_);
lean_inc_ref(v___y_1331_);
lean_inc_ref(v___y_1330_);
v___x_1339_ = lean_apply_9(v_k_1329_, v_b_1333_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, lean_box(0));
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0___boxed(lean_object* v_k_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v_b_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0(v_k_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v_b_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec_ref(v___y_1341_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(lean_object* v_name_1351_, uint8_t v_bi_1352_, lean_object* v_type_1353_, lean_object* v_k_1354_, uint8_t v_kind_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v___f_1364_; lean_object* v___x_1365_; 
lean_inc(v___y_1358_);
lean_inc_ref(v___y_1357_);
lean_inc_ref(v___y_1356_);
v___f_1364_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1364_, 0, v_k_1354_);
lean_closure_set(v___f_1364_, 1, v___y_1356_);
lean_closure_set(v___f_1364_, 2, v___y_1357_);
lean_closure_set(v___f_1364_, 3, v___y_1358_);
v___x_1365_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1351_, v_bi_1352_, v_type_1353_, v___f_1364_, v_kind_1355_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
if (lean_obj_tag(v___x_1365_) == 0)
{
return v___x_1365_;
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1365_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1365_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___boxed(lean_object* v_name_1374_, lean_object* v_bi_1375_, lean_object* v_type_1376_, lean_object* v_k_1377_, lean_object* v_kind_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
uint8_t v_bi_boxed_1387_; uint8_t v_kind_boxed_1388_; lean_object* v_res_1389_; 
v_bi_boxed_1387_ = lean_unbox(v_bi_1375_);
v_kind_boxed_1388_ = lean_unbox(v_kind_1378_);
v_res_1389_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_name_1374_, v_bi_boxed_1387_, v_type_1376_, v_k_1377_, v_kind_boxed_1388_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec_ref(v___y_1379_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3(lean_object* v_00_u03b1_1390_, lean_object* v_name_1391_, uint8_t v_bi_1392_, lean_object* v_type_1393_, lean_object* v_k_1394_, uint8_t v_kind_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v___x_1404_; 
v___x_1404_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_name_1391_, v_bi_1392_, v_type_1393_, v_k_1394_, v_kind_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___boxed(lean_object* v_00_u03b1_1405_, lean_object* v_name_1406_, lean_object* v_bi_1407_, lean_object* v_type_1408_, lean_object* v_k_1409_, lean_object* v_kind_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
uint8_t v_bi_boxed_1419_; uint8_t v_kind_boxed_1420_; lean_object* v_res_1421_; 
v_bi_boxed_1419_ = lean_unbox(v_bi_1407_);
v_kind_boxed_1420_ = lean_unbox(v_kind_1410_);
v_res_1421_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3(v_00_u03b1_1405_, v_name_1406_, v_bi_boxed_1419_, v_type_1408_, v_k_1409_, v_kind_boxed_1420_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec_ref(v___y_1411_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__0(lean_object* v_a_1422_, lean_object* v_x_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1432_, 0, v_a_1422_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__0___boxed(lean_object* v_a_1433_, lean_object* v_x_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_Elab_Do_elabDoFor___lam__0(v_a_1433_, v_x_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec_ref(v_x_1434_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__1(lean_object* v_x_1444_, lean_object* v___f_1445_, lean_object* v___x_1446_, lean_object* v_x_1447_, lean_object* v_x_1448_){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1449_ = l_Lean_TSyntax_getId(v_x_1444_);
v___x_1450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
lean_ctor_set(v___x_1450_, 1, v___f_1445_);
v___x_1451_ = lean_mk_empty_array_with_capacity(v___x_1446_);
v___x_1452_ = lean_array_push(v___x_1451_, v___x_1450_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__1___boxed(lean_object* v_x_1453_, lean_object* v___f_1454_, lean_object* v___x_1455_, lean_object* v_x_1456_, lean_object* v_x_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Lean_Elab_Do_elabDoFor___lam__1(v_x_1453_, v___f_1454_, v___x_1455_, v_x_1456_, v_x_1457_);
lean_dec(v_x_1457_);
lean_dec(v_x_1456_);
lean_dec(v___x_1455_);
lean_dec(v_x_1453_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__3(lean_object* v_a_1459_, lean_object* v___x_1460_, uint8_t v___x_1461_, lean_object* v_r_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v_k_1471_; lean_object* v___x_1472_; 
v_k_1471_ = lean_ctor_get(v_a_1459_, 1);
lean_inc_ref(v_k_1471_);
lean_dec_ref(v_a_1459_);
lean_inc(v___y_1469_);
lean_inc_ref(v___y_1468_);
lean_inc(v___y_1467_);
lean_inc_ref(v___y_1466_);
lean_inc(v___y_1465_);
lean_inc_ref(v___y_1464_);
lean_inc_ref(v___y_1463_);
lean_inc_ref(v_r_1462_);
v___x_1472_ = lean_apply_9(v_k_1471_, v_r_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, lean_box(0));
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; uint8_t v___x_1476_; uint8_t v___x_1477_; lean_object* v___x_1478_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1473_);
lean_dec_ref(v___x_1472_);
v___x_1474_ = lean_mk_empty_array_with_capacity(v___x_1460_);
v___x_1475_ = lean_array_push(v___x_1474_, v_r_1462_);
v___x_1476_ = 0;
v___x_1477_ = 1;
v___x_1478_ = l_Lean_Meta_mkLambdaFVars(v___x_1475_, v_a_1473_, v___x_1476_, v___x_1461_, v___x_1476_, v___x_1461_, v___x_1477_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
lean_dec_ref(v___x_1475_);
return v___x_1478_;
}
else
{
lean_dec_ref(v_r_1462_);
return v___x_1472_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___boxed(lean_object* v_a_1479_, lean_object* v___x_1480_, lean_object* v___x_1481_, lean_object* v_r_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
uint8_t v___x_81490__boxed_1491_; lean_object* v_res_1492_; 
v___x_81490__boxed_1491_ = lean_unbox(v___x_1481_);
v_res_1492_ = l_Lean_Elab_Do_elabDoFor___lam__3(v_a_1479_, v___x_1480_, v___x_81490__boxed_1491_, v_r_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___x_1480_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1(lean_object* v___x_1493_, lean_object* v_as_1494_, size_t v_sz_1495_, size_t v_i_1496_, lean_object* v_b_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
uint8_t v___x_1505_; 
v___x_1505_ = lean_usize_dec_lt(v_i_1496_, v_sz_1495_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; 
lean_dec_ref(v___x_1493_);
v___x_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1506_, 0, v_b_1497_);
return v___x_1506_;
}
else
{
lean_object* v_a_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v_a_1507_ = lean_array_uget_borrowed(v_as_1494_, v_i_1496_);
v___x_1508_ = l_Lean_TSyntax_getId(v_a_1507_);
v___x_1509_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_1508_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; uint8_t v___x_1514_; lean_object* v___x_1515_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc_n(v_a_1510_, 2);
lean_dec_ref(v___x_1509_);
v___x_1511_ = l_Lean_LocalDecl_toExpr(v_a_1510_);
v___x_1512_ = lean_box(0);
v___x_1513_ = lean_box(0);
v___x_1514_ = 0;
lean_inc_ref(v___x_1511_);
lean_inc(v_a_1507_);
v___x_1515_ = l_Lean_Elab_Term_addTermInfo_x27(v_a_1507_, v___x_1511_, v___x_1512_, v___x_1512_, v___x_1513_, v___x_1514_, v___x_1514_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
lean_dec_ref(v___x_1515_);
v___x_1516_ = l_Lean_LocalDecl_type(v_a_1510_);
lean_dec(v_a_1510_);
v___x_1517_ = l_Lean_Meta_getDecLevel(v___x_1516_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v_u_1519_; lean_object* v___x_1520_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref(v___x_1517_);
v_u_1519_ = lean_ctor_get(v___x_1493_, 1);
lean_inc(v_u_1519_);
v___x_1520_ = l_Lean_Meta_isLevelDefEq(v_a_1518_, v_u_1519_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v___x_1521_; size_t v___x_1522_; size_t v___x_1523_; 
lean_dec_ref(v___x_1520_);
v___x_1521_ = lean_array_push(v_b_1497_, v___x_1511_);
v___x_1522_ = ((size_t)1ULL);
v___x_1523_ = lean_usize_add(v_i_1496_, v___x_1522_);
v_i_1496_ = v___x_1523_;
v_b_1497_ = v___x_1521_;
goto _start;
}
else
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
lean_dec_ref(v___x_1511_);
lean_dec_ref(v_b_1497_);
lean_dec_ref(v___x_1493_);
v_a_1525_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1527_ = v___x_1520_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v___x_1520_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1525_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1540_; 
lean_dec_ref(v___x_1511_);
lean_dec_ref(v_b_1497_);
lean_dec_ref(v___x_1493_);
v_a_1533_ = lean_ctor_get(v___x_1517_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1535_ = v___x_1517_;
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1517_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1538_; 
if (v_isShared_1536_ == 0)
{
v___x_1538_ = v___x_1535_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1533_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
else
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
lean_dec_ref(v___x_1511_);
lean_dec(v_a_1510_);
lean_dec_ref(v_b_1497_);
lean_dec_ref(v___x_1493_);
v_a_1541_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1515_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1515_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
else
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
lean_dec_ref(v_b_1497_);
lean_dec_ref(v___x_1493_);
v_a_1549_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v___x_1509_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1509_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
if (v_isShared_1552_ == 0)
{
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1549_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1___boxed(lean_object* v___x_1557_, lean_object* v_as_1558_, lean_object* v_sz_1559_, lean_object* v_i_1560_, lean_object* v_b_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
size_t v_sz_boxed_1569_; size_t v_i_boxed_1570_; lean_object* v_res_1571_; 
v_sz_boxed_1569_ = lean_unbox_usize(v_sz_1559_);
lean_dec(v_sz_1559_);
v_i_boxed_1570_ = lean_unbox_usize(v_i_1560_);
lean_dec(v_i_1560_);
v_res_1571_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1(v___x_1557_, v_as_1558_, v_sz_boxed_1569_, v_i_boxed_1570_, v_b_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec_ref(v_as_1558_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(lean_object* v_msgData_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v___x_1578_; lean_object* v_env_1579_; lean_object* v___x_1580_; lean_object* v_mctx_1581_; lean_object* v_lctx_1582_; lean_object* v_options_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1578_ = lean_st_ref_get(v___y_1576_);
v_env_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc_ref(v_env_1579_);
lean_dec(v___x_1578_);
v___x_1580_ = lean_st_ref_get(v___y_1574_);
v_mctx_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc_ref(v_mctx_1581_);
lean_dec(v___x_1580_);
v_lctx_1582_ = lean_ctor_get(v___y_1573_, 2);
v_options_1583_ = lean_ctor_get(v___y_1575_, 2);
lean_inc_ref(v_options_1583_);
lean_inc_ref(v_lctx_1582_);
v___x_1584_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1584_, 0, v_env_1579_);
lean_ctor_set(v___x_1584_, 1, v_mctx_1581_);
lean_ctor_set(v___x_1584_, 2, v_lctx_1582_);
lean_ctor_set(v___x_1584_, 3, v_options_1583_);
v___x_1585_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
lean_ctor_set(v___x_1585_, 1, v_msgData_1572_);
v___x_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2___boxed(lean_object* v_msgData_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(v_msgData_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
return v_res_1593_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0(void){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = lean_box(1);
v___x_1595_ = l_Lean_MessageData_ofFormat(v___x_1594_);
return v___x_1595_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3(void){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1599_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__2));
v___x_1600_ = l_Lean_MessageData_ofFormat(v___x_1599_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6(lean_object* v_x_1601_, lean_object* v_x_1602_){
_start:
{
if (lean_obj_tag(v_x_1602_) == 0)
{
return v_x_1601_;
}
else
{
lean_object* v_head_1603_; lean_object* v_tail_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1626_; 
v_head_1603_ = lean_ctor_get(v_x_1602_, 0);
v_tail_1604_ = lean_ctor_get(v_x_1602_, 1);
v_isSharedCheck_1626_ = !lean_is_exclusive(v_x_1602_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1606_ = v_x_1602_;
v_isShared_1607_ = v_isSharedCheck_1626_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_tail_1604_);
lean_inc(v_head_1603_);
lean_dec(v_x_1602_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1626_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v_before_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1624_; 
v_before_1608_ = lean_ctor_get(v_head_1603_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v_head_1603_);
if (v_isSharedCheck_1624_ == 0)
{
lean_object* v_unused_1625_; 
v_unused_1625_ = lean_ctor_get(v_head_1603_, 1);
lean_dec(v_unused_1625_);
v___x_1610_ = v_head_1603_;
v_isShared_1611_ = v_isSharedCheck_1624_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_before_1608_);
lean_dec(v_head_1603_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1624_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1612_; lean_object* v___x_1614_; 
v___x_1612_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0);
if (v_isShared_1611_ == 0)
{
lean_ctor_set_tag(v___x_1610_, 7);
lean_ctor_set(v___x_1610_, 1, v___x_1612_);
lean_ctor_set(v___x_1610_, 0, v_x_1601_);
v___x_1614_ = v___x_1610_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_x_1601_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v___x_1612_);
v___x_1614_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
lean_object* v___x_1615_; lean_object* v___x_1617_; 
v___x_1615_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3);
if (v_isShared_1607_ == 0)
{
lean_ctor_set_tag(v___x_1606_, 7);
lean_ctor_set(v___x_1606_, 1, v___x_1615_);
lean_ctor_set(v___x_1606_, 0, v___x_1614_);
v___x_1617_ = v___x_1606_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1614_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v___x_1615_);
v___x_1617_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1618_ = l_Lean_MessageData_ofSyntax(v_before_1608_);
v___x_1619_ = l_Lean_indentD(v___x_1618_);
v___x_1620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1617_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
v_x_1601_ = v___x_1620_;
v_x_1602_ = v_tail_1604_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5(lean_object* v_opts_1627_, lean_object* v_opt_1628_){
_start:
{
lean_object* v_name_1629_; lean_object* v_defValue_1630_; lean_object* v_map_1631_; lean_object* v___x_1632_; 
v_name_1629_ = lean_ctor_get(v_opt_1628_, 0);
v_defValue_1630_ = lean_ctor_get(v_opt_1628_, 1);
v_map_1631_ = lean_ctor_get(v_opts_1627_, 0);
v___x_1632_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1631_, v_name_1629_);
if (lean_obj_tag(v___x_1632_) == 0)
{
uint8_t v___x_1633_; 
v___x_1633_ = lean_unbox(v_defValue_1630_);
return v___x_1633_;
}
else
{
lean_object* v_val_1634_; 
v_val_1634_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_val_1634_);
lean_dec_ref(v___x_1632_);
if (lean_obj_tag(v_val_1634_) == 1)
{
uint8_t v_v_1635_; 
v_v_1635_ = lean_ctor_get_uint8(v_val_1634_, 0);
lean_dec_ref(v_val_1634_);
return v_v_1635_;
}
else
{
uint8_t v___x_1636_; 
lean_dec(v_val_1634_);
v___x_1636_ = lean_unbox(v_defValue_1630_);
return v___x_1636_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5___boxed(lean_object* v_opts_1637_, lean_object* v_opt_1638_){
_start:
{
uint8_t v_res_1639_; lean_object* v_r_1640_; 
v_res_1639_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5(v_opts_1637_, v_opt_1638_);
lean_dec_ref(v_opt_1638_);
lean_dec_ref(v_opts_1637_);
v_r_1640_ = lean_box(v_res_1639_);
return v_r_1640_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1644_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__1));
v___x_1645_ = l_Lean_MessageData_ofFormat(v___x_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(lean_object* v_msgData_1646_, lean_object* v_macroStack_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v_options_1650_; lean_object* v___x_1651_; uint8_t v___x_1652_; 
v_options_1650_ = lean_ctor_get(v___y_1648_, 2);
v___x_1651_ = l_Lean_Elab_pp_macroStack;
v___x_1652_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5(v_options_1650_, v___x_1651_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; 
lean_dec(v_macroStack_1647_);
v___x_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1653_, 0, v_msgData_1646_);
return v___x_1653_;
}
else
{
if (lean_obj_tag(v_macroStack_1647_) == 0)
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1654_, 0, v_msgData_1646_);
return v___x_1654_;
}
else
{
lean_object* v_head_1655_; lean_object* v_after_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1671_; 
v_head_1655_ = lean_ctor_get(v_macroStack_1647_, 0);
lean_inc(v_head_1655_);
v_after_1656_ = lean_ctor_get(v_head_1655_, 1);
v_isSharedCheck_1671_ = !lean_is_exclusive(v_head_1655_);
if (v_isSharedCheck_1671_ == 0)
{
lean_object* v_unused_1672_; 
v_unused_1672_ = lean_ctor_get(v_head_1655_, 0);
lean_dec(v_unused_1672_);
v___x_1658_ = v_head_1655_;
v_isShared_1659_ = v_isSharedCheck_1671_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_after_1656_);
lean_dec(v_head_1655_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1671_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1660_; lean_object* v___x_1662_; 
v___x_1660_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0);
if (v_isShared_1659_ == 0)
{
lean_ctor_set_tag(v___x_1658_, 7);
lean_ctor_set(v___x_1658_, 1, v___x_1660_);
lean_ctor_set(v___x_1658_, 0, v_msgData_1646_);
v___x_1662_ = v___x_1658_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_msgData_1646_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v___x_1660_);
v___x_1662_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v_msgData_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1663_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2);
v___x_1664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1662_);
lean_ctor_set(v___x_1664_, 1, v___x_1663_);
v___x_1665_ = l_Lean_MessageData_ofSyntax(v_after_1656_);
v___x_1666_ = l_Lean_indentD(v___x_1665_);
v_msgData_1667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1667_, 0, v___x_1664_);
lean_ctor_set(v_msgData_1667_, 1, v___x_1666_);
v___x_1668_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6(v_msgData_1667_, v_macroStack_1647_);
v___x_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1668_);
return v___x_1669_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___boxed(lean_object* v_msgData_1673_, lean_object* v_macroStack_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(v_msgData_1673_, v_macroStack_1674_, v___y_1675_);
lean_dec_ref(v___y_1675_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(lean_object* v_msg_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v_ref_1686_; lean_object* v___x_1687_; lean_object* v_a_1688_; lean_object* v_macroStack_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1700_; 
v_ref_1686_ = lean_ctor_get(v___y_1683_, 5);
v___x_1687_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(v_msg_1678_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_a_1688_);
lean_dec_ref(v___x_1687_);
v_macroStack_1689_ = lean_ctor_get(v___y_1679_, 1);
v___x_1690_ = l_Lean_Elab_getBetterRef(v_ref_1686_, v_macroStack_1689_);
lean_inc(v_macroStack_1689_);
v___x_1691_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(v_a_1688_, v_macroStack_1689_, v___y_1683_);
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1694_ = v___x_1691_;
v_isShared_1695_ = v_isSharedCheck_1700_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1691_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1700_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1696_; lean_object* v___x_1698_; 
v___x_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1690_);
lean_ctor_set(v___x_1696_, 1, v_a_1692_);
if (v_isShared_1695_ == 0)
{
lean_ctor_set_tag(v___x_1694_, 1);
lean_ctor_set(v___x_1694_, 0, v___x_1696_);
v___x_1698_ = v___x_1694_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1696_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg___boxed(lean_object* v_msg_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v_msg_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
return v_res_1709_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1715_ = lean_box(0);
v___x_1716_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__2___closed__2));
v___x_1717_ = l_Lean_mkConst(v___x_1716_, v___x_1715_);
return v___x_1717_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__2___closed__5(void){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__2___closed__4));
v___x_1720_ = l_Lean_stringToMessageData(v___x_1719_);
return v___x_1720_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__2___closed__7(void){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__2___closed__6));
v___x_1723_ = l_Lean_stringToMessageData(v___x_1722_);
return v___x_1723_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__2___closed__10(void){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1727_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__2___closed__9));
v___x_1728_ = l_Lean_MessageData_ofFormat(v___x_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__2(lean_object* v___y_1729_, lean_object* v_monadInfo_1730_, uint8_t v_returnsEarly_1731_, lean_object* v___x_1732_, lean_object* v_a_1733_, uint8_t v___x_1734_, lean_object* v_e_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v_defs_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___x_1767_; lean_object* v_returnVar_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1802_; lean_object* v___y_1803_; 
v___x_1767_ = lean_mk_empty_array_with_capacity(v___x_1732_);
if (lean_obj_tag(v_e_1735_) == 0)
{
if (v___x_1734_ == 0)
{
goto v___jp_1816_;
}
else
{
goto v___jp_1777_;
}
}
else
{
goto v___jp_1816_;
}
v___jp_1743_:
{
size_t v_sz_1751_; size_t v___x_1752_; lean_object* v___x_1753_; 
v_sz_1751_ = lean_array_size(v___y_1729_);
v___x_1752_ = ((size_t)0ULL);
v___x_1753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1(v_monadInfo_1730_, v___y_1729_, v_sz_1751_, v___x_1752_, v_defs_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
if (lean_obj_tag(v___x_1753_) == 0)
{
if (v_returnsEarly_1731_ == 0)
{
return v___x_1753_;
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1755_; uint8_t v___x_1756_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1754_);
v___x_1755_ = lean_array_get_size(v___y_1729_);
v___x_1756_ = lean_nat_dec_eq(v___x_1755_, v___x_1732_);
if (v___x_1756_ == 0)
{
lean_dec(v_a_1754_);
return v___x_1753_;
}
else
{
lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1765_; 
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1765_ == 0)
{
lean_object* v_unused_1766_; 
v_unused_1766_ = lean_ctor_get(v___x_1753_, 0);
lean_dec(v_unused_1766_);
v___x_1758_ = v___x_1753_;
v_isShared_1759_ = v_isSharedCheck_1765_;
goto v_resetjp_1757_;
}
else
{
lean_dec(v___x_1753_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1765_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1763_; 
v___x_1760_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__2___closed__3, &l_Lean_Elab_Do_elabDoFor___lam__2___closed__3_once, _init_l_Lean_Elab_Do_elabDoFor___lam__2___closed__3);
v___x_1761_ = lean_array_push(v_a_1754_, v___x_1760_);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v___x_1761_);
v___x_1763_ = v___x_1758_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1761_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
}
else
{
return v___x_1753_;
}
}
v___jp_1768_:
{
lean_object* v___x_1776_; 
v___x_1776_ = lean_array_push(v___x_1767_, v_returnVar_1769_);
v_defs_1744_ = v___x_1776_;
v___y_1745_ = v___y_1770_;
v___y_1746_ = v___y_1771_;
v___y_1747_ = v___y_1772_;
v___y_1748_ = v___y_1773_;
v___y_1749_ = v___y_1774_;
v___y_1750_ = v___y_1775_;
goto v___jp_1743_;
}
v___jp_1777_:
{
if (v_returnsEarly_1731_ == 0)
{
lean_dec(v_e_1735_);
lean_dec_ref(v_a_1733_);
v_defs_1744_ = v___x_1767_;
v___y_1745_ = v___y_1736_;
v___y_1746_ = v___y_1737_;
v___y_1747_ = v___y_1738_;
v___y_1748_ = v___y_1739_;
v___y_1749_ = v___y_1740_;
v___y_1750_ = v___y_1741_;
goto v___jp_1743_;
}
else
{
if (lean_obj_tag(v_e_1735_) == 0)
{
lean_object* v_resultType_1778_; lean_object* v___x_1779_; 
v_resultType_1778_ = lean_ctor_get(v_a_1733_, 0);
lean_inc_ref(v_resultType_1778_);
lean_dec_ref(v_a_1733_);
v___x_1779_ = l_Lean_Meta_mkNone(v_resultType_1778_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_a_1780_; 
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_a_1780_);
lean_dec_ref(v___x_1779_);
v_returnVar_1769_ = v_a_1780_;
v___y_1770_ = v___y_1736_;
v___y_1771_ = v___y_1737_;
v___y_1772_ = v___y_1738_;
v___y_1773_ = v___y_1739_;
v___y_1774_ = v___y_1740_;
v___y_1775_ = v___y_1741_;
goto v___jp_1768_;
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_dec_ref(v___x_1767_);
lean_dec_ref(v_monadInfo_1730_);
v_a_1781_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1779_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1779_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
else
{
lean_object* v_val_1789_; lean_object* v_resultType_1790_; lean_object* v___x_1791_; 
v_val_1789_ = lean_ctor_get(v_e_1735_, 0);
lean_inc(v_val_1789_);
lean_dec_ref(v_e_1735_);
v_resultType_1790_ = lean_ctor_get(v_a_1733_, 0);
lean_inc_ref(v_resultType_1790_);
lean_dec_ref(v_a_1733_);
v___x_1791_ = l_Lean_Meta_mkSome(v_resultType_1790_, v_val_1789_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_a_1792_; 
v_a_1792_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_a_1792_);
lean_dec_ref(v___x_1791_);
v_returnVar_1769_ = v_a_1792_;
v___y_1770_ = v___y_1736_;
v___y_1771_ = v___y_1737_;
v___y_1772_ = v___y_1738_;
v___y_1773_ = v___y_1739_;
v___y_1774_ = v___y_1740_;
v___y_1775_ = v___y_1741_;
goto v___jp_1768_;
}
else
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
lean_dec_ref(v___x_1767_);
lean_dec_ref(v_monadInfo_1730_);
v_a_1793_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1791_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1791_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
}
}
v___jp_1801_:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1815_; 
lean_inc_ref(v___y_1802_);
v___x_1804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1804_, 0, v___y_1802_);
lean_ctor_set(v___x_1804_, 1, v___y_1803_);
v___x_1805_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__2___closed__5, &l_Lean_Elab_Do_elabDoFor___lam__2___closed__5_once, _init_l_Lean_Elab_Do_elabDoFor___lam__2___closed__5);
v___x_1806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1804_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
v___x_1807_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v___x_1806_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1810_ = v___x_1807_;
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1807_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
v___jp_1816_:
{
if (v_returnsEarly_1731_ == 0)
{
lean_object* v___x_1817_; 
lean_dec_ref(v___x_1767_);
lean_dec_ref(v_a_1733_);
lean_dec_ref(v_monadInfo_1730_);
v___x_1817_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__2___closed__7, &l_Lean_Elab_Do_elabDoFor___lam__2___closed__7_once, _init_l_Lean_Elab_Do_elabDoFor___lam__2___closed__7);
if (lean_obj_tag(v_e_1735_) == 0)
{
lean_object* v___x_1818_; 
v___x_1818_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__2___closed__10, &l_Lean_Elab_Do_elabDoFor___lam__2___closed__10_once, _init_l_Lean_Elab_Do_elabDoFor___lam__2___closed__10);
v___y_1802_ = v___x_1817_;
v___y_1803_ = v___x_1818_;
goto v___jp_1801_;
}
else
{
lean_object* v_val_1819_; lean_object* v___x_1820_; 
v_val_1819_ = lean_ctor_get(v_e_1735_, 0);
lean_inc(v_val_1819_);
lean_dec_ref(v_e_1735_);
v___x_1820_ = l_Lean_MessageData_ofExpr(v_val_1819_);
v___y_1802_ = v___x_1817_;
v___y_1803_ = v___x_1820_;
goto v___jp_1801_;
}
}
else
{
goto v___jp_1777_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__2___boxed(lean_object* v___y_1821_, lean_object* v_monadInfo_1822_, lean_object* v_returnsEarly_1823_, lean_object* v___x_1824_, lean_object* v_a_1825_, lean_object* v___x_1826_, lean_object* v_e_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
uint8_t v_returnsEarly_boxed_1835_; uint8_t v___x_81921__boxed_1836_; lean_object* v_res_1837_; 
v_returnsEarly_boxed_1835_ = lean_unbox(v_returnsEarly_1823_);
v___x_81921__boxed_1836_ = lean_unbox(v___x_1826_);
v_res_1837_ = l_Lean_Elab_Do_elabDoFor___lam__2(v___y_1821_, v_monadInfo_1822_, v_returnsEarly_boxed_1835_, v___x_1824_, v_a_1825_, v___x_81921__boxed_1836_, v_e_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___x_1824_);
lean_dec_ref(v___y_1821_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__4(lean_object* v___f_1839_, lean_object* v_u_1840_, lean_object* v___x_1841_, lean_object* v___x_1842_, lean_object* v_snd_1843_, lean_object* v___x_1844_, lean_object* v_e_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1854_, 0, v_e_1845_);
lean_inc(v___y_1852_);
lean_inc_ref(v___y_1851_);
lean_inc(v___y_1850_);
lean_inc_ref(v___y_1849_);
lean_inc(v___y_1848_);
lean_inc_ref(v___y_1847_);
v___x_1855_ = lean_apply_8(v___f_1839_, v___x_1854_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, lean_box(0));
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; lean_object* v___x_1857_; 
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_a_1856_);
lean_dec_ref(v___x_1855_);
v___x_1857_ = l_Lean_Meta_mkProdMkN(v_a_1856_, v_u_1840_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v_a_1858_; lean_object* v_fst_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
lean_inc(v_a_1858_);
lean_dec_ref(v___x_1857_);
v_fst_1859_ = lean_ctor_get(v_a_1858_, 0);
lean_inc(v_fst_1859_);
lean_dec(v_a_1858_);
v___x_1860_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__4___closed__0));
v___x_1861_ = l_Lean_Name_mkStr2(v___x_1841_, v___x_1860_);
v___x_1862_ = l_Lean_mkConst(v___x_1861_, v___x_1842_);
v___x_1863_ = l_Lean_mkAppB(v___x_1862_, v_snd_1843_, v_fst_1859_);
v___x_1864_ = l_Lean_Elab_Do_mkPureApp(v___x_1844_, v___x_1863_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
return v___x_1864_;
}
else
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1872_; 
lean_dec_ref(v___x_1844_);
lean_dec_ref(v_snd_1843_);
lean_dec(v___x_1842_);
lean_dec_ref(v___x_1841_);
v_a_1865_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v___x_1857_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1857_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1870_; 
if (v_isShared_1868_ == 0)
{
v___x_1870_ = v___x_1867_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1865_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
lean_dec_ref(v___x_1844_);
lean_dec_ref(v_snd_1843_);
lean_dec(v___x_1842_);
lean_dec_ref(v___x_1841_);
lean_dec(v_u_1840_);
v_a_1873_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1855_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1855_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___boxed(lean_object* v___f_1881_, lean_object* v_u_1882_, lean_object* v___x_1883_, lean_object* v___x_1884_, lean_object* v_snd_1885_, lean_object* v___x_1886_, lean_object* v_e_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Lean_Elab_Do_elabDoFor___lam__4(v___f_1881_, v_u_1882_, v___x_1883_, v___x_1884_, v_snd_1885_, v___x_1886_, v_e_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec_ref(v___y_1888_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__5(lean_object* v___f_1898_, lean_object* v___x_1899_, lean_object* v_u_1900_, lean_object* v___x_1901_, lean_object* v___x_1902_, lean_object* v_snd_1903_, lean_object* v___x_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v___x_1913_; 
lean_inc(v___y_1911_);
lean_inc_ref(v___y_1910_);
lean_inc(v___y_1909_);
lean_inc_ref(v___y_1908_);
lean_inc(v___y_1907_);
lean_inc_ref(v___y_1906_);
v___x_1913_ = lean_apply_8(v___f_1898_, v___x_1899_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, lean_box(0));
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1915_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref(v___x_1913_);
v___x_1915_ = l_Lean_Meta_mkProdMkN(v_a_1914_, v_u_1900_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v_fst_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref(v___x_1915_);
v_fst_1917_ = lean_ctor_get(v_a_1916_, 0);
lean_inc(v_fst_1917_);
lean_dec(v_a_1916_);
v___x_1918_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__5___closed__0));
v___x_1919_ = l_Lean_Name_mkStr2(v___x_1901_, v___x_1918_);
v___x_1920_ = l_Lean_mkConst(v___x_1919_, v___x_1902_);
v___x_1921_ = l_Lean_mkAppB(v___x_1920_, v_snd_1903_, v_fst_1917_);
v___x_1922_ = l_Lean_Elab_Do_mkPureApp(v___x_1904_, v___x_1921_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
return v___x_1922_;
}
else
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1930_; 
lean_dec_ref(v___x_1904_);
lean_dec_ref(v_snd_1903_);
lean_dec(v___x_1902_);
lean_dec_ref(v___x_1901_);
v_a_1923_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1925_ = v___x_1915_;
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1915_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1928_; 
if (v_isShared_1926_ == 0)
{
v___x_1928_ = v___x_1925_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_a_1923_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_dec_ref(v___x_1904_);
lean_dec_ref(v_snd_1903_);
lean_dec(v___x_1902_);
lean_dec_ref(v___x_1901_);
lean_dec(v_u_1900_);
v_a_1931_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1913_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1913_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__5___boxed(lean_object* v___f_1939_, lean_object* v___x_1940_, lean_object* v_u_1941_, lean_object* v___x_1942_, lean_object* v___x_1943_, lean_object* v_snd_1944_, lean_object* v___x_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lean_Elab_Do_elabDoFor___lam__5(v___f_1939_, v___x_1940_, v_u_1941_, v___x_1942_, v___x_1943_, v_snd_1944_, v___x_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec_ref(v___y_1946_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__6(lean_object* v___f_1955_, lean_object* v___x_1956_, lean_object* v_u_1957_, lean_object* v___x_1958_, lean_object* v___x_1959_, lean_object* v_snd_1960_, lean_object* v___x_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v___x_1970_; 
lean_inc(v___y_1968_);
lean_inc_ref(v___y_1967_);
lean_inc(v___y_1966_);
lean_inc_ref(v___y_1965_);
lean_inc(v___y_1964_);
lean_inc_ref(v___y_1963_);
v___x_1970_ = lean_apply_8(v___f_1955_, v___x_1956_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, lean_box(0));
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v_a_1971_; lean_object* v___x_1972_; 
v_a_1971_ = lean_ctor_get(v___x_1970_, 0);
lean_inc(v_a_1971_);
lean_dec_ref(v___x_1970_);
v___x_1972_ = l_Lean_Meta_mkProdMkN(v_a_1971_, v_u_1957_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1973_; lean_object* v_fst_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_a_1973_);
lean_dec_ref(v___x_1972_);
v_fst_1974_ = lean_ctor_get(v_a_1973_, 0);
lean_inc(v_fst_1974_);
lean_dec(v_a_1973_);
v___x_1975_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__4___closed__0));
v___x_1976_ = l_Lean_Name_mkStr2(v___x_1958_, v___x_1975_);
v___x_1977_ = l_Lean_mkConst(v___x_1976_, v___x_1959_);
v___x_1978_ = l_Lean_mkAppB(v___x_1977_, v_snd_1960_, v_fst_1974_);
v___x_1979_ = l_Lean_Elab_Do_mkPureApp(v___x_1961_, v___x_1978_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
return v___x_1979_;
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec_ref(v___x_1961_);
lean_dec_ref(v_snd_1960_);
lean_dec(v___x_1959_);
lean_dec_ref(v___x_1958_);
v_a_1980_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1972_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1972_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_dec_ref(v___x_1961_);
lean_dec_ref(v_snd_1960_);
lean_dec(v___x_1959_);
lean_dec_ref(v___x_1958_);
lean_dec(v_u_1957_);
v_a_1988_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1970_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1970_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__6___boxed(lean_object* v___f_1996_, lean_object* v___x_1997_, lean_object* v_u_1998_, lean_object* v___x_1999_, lean_object* v___x_2000_, lean_object* v_snd_2001_, lean_object* v___x_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l_Lean_Elab_Do_elabDoFor___lam__6(v___f_1996_, v___x_1997_, v_u_1998_, v___x_1999_, v___x_2000_, v_snd_2001_, v___x_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec_ref(v___y_2003_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__7(lean_object* v___x_2012_, lean_object* v___f_2013_, lean_object* v___f_2014_, lean_object* v___x_2015_, lean_object* v___x_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
lean_object* v_monadInfo_2025_; lean_object* v_mutVars_2026_; lean_object* v_mutVarDefs_2027_; lean_object* v_contInfo_2028_; uint8_t v_deadCode_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2037_; 
v_monadInfo_2025_ = lean_ctor_get(v___y_2017_, 0);
v_mutVars_2026_ = lean_ctor_get(v___y_2017_, 1);
v_mutVarDefs_2027_ = lean_ctor_get(v___y_2017_, 2);
v_contInfo_2028_ = lean_ctor_get(v___y_2017_, 4);
v_deadCode_2029_ = lean_ctor_get_uint8(v___y_2017_, sizeof(void*)*5);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___y_2017_);
if (v_isSharedCheck_2037_ == 0)
{
lean_object* v_unused_2038_; 
v_unused_2038_ = lean_ctor_get(v___y_2017_, 3);
lean_dec(v_unused_2038_);
v___x_2031_ = v___y_2017_;
v_isShared_2032_ = v_isSharedCheck_2037_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_contInfo_2028_);
lean_inc(v_mutVarDefs_2027_);
lean_inc(v_mutVars_2026_);
lean_inc(v_monadInfo_2025_);
lean_dec(v___y_2017_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2037_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 3, v___x_2012_);
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_monadInfo_2025_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v_mutVars_2026_);
lean_ctor_set(v_reuseFailAlloc_2036_, 2, v_mutVarDefs_2027_);
lean_ctor_set(v_reuseFailAlloc_2036_, 3, v___x_2012_);
lean_ctor_set(v_reuseFailAlloc_2036_, 4, v_contInfo_2028_);
lean_ctor_set_uint8(v_reuseFailAlloc_2036_, sizeof(void*)*5, v_deadCode_2029_);
v___x_2034_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
lean_object* v___x_2035_; 
v___x_2035_ = l_Lean_Elab_Do_enterLoopBody___redArg(v___f_2013_, v___f_2014_, v___x_2015_, v___x_2016_, v___x_2034_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
lean_dec_ref(v___x_2034_);
return v___x_2035_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__7___boxed(lean_object* v___x_2039_, lean_object* v___f_2040_, lean_object* v___f_2041_, lean_object* v___x_2042_, lean_object* v___x_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l_Lean_Elab_Do_elabDoFor___lam__7(v___x_2039_, v___f_2040_, v___f_2041_, v___x_2042_, v___x_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
lean_dec(v___y_2050_);
lean_dec_ref(v___y_2049_);
lean_dec(v___y_2048_);
lean_dec_ref(v___y_2047_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__8(lean_object* v_a_2056_, lean_object* v_u_2057_, lean_object* v_snd_2058_, lean_object* v___f_2059_, lean_object* v___x_2060_, lean_object* v_resultName_2061_, lean_object* v_resultType_2062_, lean_object* v_body_2063_, uint8_t v___x_2064_, lean_object* v___y_2065_, lean_object* v_xh_2066_, lean_object* v_loopS_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
lean_object* v_resultType_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2104_; 
v_resultType_2076_ = lean_ctor_get(v_a_2056_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v_a_2056_);
if (v_isSharedCheck_2104_ == 0)
{
lean_object* v_unused_2105_; 
v_unused_2105_ = lean_ctor_get(v_a_2056_, 1);
lean_dec(v_unused_2105_);
v___x_2078_ = v_a_2056_;
v_isShared_2079_ = v_isSharedCheck_2104_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_resultType_2076_);
lean_dec(v_a_2056_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2104_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___f_2087_; lean_object* v___f_2088_; lean_object* v___f_2089_; lean_object* v___x_2091_; 
v___x_2080_ = l_Lean_Expr_fvarId_x21(v_loopS_2067_);
v___x_2081_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__8___closed__0));
v___x_2082_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__8___closed__1));
v___x_2083_ = lean_box(0);
lean_inc_n(v_u_2057_, 3);
v___x_2084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2084_, 0, v_u_2057_);
lean_ctor_set(v___x_2084_, 1, v___x_2083_);
lean_inc_ref_n(v___x_2084_, 3);
v___x_2085_ = l_Lean_mkConst(v___x_2082_, v___x_2084_);
lean_inc_ref_n(v_snd_2058_, 3);
v___x_2086_ = l_Lean_Expr_app___override(v___x_2085_, v_snd_2058_);
lean_inc_ref_n(v___x_2086_, 3);
lean_inc_ref_n(v___f_2059_, 2);
v___f_2087_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__4___boxed), 15, 6);
lean_closure_set(v___f_2087_, 0, v___f_2059_);
lean_closure_set(v___f_2087_, 1, v_u_2057_);
lean_closure_set(v___f_2087_, 2, v___x_2081_);
lean_closure_set(v___f_2087_, 3, v___x_2084_);
lean_closure_set(v___f_2087_, 4, v_snd_2058_);
lean_closure_set(v___f_2087_, 5, v___x_2086_);
lean_inc(v___x_2060_);
v___f_2088_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__5___boxed), 15, 7);
lean_closure_set(v___f_2088_, 0, v___f_2059_);
lean_closure_set(v___f_2088_, 1, v___x_2060_);
lean_closure_set(v___f_2088_, 2, v_u_2057_);
lean_closure_set(v___f_2088_, 3, v___x_2081_);
lean_closure_set(v___f_2088_, 4, v___x_2084_);
lean_closure_set(v___f_2088_, 5, v_snd_2058_);
lean_closure_set(v___f_2088_, 6, v___x_2086_);
v___f_2089_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__6___boxed), 15, 7);
lean_closure_set(v___f_2089_, 0, v___f_2059_);
lean_closure_set(v___f_2089_, 1, v___x_2060_);
lean_closure_set(v___f_2089_, 2, v_u_2057_);
lean_closure_set(v___f_2089_, 3, v___x_2081_);
lean_closure_set(v___f_2089_, 4, v___x_2084_);
lean_closure_set(v___f_2089_, 5, v_snd_2058_);
lean_closure_set(v___f_2089_, 6, v___x_2086_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 1, v___f_2087_);
v___x_2091_ = v___x_2078_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_resultType_2076_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v___f_2087_);
v___x_2091_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
uint8_t v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___f_2096_; lean_object* v___x_2097_; 
v___x_2092_ = 1;
lean_inc_ref(v___f_2088_);
v___x_2093_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2093_, 0, v_resultName_2061_);
lean_ctor_set(v___x_2093_, 1, v_resultType_2062_);
lean_ctor_set(v___x_2093_, 2, v___f_2088_);
lean_ctor_set_uint8(v___x_2093_, sizeof(void*)*3, v___x_2092_);
v___x_2094_ = lean_box(v___x_2064_);
v___x_2095_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoSeq___boxed), 11, 3);
lean_closure_set(v___x_2095_, 0, v_body_2063_);
lean_closure_set(v___x_2095_, 1, v___x_2093_);
lean_closure_set(v___x_2095_, 2, v___x_2094_);
v___f_2096_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__7___boxed), 13, 5);
lean_closure_set(v___f_2096_, 0, v___x_2086_);
lean_closure_set(v___f_2096_, 1, v___f_2089_);
lean_closure_set(v___f_2096_, 2, v___f_2088_);
lean_closure_set(v___f_2096_, 3, v___x_2091_);
lean_closure_set(v___f_2096_, 4, v___x_2095_);
v___x_2097_ = l_Lean_Elab_Do_bindMutVarsFromTuple(v___y_2065_, v___x_2080_, v___f_2096_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_a_2098_; lean_object* v___x_2099_; uint8_t v___x_2100_; uint8_t v___x_2101_; lean_object* v___x_2102_; 
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_a_2098_);
lean_dec_ref(v___x_2097_);
v___x_2099_ = lean_array_push(v_xh_2066_, v_loopS_2067_);
v___x_2100_ = 0;
v___x_2101_ = 1;
v___x_2102_ = l_Lean_Meta_mkLambdaFVars(v___x_2099_, v_a_2098_, v___x_2100_, v___x_2064_, v___x_2100_, v___x_2064_, v___x_2101_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
lean_dec_ref(v___x_2099_);
return v___x_2102_;
}
else
{
lean_dec_ref(v_loopS_2067_);
lean_dec_ref(v_xh_2066_);
return v___x_2097_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__8___boxed(lean_object** _args){
lean_object* v_a_2106_ = _args[0];
lean_object* v_u_2107_ = _args[1];
lean_object* v_snd_2108_ = _args[2];
lean_object* v___f_2109_ = _args[3];
lean_object* v___x_2110_ = _args[4];
lean_object* v_resultName_2111_ = _args[5];
lean_object* v_resultType_2112_ = _args[6];
lean_object* v_body_2113_ = _args[7];
lean_object* v___x_2114_ = _args[8];
lean_object* v___y_2115_ = _args[9];
lean_object* v_xh_2116_ = _args[10];
lean_object* v_loopS_2117_ = _args[11];
lean_object* v___y_2118_ = _args[12];
lean_object* v___y_2119_ = _args[13];
lean_object* v___y_2120_ = _args[14];
lean_object* v___y_2121_ = _args[15];
lean_object* v___y_2122_ = _args[16];
lean_object* v___y_2123_ = _args[17];
lean_object* v___y_2124_ = _args[18];
lean_object* v___y_2125_ = _args[19];
_start:
{
uint8_t v___x_82477__boxed_2126_; lean_object* v_res_2127_; 
v___x_82477__boxed_2126_ = lean_unbox(v___x_2114_);
v_res_2127_ = l_Lean_Elab_Do_elabDoFor___lam__8(v_a_2106_, v_u_2107_, v_snd_2108_, v___f_2109_, v___x_2110_, v_resultName_2111_, v_resultType_2112_, v_body_2113_, v___x_82477__boxed_2126_, v___y_2115_, v_xh_2116_, v_loopS_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec_ref(v___y_2118_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9(lean_object* v___x_2128_, lean_object* v___x_2129_, lean_object* v_x_2130_, lean_object* v_a_2131_, lean_object* v_u_2132_, lean_object* v_snd_2133_, lean_object* v___f_2134_, lean_object* v___x_2135_, lean_object* v_resultName_2136_, lean_object* v_resultType_2137_, lean_object* v_body_2138_, uint8_t v___x_2139_, lean_object* v___y_2140_, lean_object* v_a_2141_, lean_object* v_h_x3f_2142_, lean_object* v___x_2143_, lean_object* v_xh_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2153_ = lean_array_get_borrowed(v___x_2128_, v_xh_2144_, v___x_2129_);
lean_inc(v___x_2153_);
v___x_2154_ = l_Lean_Elab_Term_addLocalVarInfo(v_x_2130_, v___x_2153_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v___x_2155_; lean_object* v___f_2156_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v___y_2163_; lean_object* v___y_2164_; 
lean_dec_ref(v___x_2154_);
v___x_2155_ = lean_box(v___x_2139_);
lean_inc_ref(v_xh_2144_);
lean_inc_ref(v_snd_2133_);
v___f_2156_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__8___boxed), 20, 11);
lean_closure_set(v___f_2156_, 0, v_a_2131_);
lean_closure_set(v___f_2156_, 1, v_u_2132_);
lean_closure_set(v___f_2156_, 2, v_snd_2133_);
lean_closure_set(v___f_2156_, 3, v___f_2134_);
lean_closure_set(v___f_2156_, 4, v___x_2135_);
lean_closure_set(v___f_2156_, 5, v_resultName_2136_);
lean_closure_set(v___f_2156_, 6, v_resultType_2137_);
lean_closure_set(v___f_2156_, 7, v_body_2138_);
lean_closure_set(v___f_2156_, 8, v___x_2155_);
lean_closure_set(v___f_2156_, 9, v___y_2140_);
lean_closure_set(v___f_2156_, 10, v_xh_2144_);
if (lean_obj_tag(v_h_x3f_2142_) == 1)
{
lean_object* v_val_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v_val_2168_ = lean_ctor_get(v_h_x3f_2142_, 0);
lean_inc(v_val_2168_);
lean_dec_ref(v_h_x3f_2142_);
v___x_2169_ = lean_array_get(v___x_2128_, v_xh_2144_, v___x_2143_);
lean_dec_ref(v_xh_2144_);
v___x_2170_ = l_Lean_Elab_Term_addLocalVarInfo(v_val_2168_, v___x_2169_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_dec_ref(v___x_2170_);
v___y_2158_ = v___y_2145_;
v___y_2159_ = v___y_2146_;
v___y_2160_ = v___y_2147_;
v___y_2161_ = v___y_2148_;
v___y_2162_ = v___y_2149_;
v___y_2163_ = v___y_2150_;
v___y_2164_ = v___y_2151_;
goto v___jp_2157_;
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
lean_dec_ref(v___f_2156_);
lean_dec(v_a_2141_);
lean_dec_ref(v_snd_2133_);
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2170_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2170_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
else
{
lean_dec_ref(v_xh_2144_);
lean_dec(v_h_x3f_2142_);
v___y_2158_ = v___y_2145_;
v___y_2159_ = v___y_2146_;
v___y_2160_ = v___y_2147_;
v___y_2161_ = v___y_2148_;
v___y_2162_ = v___y_2149_;
v___y_2163_ = v___y_2150_;
v___y_2164_ = v___y_2151_;
goto v___jp_2157_;
}
v___jp_2157_:
{
uint8_t v___x_2165_; uint8_t v___x_2166_; lean_object* v___x_2167_; 
v___x_2165_ = 0;
v___x_2166_ = 1;
v___x_2167_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_a_2141_, v___x_2165_, v_snd_2133_, v___f_2156_, v___x_2166_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
return v___x_2167_;
}
}
else
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
lean_dec_ref(v_xh_2144_);
lean_dec(v_h_x3f_2142_);
lean_dec(v_a_2141_);
lean_dec(v___y_2140_);
lean_dec(v_body_2138_);
lean_dec_ref(v_resultType_2137_);
lean_dec(v_resultName_2136_);
lean_dec(v___x_2135_);
lean_dec_ref(v___f_2134_);
lean_dec_ref(v_snd_2133_);
lean_dec(v_u_2132_);
lean_dec_ref(v_a_2131_);
v_a_2179_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2154_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2154_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9___boxed(lean_object** _args){
lean_object* v___x_2187_ = _args[0];
lean_object* v___x_2188_ = _args[1];
lean_object* v_x_2189_ = _args[2];
lean_object* v_a_2190_ = _args[3];
lean_object* v_u_2191_ = _args[4];
lean_object* v_snd_2192_ = _args[5];
lean_object* v___f_2193_ = _args[6];
lean_object* v___x_2194_ = _args[7];
lean_object* v_resultName_2195_ = _args[8];
lean_object* v_resultType_2196_ = _args[9];
lean_object* v_body_2197_ = _args[10];
lean_object* v___x_2198_ = _args[11];
lean_object* v___y_2199_ = _args[12];
lean_object* v_a_2200_ = _args[13];
lean_object* v_h_x3f_2201_ = _args[14];
lean_object* v___x_2202_ = _args[15];
lean_object* v_xh_2203_ = _args[16];
lean_object* v___y_2204_ = _args[17];
lean_object* v___y_2205_ = _args[18];
lean_object* v___y_2206_ = _args[19];
lean_object* v___y_2207_ = _args[20];
lean_object* v___y_2208_ = _args[21];
lean_object* v___y_2209_ = _args[22];
lean_object* v___y_2210_ = _args[23];
lean_object* v___y_2211_ = _args[24];
_start:
{
uint8_t v___x_82583__boxed_2212_; lean_object* v_res_2213_; 
v___x_82583__boxed_2212_ = lean_unbox(v___x_2198_);
v_res_2213_ = l_Lean_Elab_Do_elabDoFor___lam__9(v___x_2187_, v___x_2188_, v_x_2189_, v_a_2190_, v_u_2191_, v_snd_2192_, v___f_2193_, v___x_2194_, v_resultName_2195_, v_resultType_2196_, v_body_2197_, v___x_82583__boxed_2212_, v___y_2199_, v_a_2200_, v_h_x3f_2201_, v___x_2202_, v_xh_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec(v___x_2202_);
lean_dec(v___x_2188_);
lean_dec_ref(v___x_2187_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(lean_object* v_name_2214_, lean_object* v_type_2215_, lean_object* v_k_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
uint8_t v___x_2225_; uint8_t v___x_2226_; lean_object* v___x_2227_; 
v___x_2225_ = 0;
v___x_2226_ = 0;
v___x_2227_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_name_2214_, v___x_2225_, v_type_2215_, v_k_2216_, v___x_2226_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg___boxed(lean_object* v_name_2228_, lean_object* v_type_2229_, lean_object* v_k_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(v_name_2228_, v_type_2229_, v_k_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec_ref(v___y_2231_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__10(uint8_t v_returnsEarly_2257_, lean_object* v_dec_2258_, lean_object* v_a_2259_, lean_object* v_doBlockResultType_2260_, lean_object* v_a_2261_, lean_object* v_v_2262_, lean_object* v_u_2263_, lean_object* v___f_2264_, lean_object* v___y_2265_, lean_object* v___x_2266_, lean_object* v___x_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v_ret_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2283_; lean_object* v___y_2284_; 
if (v_returnsEarly_2257_ == 0)
{
lean_object* v___x_2331_; 
lean_dec_ref(v___f_2264_);
lean_dec(v_u_2263_);
lean_dec(v_v_2262_);
lean_dec_ref(v_a_2261_);
lean_dec_ref(v_doBlockResultType_2260_);
lean_dec(v_a_2259_);
v___x_2331_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_dec_2258_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
return v___x_2331_;
}
else
{
lean_object* v___x_2332_; 
v___x_2332_ = l_Lean_Meta_getFVarFromUserName(v_a_2259_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; lean_object* v___x_2334_; uint8_t v___x_2335_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2333_);
lean_dec_ref(v___x_2332_);
v___x_2334_ = lean_array_get_size(v___y_2265_);
v___x_2335_ = lean_nat_dec_eq(v___x_2334_, v___x_2266_);
if (v___x_2335_ == 0)
{
v_ret_2277_ = v_a_2333_;
v___y_2278_ = v___y_2268_;
v___y_2279_ = v___y_2269_;
v___y_2280_ = v___y_2270_;
v___y_2281_ = v___y_2271_;
v___y_2282_ = v___y_2272_;
v___y_2283_ = v___y_2273_;
v___y_2284_ = v___y_2274_;
goto v___jp_2276_;
}
else
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2336_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__10___closed__9));
v___x_2337_ = lean_mk_empty_array_with_capacity(v___x_2267_);
v___x_2338_ = lean_array_push(v___x_2337_, v_a_2333_);
v___x_2339_ = l_Lean_Meta_mkAppM(v___x_2336_, v___x_2338_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_a_2340_);
lean_dec_ref(v___x_2339_);
v_ret_2277_ = v_a_2340_;
v___y_2278_ = v___y_2268_;
v___y_2279_ = v___y_2269_;
v___y_2280_ = v___y_2270_;
v___y_2281_ = v___y_2271_;
v___y_2282_ = v___y_2272_;
v___y_2283_ = v___y_2273_;
v___y_2284_ = v___y_2274_;
goto v___jp_2276_;
}
else
{
lean_dec_ref(v___f_2264_);
lean_dec(v_u_2263_);
lean_dec(v_v_2262_);
lean_dec_ref(v_a_2261_);
lean_dec_ref(v_doBlockResultType_2260_);
lean_dec_ref(v_dec_2258_);
return v___x_2339_;
}
}
}
else
{
lean_dec_ref(v___f_2264_);
lean_dec(v_u_2263_);
lean_dec(v_v_2262_);
lean_dec_ref(v_a_2261_);
lean_dec_ref(v_doBlockResultType_2260_);
lean_dec_ref(v_dec_2258_);
return v___x_2332_;
}
}
v___jp_2276_:
{
lean_object* v___x_2285_; 
lean_inc(v___y_2284_);
lean_inc_ref(v___y_2283_);
lean_inc(v___y_2282_);
lean_inc_ref(v___y_2281_);
lean_inc_ref(v_ret_2277_);
v___x_2285_ = lean_infer_type(v_ret_2277_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v___x_2287_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2286_);
lean_dec_ref(v___x_2285_);
v___x_2287_ = l_Lean_Elab_Do_mkMonadicType___redArg(v_doBlockResultType_2260_, v___y_2278_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; lean_object* v___x_2289_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2288_);
lean_dec_ref(v___x_2287_);
v___x_2289_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_dec_2258_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v_a_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_a_2290_);
lean_dec_ref(v___x_2289_);
v___x_2291_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__10___closed__1));
v___x_2292_ = l_Lean_Core_mkFreshUserName(v___x_2291_, v___y_2283_, v___y_2284_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; lean_object* v_resultType_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2321_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_a_2293_);
lean_dec_ref(v___x_2292_);
v_resultType_2294_ = lean_ctor_get(v_a_2261_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v_a_2261_);
if (v_isSharedCheck_2321_ == 0)
{
lean_object* v_unused_2322_; 
v_unused_2322_ = lean_ctor_get(v_a_2261_, 1);
lean_dec(v_unused_2322_);
v___x_2296_ = v_a_2261_;
v_isShared_2297_ = v_isSharedCheck_2321_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_resultType_2294_);
lean_dec(v_a_2261_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2321_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2298_; uint8_t v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2305_; 
v___x_2298_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__10___closed__2));
v___x_2299_ = 0;
v___x_2300_ = l_Lean_mkLambda(v___x_2298_, v___x_2299_, v_a_2286_, v_a_2288_);
v___x_2301_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__10___closed__6));
v___x_2302_ = l_Lean_Level_succ___override(v_v_2262_);
v___x_2303_ = lean_box(0);
if (v_isShared_2297_ == 0)
{
lean_ctor_set_tag(v___x_2296_, 1);
lean_ctor_set(v___x_2296_, 1, v___x_2303_);
lean_ctor_set(v___x_2296_, 0, v___x_2302_);
v___x_2305_ = v___x_2296_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2302_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v___x_2303_);
v___x_2305_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2306_, 0, v_u_2263_);
lean_ctor_set(v___x_2306_, 1, v___x_2305_);
v___x_2307_ = l_Lean_mkConst(v___x_2301_, v___x_2306_);
lean_inc_ref(v_resultType_2294_);
v___x_2308_ = l_Lean_mkApp3(v___x_2307_, v_resultType_2294_, v___x_2300_, v_ret_2277_);
v___x_2309_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(v_a_2293_, v_resultType_2294_, v___f_2264_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2319_; 
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2312_ = v___x_2309_;
v_isShared_2313_ = v_isSharedCheck_2319_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2309_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2319_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2317_; 
v___x_2314_ = l_Lean_mkSimpleThunk(v_a_2290_);
v___x_2315_ = l_Lean_mkAppB(v___x_2308_, v_a_2310_, v___x_2314_);
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 0, v___x_2315_);
v___x_2317_ = v___x_2312_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2315_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
else
{
lean_dec_ref(v___x_2308_);
lean_dec(v_a_2290_);
return v___x_2309_;
}
}
}
}
else
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2330_; 
lean_dec(v_a_2290_);
lean_dec(v_a_2288_);
lean_dec(v_a_2286_);
lean_dec_ref(v_ret_2277_);
lean_dec_ref(v___f_2264_);
lean_dec(v_u_2263_);
lean_dec(v_v_2262_);
lean_dec_ref(v_a_2261_);
v_a_2323_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2325_ = v___x_2292_;
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2292_);
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
lean_dec(v_a_2288_);
lean_dec(v_a_2286_);
lean_dec_ref(v_ret_2277_);
lean_dec_ref(v___f_2264_);
lean_dec(v_u_2263_);
lean_dec(v_v_2262_);
lean_dec_ref(v_a_2261_);
return v___x_2289_;
}
}
else
{
lean_dec(v_a_2286_);
lean_dec_ref(v_ret_2277_);
lean_dec_ref(v___f_2264_);
lean_dec(v_u_2263_);
lean_dec(v_v_2262_);
lean_dec_ref(v_a_2261_);
lean_dec_ref(v_dec_2258_);
return v___x_2287_;
}
}
else
{
lean_dec_ref(v_ret_2277_);
lean_dec_ref(v___f_2264_);
lean_dec(v_u_2263_);
lean_dec(v_v_2262_);
lean_dec_ref(v_a_2261_);
lean_dec_ref(v_doBlockResultType_2260_);
lean_dec_ref(v_dec_2258_);
return v___x_2285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___boxed(lean_object** _args){
lean_object* v_returnsEarly_2341_ = _args[0];
lean_object* v_dec_2342_ = _args[1];
lean_object* v_a_2343_ = _args[2];
lean_object* v_doBlockResultType_2344_ = _args[3];
lean_object* v_a_2345_ = _args[4];
lean_object* v_v_2346_ = _args[5];
lean_object* v_u_2347_ = _args[6];
lean_object* v___f_2348_ = _args[7];
lean_object* v___y_2349_ = _args[8];
lean_object* v___x_2350_ = _args[9];
lean_object* v___x_2351_ = _args[10];
lean_object* v___y_2352_ = _args[11];
lean_object* v___y_2353_ = _args[12];
lean_object* v___y_2354_ = _args[13];
lean_object* v___y_2355_ = _args[14];
lean_object* v___y_2356_ = _args[15];
lean_object* v___y_2357_ = _args[16];
lean_object* v___y_2358_ = _args[17];
lean_object* v___y_2359_ = _args[18];
_start:
{
uint8_t v_returnsEarly_boxed_2360_; lean_object* v_res_2361_; 
v_returnsEarly_boxed_2360_ = lean_unbox(v_returnsEarly_2341_);
v_res_2361_ = l_Lean_Elab_Do_elabDoFor___lam__10(v_returnsEarly_boxed_2360_, v_dec_2342_, v_a_2343_, v_doBlockResultType_2344_, v_a_2345_, v_v_2346_, v_u_2347_, v___f_2348_, v___y_2349_, v___x_2350_, v___x_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v___x_2351_);
lean_dec(v___x_2350_);
lean_dec_ref(v___y_2349_);
return v_res_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__11(lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___x_2364_, uint8_t v___x_2365_, lean_object* v_postS_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2375_ = l_Lean_Expr_fvarId_x21(v_postS_2366_);
v___x_2376_ = l_Lean_Elab_Do_bindMutVarsFromTuple(v___y_2362_, v___x_2375_, v___y_2363_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v_a_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; uint8_t v___x_2380_; uint8_t v___x_2381_; lean_object* v___x_2382_; 
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
lean_inc(v_a_2377_);
lean_dec_ref(v___x_2376_);
v___x_2378_ = lean_mk_empty_array_with_capacity(v___x_2364_);
v___x_2379_ = lean_array_push(v___x_2378_, v_postS_2366_);
v___x_2380_ = 0;
v___x_2381_ = 1;
v___x_2382_ = l_Lean_Meta_mkLambdaFVars(v___x_2379_, v_a_2377_, v___x_2380_, v___x_2365_, v___x_2380_, v___x_2365_, v___x_2381_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
lean_dec_ref(v___x_2379_);
return v___x_2382_;
}
else
{
lean_dec_ref(v_postS_2366_);
return v___x_2376_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__11___boxed(lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___x_2385_, lean_object* v___x_2386_, lean_object* v_postS_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
uint8_t v___x_82960__boxed_2396_; lean_object* v_res_2397_; 
v___x_82960__boxed_2396_ = lean_unbox(v___x_2386_);
v_res_2397_ = l_Lean_Elab_Do_elabDoFor___lam__11(v___y_2383_, v___y_2384_, v___x_2385_, v___x_82960__boxed_2396_, v_postS_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec_ref(v___y_2388_);
lean_dec(v___x_2385_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__12(lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v___x_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_val_2408_, lean_object* v_a_2409_, lean_object* v_x_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2419_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__12___closed__2));
v___x_2420_ = lean_box(0);
v___x_2421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2421_, 0, v_a_2403_);
lean_ctor_set(v___x_2421_, 1, v___x_2420_);
v___x_2422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2422_, 0, v_a_2404_);
lean_ctor_set(v___x_2422_, 1, v___x_2421_);
v___x_2423_ = l_Lean_mkConst(v___x_2419_, v___x_2422_);
v___x_2424_ = l_Lean_instInhabitedExpr;
v___x_2425_ = lean_array_get_borrowed(v___x_2424_, v_x_2410_, v___x_2405_);
lean_inc(v___x_2425_);
v___x_2426_ = l_Lean_mkApp5(v___x_2423_, v_a_2406_, v_a_2407_, v_val_2408_, v_a_2409_, v___x_2425_);
v___x_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2426_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__12___boxed(lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v___x_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_val_2433_, lean_object* v_a_2434_, lean_object* v_x_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Lean_Elab_Do_elabDoFor___lam__12(v_a_2428_, v_a_2429_, v___x_2430_, v_a_2431_, v_a_2432_, v_val_2433_, v_a_2434_, v_x_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec_ref(v_x_2435_);
lean_dec(v___x_2430_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__0(lean_object* v___x_2445_, lean_object* v_a_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v___x_2455_; lean_object* v___x_81262__overap_2456_; lean_object* v___x_2457_; 
v___x_2455_ = l_Lean_instInhabitedExpr;
v___x_81262__overap_2456_ = l_instInhabitedOfMonad___redArg(v___x_2445_, v___x_2455_);
lean_inc(v___y_2453_);
lean_inc_ref(v___y_2452_);
lean_inc(v___y_2451_);
lean_inc_ref(v___y_2450_);
lean_inc(v___y_2449_);
lean_inc_ref(v___y_2448_);
lean_inc_ref(v___y_2447_);
v___x_2457_ = lean_apply_8(v___x_81262__overap_2456_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, lean_box(0));
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__0___boxed(lean_object* v___x_2458_, lean_object* v_a_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__0(v___x_2458_, v_a_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_);
lean_dec(v___y_2466_);
lean_dec_ref(v___y_2465_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec_ref(v_a_2459_);
return v_res_2468_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2469_; 
v___x_2469_ = l_instMonadEIO(lean_box(0));
return v___x_2469_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1(void){
_start:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2470_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0);
v___x_2471_ = l_StateRefT_x27_instMonad___redArg(v___x_2470_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__1___boxed(lean_object* v_acc_2478_, lean_object* v_declInfos_2479_, lean_object* v_k_2480_, lean_object* v_kind_2481_, lean_object* v_x_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
uint8_t v_kind_boxed_2491_; lean_object* v_res_2492_; 
v_kind_boxed_2491_ = lean_unbox(v_kind_2481_);
v_res_2492_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__1(v_acc_2478_, v_declInfos_2479_, v_k_2480_, v_kind_boxed_2491_, v_x_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec_ref(v___y_2483_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(lean_object* v_declInfos_2493_, lean_object* v_k_2494_, uint8_t v_kind_2495_, lean_object* v_acc_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_){
_start:
{
lean_object* v___x_2505_; lean_object* v_toApplicative_2506_; lean_object* v_toFunctor_2507_; lean_object* v_toSeq_2508_; lean_object* v_toSeqLeft_2509_; lean_object* v_toSeqRight_2510_; lean_object* v___f_2511_; lean_object* v___f_2512_; lean_object* v___f_2513_; lean_object* v___f_2514_; lean_object* v___x_2515_; lean_object* v___f_2516_; lean_object* v___f_2517_; lean_object* v___f_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v_toApplicative_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2602_; 
v___x_2505_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1);
v_toApplicative_2506_ = lean_ctor_get(v___x_2505_, 0);
v_toFunctor_2507_ = lean_ctor_get(v_toApplicative_2506_, 0);
v_toSeq_2508_ = lean_ctor_get(v_toApplicative_2506_, 2);
v_toSeqLeft_2509_ = lean_ctor_get(v_toApplicative_2506_, 3);
v_toSeqRight_2510_ = lean_ctor_get(v_toApplicative_2506_, 4);
v___f_2511_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__2));
v___f_2512_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__3));
lean_inc_ref_n(v_toFunctor_2507_, 2);
v___f_2513_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2513_, 0, v_toFunctor_2507_);
v___f_2514_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2514_, 0, v_toFunctor_2507_);
v___x_2515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2515_, 0, v___f_2513_);
lean_ctor_set(v___x_2515_, 1, v___f_2514_);
lean_inc(v_toSeqRight_2510_);
v___f_2516_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2516_, 0, v_toSeqRight_2510_);
lean_inc(v_toSeqLeft_2509_);
v___f_2517_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2517_, 0, v_toSeqLeft_2509_);
lean_inc(v_toSeq_2508_);
v___f_2518_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2518_, 0, v_toSeq_2508_);
v___x_2519_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2515_);
lean_ctor_set(v___x_2519_, 1, v___f_2511_);
lean_ctor_set(v___x_2519_, 2, v___f_2518_);
lean_ctor_set(v___x_2519_, 3, v___f_2517_);
lean_ctor_set(v___x_2519_, 4, v___f_2516_);
v___x_2520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2519_);
lean_ctor_set(v___x_2520_, 1, v___f_2512_);
v___x_2521_ = l_StateRefT_x27_instMonad___redArg(v___x_2520_);
v_toApplicative_2522_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2602_ == 0)
{
lean_object* v_unused_2603_; 
v_unused_2603_ = lean_ctor_get(v___x_2521_, 1);
lean_dec(v_unused_2603_);
v___x_2524_ = v___x_2521_;
v_isShared_2525_ = v_isSharedCheck_2602_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_toApplicative_2522_);
lean_dec(v___x_2521_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2602_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v_toFunctor_2526_; lean_object* v_toSeq_2527_; lean_object* v_toSeqLeft_2528_; lean_object* v_toSeqRight_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2600_; 
v_toFunctor_2526_ = lean_ctor_get(v_toApplicative_2522_, 0);
v_toSeq_2527_ = lean_ctor_get(v_toApplicative_2522_, 2);
v_toSeqLeft_2528_ = lean_ctor_get(v_toApplicative_2522_, 3);
v_toSeqRight_2529_ = lean_ctor_get(v_toApplicative_2522_, 4);
v_isSharedCheck_2600_ = !lean_is_exclusive(v_toApplicative_2522_);
if (v_isSharedCheck_2600_ == 0)
{
lean_object* v_unused_2601_; 
v_unused_2601_ = lean_ctor_get(v_toApplicative_2522_, 1);
lean_dec(v_unused_2601_);
v___x_2531_ = v_toApplicative_2522_;
v_isShared_2532_ = v_isSharedCheck_2600_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_toSeqRight_2529_);
lean_inc(v_toSeqLeft_2528_);
lean_inc(v_toSeq_2527_);
lean_inc(v_toFunctor_2526_);
lean_dec(v_toApplicative_2522_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2600_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___f_2533_; lean_object* v___f_2534_; lean_object* v___f_2535_; lean_object* v___f_2536_; lean_object* v___x_2537_; lean_object* v___f_2538_; lean_object* v___f_2539_; lean_object* v___f_2540_; lean_object* v___x_2542_; 
v___f_2533_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__4));
v___f_2534_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__5));
lean_inc_ref(v_toFunctor_2526_);
v___f_2535_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2535_, 0, v_toFunctor_2526_);
v___f_2536_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2536_, 0, v_toFunctor_2526_);
v___x_2537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___f_2535_);
lean_ctor_set(v___x_2537_, 1, v___f_2536_);
v___f_2538_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2538_, 0, v_toSeqRight_2529_);
v___f_2539_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2539_, 0, v_toSeqLeft_2528_);
v___f_2540_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2540_, 0, v_toSeq_2527_);
if (v_isShared_2532_ == 0)
{
lean_ctor_set(v___x_2531_, 4, v___f_2538_);
lean_ctor_set(v___x_2531_, 3, v___f_2539_);
lean_ctor_set(v___x_2531_, 2, v___f_2540_);
lean_ctor_set(v___x_2531_, 1, v___f_2533_);
lean_ctor_set(v___x_2531_, 0, v___x_2537_);
v___x_2542_ = v___x_2531_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2537_);
lean_ctor_set(v_reuseFailAlloc_2599_, 1, v___f_2533_);
lean_ctor_set(v_reuseFailAlloc_2599_, 2, v___f_2540_);
lean_ctor_set(v_reuseFailAlloc_2599_, 3, v___f_2539_);
lean_ctor_set(v_reuseFailAlloc_2599_, 4, v___f_2538_);
v___x_2542_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
lean_object* v___x_2544_; 
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 1, v___f_2534_);
lean_ctor_set(v___x_2524_, 0, v___x_2542_);
v___x_2544_ = v___x_2524_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2542_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v___f_2534_);
v___x_2544_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
lean_object* v___x_2545_; lean_object* v_toApplicative_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2596_; 
v___x_2545_ = l_StateRefT_x27_instMonad___redArg(v___x_2544_);
v_toApplicative_2546_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2596_ == 0)
{
lean_object* v_unused_2597_; 
v_unused_2597_ = lean_ctor_get(v___x_2545_, 1);
lean_dec(v_unused_2597_);
v___x_2548_ = v___x_2545_;
v_isShared_2549_ = v_isSharedCheck_2596_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_toApplicative_2546_);
lean_dec(v___x_2545_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2596_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v_toFunctor_2550_; lean_object* v_toSeq_2551_; lean_object* v_toSeqLeft_2552_; lean_object* v_toSeqRight_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2594_; 
v_toFunctor_2550_ = lean_ctor_get(v_toApplicative_2546_, 0);
v_toSeq_2551_ = lean_ctor_get(v_toApplicative_2546_, 2);
v_toSeqLeft_2552_ = lean_ctor_get(v_toApplicative_2546_, 3);
v_toSeqRight_2553_ = lean_ctor_get(v_toApplicative_2546_, 4);
v_isSharedCheck_2594_ = !lean_is_exclusive(v_toApplicative_2546_);
if (v_isSharedCheck_2594_ == 0)
{
lean_object* v_unused_2595_; 
v_unused_2595_ = lean_ctor_get(v_toApplicative_2546_, 1);
lean_dec(v_unused_2595_);
v___x_2555_ = v_toApplicative_2546_;
v_isShared_2556_ = v_isSharedCheck_2594_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_toSeqRight_2553_);
lean_inc(v_toSeqLeft_2552_);
lean_inc(v_toSeq_2551_);
lean_inc(v_toFunctor_2550_);
lean_dec(v_toApplicative_2546_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2594_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___f_2557_; lean_object* v___f_2558_; lean_object* v___f_2559_; lean_object* v___f_2560_; lean_object* v___x_2561_; lean_object* v___f_2562_; lean_object* v___f_2563_; lean_object* v___f_2564_; lean_object* v___x_2566_; 
v___f_2557_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__6));
v___f_2558_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__7));
lean_inc_ref(v_toFunctor_2550_);
v___f_2559_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2559_, 0, v_toFunctor_2550_);
v___f_2560_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2560_, 0, v_toFunctor_2550_);
v___x_2561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2561_, 0, v___f_2559_);
lean_ctor_set(v___x_2561_, 1, v___f_2560_);
v___f_2562_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2562_, 0, v_toSeqRight_2553_);
v___f_2563_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2563_, 0, v_toSeqLeft_2552_);
v___f_2564_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2564_, 0, v_toSeq_2551_);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 4, v___f_2562_);
lean_ctor_set(v___x_2555_, 3, v___f_2563_);
lean_ctor_set(v___x_2555_, 2, v___f_2564_);
lean_ctor_set(v___x_2555_, 1, v___f_2557_);
lean_ctor_set(v___x_2555_, 0, v___x_2561_);
v___x_2566_ = v___x_2555_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v___x_2561_);
lean_ctor_set(v_reuseFailAlloc_2593_, 1, v___f_2557_);
lean_ctor_set(v_reuseFailAlloc_2593_, 2, v___f_2564_);
lean_ctor_set(v_reuseFailAlloc_2593_, 3, v___f_2563_);
lean_ctor_set(v_reuseFailAlloc_2593_, 4, v___f_2562_);
v___x_2566_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
lean_object* v___x_2568_; 
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 1, v___f_2558_);
lean_ctor_set(v___x_2548_, 0, v___x_2566_);
v___x_2568_ = v___x_2548_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v___x_2566_);
lean_ctor_set(v_reuseFailAlloc_2592_, 1, v___f_2558_);
v___x_2568_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; uint8_t v___x_2572_; 
v___x_2569_ = l_ReaderT_instMonad___redArg(v___x_2568_);
v___x_2570_ = lean_array_get_size(v_acc_2496_);
v___x_2571_ = lean_array_get_size(v_declInfos_2493_);
v___x_2572_ = lean_nat_dec_lt(v___x_2570_, v___x_2571_);
if (v___x_2572_ == 0)
{
lean_object* v___x_2573_; 
lean_dec_ref(v___x_2569_);
lean_dec_ref(v_declInfos_2493_);
lean_inc(v___y_2503_);
lean_inc_ref(v___y_2502_);
lean_inc(v___y_2501_);
lean_inc_ref(v___y_2500_);
lean_inc(v___y_2499_);
lean_inc_ref(v___y_2498_);
lean_inc_ref(v___y_2497_);
v___x_2573_ = lean_apply_9(v_k_2494_, v_acc_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, lean_box(0));
return v___x_2573_;
}
else
{
lean_object* v___f_2574_; lean_object* v___x_2575_; uint8_t v___x_2576_; lean_object* v___f_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v_snd_2582_; lean_object* v_fst_2583_; lean_object* v_fst_2584_; lean_object* v_snd_2585_; lean_object* v___x_2586_; 
v___f_2574_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2574_, 0, v___x_2569_);
v___x_2575_ = lean_box(0);
v___x_2576_ = 0;
v___f_2577_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2577_, 0, v___f_2574_);
v___x_2578_ = lean_box(v___x_2576_);
v___x_2579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2578_);
lean_ctor_set(v___x_2579_, 1, v___f_2577_);
v___x_2580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2575_);
lean_ctor_set(v___x_2580_, 1, v___x_2579_);
v___x_2581_ = lean_array_get(v___x_2580_, v_declInfos_2493_, v___x_2570_);
lean_dec_ref(v___x_2580_);
v_snd_2582_ = lean_ctor_get(v___x_2581_, 1);
lean_inc(v_snd_2582_);
v_fst_2583_ = lean_ctor_get(v___x_2581_, 0);
lean_inc(v_fst_2583_);
lean_dec(v___x_2581_);
v_fst_2584_ = lean_ctor_get(v_snd_2582_, 0);
lean_inc(v_fst_2584_);
v_snd_2585_ = lean_ctor_get(v_snd_2582_, 1);
lean_inc(v_snd_2585_);
lean_dec(v_snd_2582_);
lean_inc(v___y_2503_);
lean_inc_ref(v___y_2502_);
lean_inc(v___y_2501_);
lean_inc_ref(v___y_2500_);
lean_inc(v___y_2499_);
lean_inc_ref(v___y_2498_);
lean_inc_ref(v___y_2497_);
lean_inc_ref(v_acc_2496_);
v___x_2586_ = lean_apply_9(v_snd_2585_, v_acc_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, lean_box(0));
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; lean_object* v___x_2588_; lean_object* v___f_2589_; uint8_t v___x_2590_; lean_object* v___x_2591_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_a_2587_);
lean_dec_ref(v___x_2586_);
v___x_2588_ = lean_box(v_kind_2495_);
v___f_2589_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__1___boxed), 13, 4);
lean_closure_set(v___f_2589_, 0, v_acc_2496_);
lean_closure_set(v___f_2589_, 1, v_declInfos_2493_);
lean_closure_set(v___f_2589_, 2, v_k_2494_);
lean_closure_set(v___f_2589_, 3, v___x_2588_);
v___x_2590_ = lean_unbox(v_fst_2584_);
lean_dec(v_fst_2584_);
v___x_2591_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_fst_2583_, v___x_2590_, v_a_2587_, v___f_2589_, v_kind_2495_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
return v___x_2591_;
}
else
{
lean_dec(v_fst_2584_);
lean_dec(v_fst_2583_);
lean_dec_ref(v_acc_2496_);
lean_dec_ref(v_k_2494_);
lean_dec_ref(v_declInfos_2493_);
return v___x_2586_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__1(lean_object* v_acc_2604_, lean_object* v_declInfos_2605_, lean_object* v_k_2606_, uint8_t v_kind_2607_, lean_object* v_x_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_){
_start:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2617_ = lean_array_push(v_acc_2604_, v_x_2608_);
v___x_2618_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(v_declInfos_2605_, v_k_2606_, v_kind_2607_, v___x_2617_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___boxed(lean_object* v_declInfos_2619_, lean_object* v_k_2620_, lean_object* v_kind_2621_, lean_object* v_acc_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
uint8_t v_kind_boxed_2631_; lean_object* v_res_2632_; 
v_kind_boxed_2631_ = lean_unbox(v_kind_2621_);
v_res_2632_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(v_declInfos_2619_, v_k_2620_, v_kind_boxed_2631_, v_acc_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec_ref(v___y_2623_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7(lean_object* v_declInfos_2635_, lean_object* v_k_2636_, uint8_t v_kind_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2646_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___closed__0));
v___x_2647_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(v_declInfos_2635_, v_k_2636_, v_kind_2637_, v___x_2646_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___boxed(lean_object* v_declInfos_2648_, lean_object* v_k_2649_, lean_object* v_kind_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
uint8_t v_kind_boxed_2659_; lean_object* v_res_2660_; 
v_kind_boxed_2659_ = lean_unbox(v_kind_2650_);
v_res_2660_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7(v_declInfos_2648_, v_k_2649_, v_kind_boxed_2659_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec_ref(v___y_2651_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(size_t v_sz_2661_, size_t v_i_2662_, lean_object* v_bs_2663_){
_start:
{
uint8_t v___x_2664_; 
v___x_2664_ = lean_usize_dec_lt(v_i_2662_, v_sz_2661_);
if (v___x_2664_ == 0)
{
return v_bs_2663_;
}
else
{
lean_object* v_v_2665_; lean_object* v_fst_2666_; lean_object* v_snd_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2683_; 
v_v_2665_ = lean_array_uget(v_bs_2663_, v_i_2662_);
v_fst_2666_ = lean_ctor_get(v_v_2665_, 0);
v_snd_2667_ = lean_ctor_get(v_v_2665_, 1);
v_isSharedCheck_2683_ = !lean_is_exclusive(v_v_2665_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2669_ = v_v_2665_;
v_isShared_2670_ = v_isSharedCheck_2683_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_snd_2667_);
lean_inc(v_fst_2666_);
lean_dec(v_v_2665_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2683_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2671_; lean_object* v_bs_x27_2672_; uint8_t v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2676_; 
v___x_2671_ = lean_unsigned_to_nat(0u);
v_bs_x27_2672_ = lean_array_uset(v_bs_2663_, v_i_2662_, v___x_2671_);
v___x_2673_ = 0;
v___x_2674_ = lean_box(v___x_2673_);
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 0, v___x_2674_);
v___x_2676_ = v___x_2669_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v___x_2674_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v_snd_2667_);
v___x_2676_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
lean_object* v___x_2677_; size_t v___x_2678_; size_t v___x_2679_; lean_object* v___x_2680_; 
v___x_2677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2677_, 0, v_fst_2666_);
lean_ctor_set(v___x_2677_, 1, v___x_2676_);
v___x_2678_ = ((size_t)1ULL);
v___x_2679_ = lean_usize_add(v_i_2662_, v___x_2678_);
v___x_2680_ = lean_array_uset(v_bs_x27_2672_, v_i_2662_, v___x_2677_);
v_i_2662_ = v___x_2679_;
v_bs_2663_ = v___x_2680_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6___boxed(lean_object* v_sz_2684_, lean_object* v_i_2685_, lean_object* v_bs_2686_){
_start:
{
size_t v_sz_boxed_2687_; size_t v_i_boxed_2688_; lean_object* v_res_2689_; 
v_sz_boxed_2687_ = lean_unbox_usize(v_sz_2684_);
lean_dec(v_sz_2684_);
v_i_boxed_2688_ = lean_unbox_usize(v_i_2685_);
lean_dec(v_i_2685_);
v_res_2689_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(v_sz_boxed_2687_, v_i_boxed_2688_, v_bs_2686_);
return v_res_2689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(lean_object* v_declInfos_2690_, lean_object* v_k_2691_, uint8_t v_kind_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
size_t v_sz_2701_; size_t v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v_sz_2701_ = lean_array_size(v_declInfos_2690_);
v___x_2702_ = ((size_t)0ULL);
v___x_2703_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(v_sz_2701_, v___x_2702_, v_declInfos_2690_);
v___x_2704_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7(v___x_2703_, v_k_2691_, v_kind_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_);
return v___x_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4___boxed(lean_object* v_declInfos_2705_, lean_object* v_k_2706_, lean_object* v_kind_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
uint8_t v_kind_boxed_2716_; lean_object* v_res_2717_; 
v_kind_boxed_2716_ = lean_unbox(v_kind_2707_);
v_res_2717_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(v_declInfos_2705_, v_k_2706_, v_kind_boxed_2716_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec_ref(v___y_2708_);
return v_res_2717_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0(uint8_t v___y_2725_, uint8_t v_suppressElabErrors_2726_, lean_object* v_x_2727_){
_start:
{
if (lean_obj_tag(v_x_2727_) == 1)
{
lean_object* v_pre_2728_; 
v_pre_2728_ = lean_ctor_get(v_x_2727_, 0);
switch(lean_obj_tag(v_pre_2728_))
{
case 1:
{
lean_object* v_pre_2729_; 
v_pre_2729_ = lean_ctor_get(v_pre_2728_, 0);
switch(lean_obj_tag(v_pre_2729_))
{
case 0:
{
lean_object* v_str_2730_; lean_object* v_str_2731_; lean_object* v___x_2732_; uint8_t v___x_2733_; 
v_str_2730_ = lean_ctor_get(v_x_2727_, 1);
v_str_2731_ = lean_ctor_get(v_pre_2728_, 1);
v___x_2732_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66));
v___x_2733_ = lean_string_dec_eq(v_str_2731_, v___x_2732_);
if (v___x_2733_ == 0)
{
lean_object* v___x_2734_; uint8_t v___x_2735_; 
v___x_2734_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__0));
v___x_2735_ = lean_string_dec_eq(v_str_2731_, v___x_2734_);
if (v___x_2735_ == 0)
{
return v___y_2725_;
}
else
{
lean_object* v___x_2736_; uint8_t v___x_2737_; 
v___x_2736_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__1));
v___x_2737_ = lean_string_dec_eq(v_str_2730_, v___x_2736_);
if (v___x_2737_ == 0)
{
return v___y_2725_;
}
else
{
return v_suppressElabErrors_2726_;
}
}
}
else
{
lean_object* v___x_2738_; uint8_t v___x_2739_; 
v___x_2738_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__2));
v___x_2739_ = lean_string_dec_eq(v_str_2730_, v___x_2738_);
if (v___x_2739_ == 0)
{
return v___y_2725_;
}
else
{
return v_suppressElabErrors_2726_;
}
}
}
case 1:
{
lean_object* v_pre_2740_; 
v_pre_2740_ = lean_ctor_get(v_pre_2729_, 0);
if (lean_obj_tag(v_pre_2740_) == 0)
{
lean_object* v_str_2741_; lean_object* v_str_2742_; lean_object* v_str_2743_; lean_object* v___x_2744_; uint8_t v___x_2745_; 
v_str_2741_ = lean_ctor_get(v_x_2727_, 1);
v_str_2742_ = lean_ctor_get(v_pre_2728_, 1);
v_str_2743_ = lean_ctor_get(v_pre_2729_, 1);
v___x_2744_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__3));
v___x_2745_ = lean_string_dec_eq(v_str_2743_, v___x_2744_);
if (v___x_2745_ == 0)
{
return v___y_2725_;
}
else
{
lean_object* v___x_2746_; uint8_t v___x_2747_; 
v___x_2746_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__4));
v___x_2747_ = lean_string_dec_eq(v_str_2742_, v___x_2746_);
if (v___x_2747_ == 0)
{
return v___y_2725_;
}
else
{
lean_object* v___x_2748_; uint8_t v___x_2749_; 
v___x_2748_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__5));
v___x_2749_ = lean_string_dec_eq(v_str_2741_, v___x_2748_);
if (v___x_2749_ == 0)
{
return v___y_2725_;
}
else
{
return v_suppressElabErrors_2726_;
}
}
}
}
else
{
return v___y_2725_;
}
}
default: 
{
return v___y_2725_;
}
}
}
case 0:
{
lean_object* v_str_2750_; lean_object* v___x_2751_; uint8_t v___x_2752_; 
v_str_2750_ = lean_ctor_get(v_x_2727_, 1);
v___x_2751_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___closed__6));
v___x_2752_ = lean_string_dec_eq(v_str_2750_, v___x_2751_);
if (v___x_2752_ == 0)
{
return v___y_2725_;
}
else
{
return v_suppressElabErrors_2726_;
}
}
default: 
{
return v___y_2725_;
}
}
}
else
{
return v___y_2725_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___boxed(lean_object* v___y_2753_, lean_object* v_suppressElabErrors_2754_, lean_object* v_x_2755_){
_start:
{
uint8_t v___y_83482__boxed_2756_; uint8_t v_suppressElabErrors_boxed_2757_; uint8_t v_res_2758_; lean_object* v_r_2759_; 
v___y_83482__boxed_2756_ = lean_unbox(v___y_2753_);
v_suppressElabErrors_boxed_2757_ = lean_unbox(v_suppressElabErrors_2754_);
v_res_2758_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0(v___y_83482__boxed_2756_, v_suppressElabErrors_boxed_2757_, v_x_2755_);
lean_dec(v_x_2755_);
v_r_2759_ = lean_box(v_res_2758_);
return v_r_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg(lean_object* v_ref_2760_, lean_object* v_msgData_2761_, uint8_t v_severity_2762_, uint8_t v_isSilent_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v___y_2770_; lean_object* v___y_2771_; uint8_t v___y_2772_; uint8_t v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2806_; lean_object* v___y_2807_; uint8_t v___y_2808_; lean_object* v___y_2809_; uint8_t v___y_2810_; lean_object* v___y_2811_; uint8_t v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; uint8_t v___y_2834_; uint8_t v___y_2835_; lean_object* v___y_2836_; uint8_t v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; uint8_t v___y_2845_; lean_object* v___y_2846_; uint8_t v___y_2847_; uint8_t v___y_2848_; uint8_t v___x_2853_; lean_object* v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; uint8_t v___y_2859_; uint8_t v___y_2860_; uint8_t v___y_2861_; uint8_t v___y_2863_; uint8_t v___x_2878_; 
v___x_2853_ = 2;
v___x_2878_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2762_, v___x_2853_);
if (v___x_2878_ == 0)
{
v___y_2863_ = v___x_2878_;
goto v___jp_2862_;
}
else
{
uint8_t v___x_2879_; 
lean_inc_ref(v_msgData_2761_);
v___x_2879_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2761_);
v___y_2863_ = v___x_2879_;
goto v___jp_2862_;
}
v___jp_2769_:
{
lean_object* v___x_2779_; lean_object* v_currNamespace_2780_; lean_object* v_openDecls_2781_; lean_object* v_env_2782_; lean_object* v_nextMacroScope_2783_; lean_object* v_ngen_2784_; lean_object* v_auxDeclNGen_2785_; lean_object* v_traceState_2786_; lean_object* v_cache_2787_; lean_object* v_messages_2788_; lean_object* v_infoState_2789_; lean_object* v_snapshotTasks_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2804_; 
v___x_2779_ = lean_st_ref_take(v___y_2778_);
v_currNamespace_2780_ = lean_ctor_get(v___y_2777_, 6);
v_openDecls_2781_ = lean_ctor_get(v___y_2777_, 7);
v_env_2782_ = lean_ctor_get(v___x_2779_, 0);
v_nextMacroScope_2783_ = lean_ctor_get(v___x_2779_, 1);
v_ngen_2784_ = lean_ctor_get(v___x_2779_, 2);
v_auxDeclNGen_2785_ = lean_ctor_get(v___x_2779_, 3);
v_traceState_2786_ = lean_ctor_get(v___x_2779_, 4);
v_cache_2787_ = lean_ctor_get(v___x_2779_, 5);
v_messages_2788_ = lean_ctor_get(v___x_2779_, 6);
v_infoState_2789_ = lean_ctor_get(v___x_2779_, 7);
v_snapshotTasks_2790_ = lean_ctor_get(v___x_2779_, 8);
v_isSharedCheck_2804_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2792_ = v___x_2779_;
v_isShared_2793_ = v_isSharedCheck_2804_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_snapshotTasks_2790_);
lean_inc(v_infoState_2789_);
lean_inc(v_messages_2788_);
lean_inc(v_cache_2787_);
lean_inc(v_traceState_2786_);
lean_inc(v_auxDeclNGen_2785_);
lean_inc(v_ngen_2784_);
lean_inc(v_nextMacroScope_2783_);
lean_inc(v_env_2782_);
lean_dec(v___x_2779_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2804_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2799_; 
lean_inc(v_openDecls_2781_);
lean_inc(v_currNamespace_2780_);
v___x_2794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2794_, 0, v_currNamespace_2780_);
lean_ctor_set(v___x_2794_, 1, v_openDecls_2781_);
v___x_2795_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2794_);
lean_ctor_set(v___x_2795_, 1, v___y_2770_);
lean_inc_ref(v___y_2776_);
lean_inc_ref(v___y_2775_);
v___x_2796_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2796_, 0, v___y_2775_);
lean_ctor_set(v___x_2796_, 1, v___y_2771_);
lean_ctor_set(v___x_2796_, 2, v___y_2774_);
lean_ctor_set(v___x_2796_, 3, v___y_2776_);
lean_ctor_set(v___x_2796_, 4, v___x_2795_);
lean_ctor_set_uint8(v___x_2796_, sizeof(void*)*5, v___y_2773_);
lean_ctor_set_uint8(v___x_2796_, sizeof(void*)*5 + 1, v___y_2772_);
lean_ctor_set_uint8(v___x_2796_, sizeof(void*)*5 + 2, v_isSilent_2763_);
v___x_2797_ = l_Lean_MessageLog_add(v___x_2796_, v_messages_2788_);
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 6, v___x_2797_);
v___x_2799_ = v___x_2792_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v_env_2782_);
lean_ctor_set(v_reuseFailAlloc_2803_, 1, v_nextMacroScope_2783_);
lean_ctor_set(v_reuseFailAlloc_2803_, 2, v_ngen_2784_);
lean_ctor_set(v_reuseFailAlloc_2803_, 3, v_auxDeclNGen_2785_);
lean_ctor_set(v_reuseFailAlloc_2803_, 4, v_traceState_2786_);
lean_ctor_set(v_reuseFailAlloc_2803_, 5, v_cache_2787_);
lean_ctor_set(v_reuseFailAlloc_2803_, 6, v___x_2797_);
lean_ctor_set(v_reuseFailAlloc_2803_, 7, v_infoState_2789_);
lean_ctor_set(v_reuseFailAlloc_2803_, 8, v_snapshotTasks_2790_);
v___x_2799_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2800_ = lean_st_ref_set(v___y_2778_, v___x_2799_);
v___x_2801_ = lean_box(0);
v___x_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2801_);
return v___x_2802_;
}
}
}
v___jp_2805_:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2829_; 
v___x_2814_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2761_);
v___x_2815_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(v___x_2814_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_);
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2818_ = v___x_2815_;
v_isShared_2819_ = v_isSharedCheck_2829_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2815_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2829_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
lean_inc_ref_n(v___y_2807_, 2);
v___x_2820_ = l_Lean_FileMap_toPosition(v___y_2807_, v___y_2809_);
lean_dec(v___y_2809_);
v___x_2821_ = l_Lean_FileMap_toPosition(v___y_2807_, v___y_2813_);
lean_dec(v___y_2813_);
v___x_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2821_);
v___x_2823_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__64));
if (v___y_2812_ == 0)
{
lean_del_object(v___x_2818_);
lean_dec_ref(v___y_2806_);
v___y_2770_ = v_a_2816_;
v___y_2771_ = v___x_2820_;
v___y_2772_ = v___y_2808_;
v___y_2773_ = v___y_2810_;
v___y_2774_ = v___x_2822_;
v___y_2775_ = v___y_2811_;
v___y_2776_ = v___x_2823_;
v___y_2777_ = v___y_2766_;
v___y_2778_ = v___y_2767_;
goto v___jp_2769_;
}
else
{
uint8_t v___x_2824_; 
lean_inc(v_a_2816_);
v___x_2824_ = l_Lean_MessageData_hasTag(v___y_2806_, v_a_2816_);
if (v___x_2824_ == 0)
{
lean_object* v___x_2825_; lean_object* v___x_2827_; 
lean_dec_ref(v___x_2822_);
lean_dec_ref(v___x_2820_);
lean_dec(v_a_2816_);
v___x_2825_ = lean_box(0);
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 0, v___x_2825_);
v___x_2827_ = v___x_2818_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v___x_2825_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
else
{
lean_del_object(v___x_2818_);
v___y_2770_ = v_a_2816_;
v___y_2771_ = v___x_2820_;
v___y_2772_ = v___y_2808_;
v___y_2773_ = v___y_2810_;
v___y_2774_ = v___x_2822_;
v___y_2775_ = v___y_2811_;
v___y_2776_ = v___x_2823_;
v___y_2777_ = v___y_2766_;
v___y_2778_ = v___y_2767_;
goto v___jp_2769_;
}
}
}
}
v___jp_2830_:
{
lean_object* v___x_2839_; 
v___x_2839_ = l_Lean_Syntax_getTailPos_x3f(v___y_2833_, v___y_2835_);
lean_dec(v___y_2833_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_inc(v___y_2838_);
v___y_2806_ = v___y_2831_;
v___y_2807_ = v___y_2832_;
v___y_2808_ = v___y_2834_;
v___y_2809_ = v___y_2838_;
v___y_2810_ = v___y_2835_;
v___y_2811_ = v___y_2836_;
v___y_2812_ = v___y_2837_;
v___y_2813_ = v___y_2838_;
goto v___jp_2805_;
}
else
{
lean_object* v_val_2840_; 
v_val_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_val_2840_);
lean_dec_ref(v___x_2839_);
v___y_2806_ = v___y_2831_;
v___y_2807_ = v___y_2832_;
v___y_2808_ = v___y_2834_;
v___y_2809_ = v___y_2838_;
v___y_2810_ = v___y_2835_;
v___y_2811_ = v___y_2836_;
v___y_2812_ = v___y_2837_;
v___y_2813_ = v_val_2840_;
goto v___jp_2805_;
}
}
v___jp_2841_:
{
lean_object* v_ref_2849_; lean_object* v___x_2850_; 
v_ref_2849_ = l_Lean_replaceRef(v_ref_2760_, v___y_2844_);
v___x_2850_ = l_Lean_Syntax_getPos_x3f(v_ref_2849_, v___y_2845_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v___x_2851_; 
v___x_2851_ = lean_unsigned_to_nat(0u);
v___y_2831_ = v___y_2842_;
v___y_2832_ = v___y_2843_;
v___y_2833_ = v_ref_2849_;
v___y_2834_ = v___y_2848_;
v___y_2835_ = v___y_2845_;
v___y_2836_ = v___y_2846_;
v___y_2837_ = v___y_2847_;
v___y_2838_ = v___x_2851_;
goto v___jp_2830_;
}
else
{
lean_object* v_val_2852_; 
v_val_2852_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_val_2852_);
lean_dec_ref(v___x_2850_);
v___y_2831_ = v___y_2842_;
v___y_2832_ = v___y_2843_;
v___y_2833_ = v_ref_2849_;
v___y_2834_ = v___y_2848_;
v___y_2835_ = v___y_2845_;
v___y_2836_ = v___y_2846_;
v___y_2837_ = v___y_2847_;
v___y_2838_ = v_val_2852_;
goto v___jp_2830_;
}
}
v___jp_2854_:
{
if (v___y_2861_ == 0)
{
v___y_2842_ = v___y_2857_;
v___y_2843_ = v___y_2856_;
v___y_2844_ = v___y_2855_;
v___y_2845_ = v___y_2860_;
v___y_2846_ = v___y_2858_;
v___y_2847_ = v___y_2859_;
v___y_2848_ = v_severity_2762_;
goto v___jp_2841_;
}
else
{
v___y_2842_ = v___y_2857_;
v___y_2843_ = v___y_2856_;
v___y_2844_ = v___y_2855_;
v___y_2845_ = v___y_2860_;
v___y_2846_ = v___y_2858_;
v___y_2847_ = v___y_2859_;
v___y_2848_ = v___x_2853_;
goto v___jp_2841_;
}
}
v___jp_2862_:
{
if (v___y_2863_ == 0)
{
lean_object* v_fileName_2864_; lean_object* v_fileMap_2865_; lean_object* v_options_2866_; lean_object* v_ref_2867_; uint8_t v_suppressElabErrors_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___f_2871_; uint8_t v___x_2872_; uint8_t v___x_2873_; 
v_fileName_2864_ = lean_ctor_get(v___y_2766_, 0);
v_fileMap_2865_ = lean_ctor_get(v___y_2766_, 1);
v_options_2866_ = lean_ctor_get(v___y_2766_, 2);
v_ref_2867_ = lean_ctor_get(v___y_2766_, 5);
v_suppressElabErrors_2868_ = lean_ctor_get_uint8(v___y_2766_, sizeof(void*)*14 + 1);
v___x_2869_ = lean_box(v___y_2863_);
v___x_2870_ = lean_box(v_suppressElabErrors_2868_);
v___f_2871_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2871_, 0, v___x_2869_);
lean_closure_set(v___f_2871_, 1, v___x_2870_);
v___x_2872_ = 1;
v___x_2873_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2762_, v___x_2872_);
if (v___x_2873_ == 0)
{
v___y_2855_ = v_ref_2867_;
v___y_2856_ = v_fileMap_2865_;
v___y_2857_ = v___f_2871_;
v___y_2858_ = v_fileName_2864_;
v___y_2859_ = v_suppressElabErrors_2868_;
v___y_2860_ = v___y_2863_;
v___y_2861_ = v___x_2873_;
goto v___jp_2854_;
}
else
{
lean_object* v___x_2874_; uint8_t v___x_2875_; 
v___x_2874_ = l_Lean_warningAsError;
v___x_2875_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5(v_options_2866_, v___x_2874_);
v___y_2855_ = v_ref_2867_;
v___y_2856_ = v_fileMap_2865_;
v___y_2857_ = v___f_2871_;
v___y_2858_ = v_fileName_2864_;
v___y_2859_ = v_suppressElabErrors_2868_;
v___y_2860_ = v___y_2863_;
v___y_2861_ = v___x_2875_;
goto v___jp_2854_;
}
}
else
{
lean_object* v___x_2876_; lean_object* v___x_2877_; 
lean_dec_ref(v_msgData_2761_);
v___x_2876_ = lean_box(0);
v___x_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2876_);
return v___x_2877_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg___boxed(lean_object* v_ref_2880_, lean_object* v_msgData_2881_, lean_object* v_severity_2882_, lean_object* v_isSilent_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
uint8_t v_severity_boxed_2889_; uint8_t v_isSilent_boxed_2890_; lean_object* v_res_2891_; 
v_severity_boxed_2889_ = lean_unbox(v_severity_2882_);
v_isSilent_boxed_2890_ = lean_unbox(v_isSilent_2883_);
v_res_2891_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg(v_ref_2880_, v_msgData_2881_, v_severity_boxed_2889_, v_isSilent_boxed_2890_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v_ref_2880_);
return v_res_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10(lean_object* v_msgData_2892_, uint8_t v_severity_2893_, uint8_t v_isSilent_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_){
_start:
{
lean_object* v_ref_2903_; lean_object* v___x_2904_; 
v_ref_2903_ = lean_ctor_get(v___y_2900_, 5);
v___x_2904_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg(v_ref_2903_, v_msgData_2892_, v_severity_2893_, v_isSilent_2894_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
return v___x_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10___boxed(lean_object* v_msgData_2905_, lean_object* v_severity_2906_, lean_object* v_isSilent_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_){
_start:
{
uint8_t v_severity_boxed_2916_; uint8_t v_isSilent_boxed_2917_; lean_object* v_res_2918_; 
v_severity_boxed_2916_ = lean_unbox(v_severity_2906_);
v_isSilent_boxed_2917_ = lean_unbox(v_isSilent_2907_);
v_res_2918_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10(v_msgData_2905_, v_severity_boxed_2916_, v_isSilent_boxed_2917_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
lean_dec_ref(v___y_2908_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6(lean_object* v_msgData_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_){
_start:
{
uint8_t v___x_2928_; uint8_t v___x_2929_; lean_object* v___x_2930_; 
v___x_2928_ = 2;
v___x_2929_ = 0;
v___x_2930_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10(v_msgData_2919_, v___x_2928_, v___x_2929_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6___boxed(lean_object* v_msgData_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
lean_object* v_res_2940_; 
v_res_2940_ = l_Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6(v_msgData_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec_ref(v___y_2932_);
return v_res_2940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__8(lean_object* v_a_2941_, lean_object* v_as_2942_, size_t v_i_2943_, size_t v_stop_2944_, lean_object* v_b_2945_){
_start:
{
lean_object* v___y_2947_; uint8_t v___x_2951_; 
v___x_2951_ = lean_usize_dec_eq(v_i_2943_, v_stop_2944_);
if (v___x_2951_ == 0)
{
lean_object* v_reassigns_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; uint8_t v___x_2955_; 
v_reassigns_2952_ = lean_ctor_get(v_a_2941_, 1);
v___x_2953_ = lean_array_uget_borrowed(v_as_2942_, v_i_2943_);
v___x_2954_ = l_Lean_TSyntax_getId(v___x_2953_);
v___x_2955_ = l_Lean_NameSet_contains(v_reassigns_2952_, v___x_2954_);
lean_dec(v___x_2954_);
if (v___x_2955_ == 0)
{
v___y_2947_ = v_b_2945_;
goto v___jp_2946_;
}
else
{
lean_object* v___x_2956_; 
lean_inc(v___x_2953_);
v___x_2956_ = lean_array_push(v_b_2945_, v___x_2953_);
v___y_2947_ = v___x_2956_;
goto v___jp_2946_;
}
}
else
{
return v_b_2945_;
}
v___jp_2946_:
{
size_t v___x_2948_; size_t v___x_2949_; 
v___x_2948_ = ((size_t)1ULL);
v___x_2949_ = lean_usize_add(v_i_2943_, v___x_2948_);
v_i_2943_ = v___x_2949_;
v_b_2945_ = v___y_2947_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__8___boxed(lean_object* v_a_2957_, lean_object* v_as_2958_, lean_object* v_i_2959_, lean_object* v_stop_2960_, lean_object* v_b_2961_){
_start:
{
size_t v_i_boxed_2962_; size_t v_stop_boxed_2963_; lean_object* v_res_2964_; 
v_i_boxed_2962_ = lean_unbox_usize(v_i_2959_);
lean_dec(v_i_2959_);
v_stop_boxed_2963_ = lean_unbox_usize(v_stop_2960_);
lean_dec(v_stop_2960_);
v_res_2964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__8(v_a_2957_, v_as_2958_, v_i_boxed_2962_, v_stop_boxed_2963_, v_b_2961_);
lean_dec_ref(v_as_2958_);
lean_dec_ref(v_a_2957_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__7(size_t v_sz_2965_, size_t v_i_2966_, lean_object* v_bs_2967_){
_start:
{
uint8_t v___x_2968_; 
v___x_2968_ = lean_usize_dec_lt(v_i_2966_, v_sz_2965_);
if (v___x_2968_ == 0)
{
return v_bs_2967_;
}
else
{
lean_object* v_v_2969_; lean_object* v___x_2970_; lean_object* v_bs_x27_2971_; lean_object* v___x_2972_; size_t v___x_2973_; size_t v___x_2974_; lean_object* v___x_2975_; 
v_v_2969_ = lean_array_uget(v_bs_2967_, v_i_2966_);
v___x_2970_ = lean_unsigned_to_nat(0u);
v_bs_x27_2971_ = lean_array_uset(v_bs_2967_, v_i_2966_, v___x_2970_);
v___x_2972_ = l_Lean_TSyntax_getId(v_v_2969_);
lean_dec(v_v_2969_);
v___x_2973_ = ((size_t)1ULL);
v___x_2974_ = lean_usize_add(v_i_2966_, v___x_2973_);
v___x_2975_ = lean_array_uset(v_bs_x27_2971_, v_i_2966_, v___x_2972_);
v_i_2966_ = v___x_2974_;
v_bs_2967_ = v___x_2975_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__7___boxed(lean_object* v_sz_2977_, lean_object* v_i_2978_, lean_object* v_bs_2979_){
_start:
{
size_t v_sz_boxed_2980_; size_t v_i_boxed_2981_; lean_object* v_res_2982_; 
v_sz_boxed_2980_ = lean_unbox_usize(v_sz_2977_);
lean_dec(v_sz_2977_);
v_i_boxed_2981_ = lean_unbox_usize(v_i_2978_);
lean_dec(v_i_2978_);
v_res_2982_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__7(v_sz_boxed_2980_, v_i_boxed_2981_, v_bs_2979_);
return v_res_2982_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___closed__12(void){
_start:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3003_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__11));
v___x_3004_ = l_Lean_stringToMessageData(v___x_3003_);
return v___x_3004_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___closed__14(void){
_start:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3006_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__13));
v___x_3007_ = l_Lean_stringToMessageData(v___x_3006_);
return v___x_3007_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___closed__16(void){
_start:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3009_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__15));
v___x_3010_ = l_Lean_stringToMessageData(v___x_3009_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor(lean_object* v_stx_3020_, lean_object* v_dec_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_){
_start:
{
lean_object* v___x_3030_; uint8_t v___x_3031_; 
v___x_3030_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
lean_inc(v_stx_3020_);
v___x_3031_ = l_Lean_Syntax_isOfKind(v_stx_3020_, v___x_3030_);
if (v___x_3031_ == 0)
{
lean_object* v___x_3032_; 
lean_dec_ref(v_dec_3021_);
lean_dec(v_stx_3020_);
v___x_3032_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_3032_;
}
else
{
lean_object* v___x_3033_; lean_object* v___x_3034_; uint8_t v___x_3035_; 
v___x_3033_ = lean_unsigned_to_nat(1u);
v___x_3034_ = l_Lean_Syntax_getArg(v_stx_3020_, v___x_3033_);
lean_inc(v___x_3034_);
v___x_3035_ = l_Lean_Syntax_matchesNull(v___x_3034_, v___x_3033_);
if (v___x_3035_ == 0)
{
lean_object* v___x_3036_; 
lean_dec(v___x_3034_);
lean_dec_ref(v_dec_3021_);
lean_dec(v_stx_3020_);
v___x_3036_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_3036_;
}
else
{
lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; uint8_t v___x_3040_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; uint8_t v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3057_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; uint8_t v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v_fst_3110_; lean_object* v_snd_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3149_; uint8_t v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; uint8_t v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; uint8_t v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; uint8_t v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; uint8_t v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; uint8_t v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v_h_x3f_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; 
v___x_3037_ = lean_unsigned_to_nat(0u);
v___x_3038_ = l_Lean_Syntax_getArg(v___x_3034_, v___x_3037_);
lean_dec(v___x_3034_);
v___x_3039_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
lean_inc(v___x_3038_);
v___x_3040_ = l_Lean_Syntax_isOfKind(v___x_3038_, v___x_3039_);
if (v___x_3040_ == 0)
{
lean_object* v___x_3503_; 
lean_dec(v___x_3038_);
lean_dec_ref(v_dec_3021_);
lean_dec(v_stx_3020_);
v___x_3503_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_3503_;
}
else
{
lean_object* v___x_3504_; uint8_t v___x_3505_; 
v___x_3504_ = l_Lean_Syntax_getArg(v___x_3038_, v___x_3037_);
v___x_3505_ = l_Lean_Syntax_isNone(v___x_3504_);
if (v___x_3505_ == 0)
{
lean_object* v___x_3506_; uint8_t v___x_3507_; 
v___x_3506_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3504_);
v___x_3507_ = l_Lean_Syntax_matchesNull(v___x_3504_, v___x_3506_);
if (v___x_3507_ == 0)
{
lean_object* v___x_3508_; 
lean_dec(v___x_3504_);
lean_dec(v___x_3038_);
lean_dec_ref(v_dec_3021_);
lean_dec(v_stx_3020_);
v___x_3508_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_3508_;
}
else
{
lean_object* v_h_x3f_3509_; lean_object* v___x_3510_; 
v_h_x3f_3509_ = l_Lean_Syntax_getArg(v___x_3504_, v___x_3037_);
lean_dec(v___x_3504_);
v___x_3510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3510_, 0, v_h_x3f_3509_);
v_h_x3f_3381_ = v___x_3510_;
v___y_3382_ = v_a_3022_;
v___y_3383_ = v_a_3023_;
v___y_3384_ = v_a_3024_;
v___y_3385_ = v_a_3025_;
v___y_3386_ = v_a_3026_;
v___y_3387_ = v_a_3027_;
v___y_3388_ = v_a_3028_;
goto v___jp_3380_;
}
}
else
{
lean_object* v___x_3511_; 
lean_dec(v___x_3504_);
v___x_3511_ = lean_box(0);
v_h_x3f_3381_ = v___x_3511_;
v___y_3382_ = v_a_3022_;
v___y_3383_ = v_a_3023_;
v___y_3384_ = v_a_3024_;
v___y_3385_ = v_a_3025_;
v___y_3386_ = v_a_3026_;
v___y_3387_ = v_a_3027_;
v___y_3388_ = v_a_3028_;
goto v___jp_3380_;
}
}
v___jp_3041_:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___f_3071_; uint8_t v___x_3072_; lean_object* v___x_3073_; 
v___x_3069_ = l_Lean_instInhabitedExpr;
v___x_3070_ = lean_box(v___x_3040_);
lean_inc(v___y_3049_);
lean_inc(v___y_3042_);
lean_inc(v___y_3050_);
lean_inc_ref(v___y_3056_);
v___f_3071_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__9___boxed), 25, 16);
lean_closure_set(v___f_3071_, 0, v___x_3069_);
lean_closure_set(v___f_3071_, 1, v___x_3037_);
lean_closure_set(v___f_3071_, 2, v___y_3054_);
lean_closure_set(v___f_3071_, 3, v___y_3056_);
lean_closure_set(v___f_3071_, 4, v___y_3050_);
lean_closure_set(v___f_3071_, 5, v___y_3057_);
lean_closure_set(v___f_3071_, 6, v___y_3055_);
lean_closure_set(v___f_3071_, 7, v___y_3052_);
lean_closure_set(v___f_3071_, 8, v___y_3051_);
lean_closure_set(v___f_3071_, 9, v___y_3058_);
lean_closure_set(v___f_3071_, 10, v___y_3046_);
lean_closure_set(v___f_3071_, 11, v___x_3070_);
lean_closure_set(v___f_3071_, 12, v___y_3042_);
lean_closure_set(v___f_3071_, 13, v___y_3049_);
lean_closure_set(v___f_3071_, 14, v___y_3047_);
lean_closure_set(v___f_3071_, 15, v___x_3033_);
v___x_3072_ = 0;
v___x_3073_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(v___y_3068_, v___f_3071_, v___x_3072_, v___y_3060_, v___y_3067_, v___y_3062_, v___y_3059_, v___y_3065_, v___y_3064_, v___y_3063_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_object* v_a_3074_; lean_object* v_doBlockResultType_3075_; lean_object* v___x_3076_; lean_object* v___y_3077_; lean_object* v___x_3078_; lean_object* v___f_3079_; lean_object* v___x_3080_; 
v_a_3074_ = lean_ctor_get(v___x_3073_, 0);
lean_inc(v_a_3074_);
lean_dec_ref(v___x_3073_);
v_doBlockResultType_3075_ = lean_ctor_get(v___y_3060_, 3);
v___x_3076_ = lean_box(v___y_3045_);
lean_inc(v___y_3053_);
lean_inc_ref(v_doBlockResultType_3075_);
v___y_3077_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__10___boxed), 19, 11);
lean_closure_set(v___y_3077_, 0, v___x_3076_);
lean_closure_set(v___y_3077_, 1, v_dec_3021_);
lean_closure_set(v___y_3077_, 2, v___y_3044_);
lean_closure_set(v___y_3077_, 3, v_doBlockResultType_3075_);
lean_closure_set(v___y_3077_, 4, v___y_3056_);
lean_closure_set(v___y_3077_, 5, v___y_3053_);
lean_closure_set(v___y_3077_, 6, v___y_3050_);
lean_closure_set(v___y_3077_, 7, v___y_3048_);
lean_closure_set(v___y_3077_, 8, v___y_3043_);
lean_closure_set(v___y_3077_, 9, v___x_3037_);
lean_closure_set(v___y_3077_, 10, v___x_3033_);
v___x_3078_ = lean_box(v___x_3040_);
v___f_3079_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__11___boxed), 13, 4);
lean_closure_set(v___f_3079_, 0, v___y_3042_);
lean_closure_set(v___f_3079_, 1, v___y_3077_);
lean_closure_set(v___f_3079_, 2, v___x_3033_);
lean_closure_set(v___f_3079_, 3, v___x_3078_);
lean_inc_ref(v___y_3066_);
v___x_3080_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(v___y_3049_, v___y_3066_, v___f_3079_, v___y_3060_, v___y_3067_, v___y_3062_, v___y_3059_, v___y_3065_, v___y_3064_, v___y_3063_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v_a_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
lean_inc(v_a_3081_);
lean_dec_ref(v___x_3080_);
v___x_3082_ = l_Lean_Expr_app___override(v___y_3061_, v_a_3074_);
lean_inc_ref(v_doBlockResultType_3075_);
v___x_3083_ = l_Lean_Elab_Do_mkBindApp(v___y_3066_, v_doBlockResultType_3075_, v___x_3082_, v_a_3081_, v___y_3060_, v___y_3067_, v___y_3062_, v___y_3059_, v___y_3065_, v___y_3064_, v___y_3063_);
return v___x_3083_;
}
else
{
lean_dec(v_a_3074_);
lean_dec_ref(v___y_3066_);
lean_dec_ref(v___y_3061_);
return v___x_3080_;
}
}
else
{
lean_dec_ref(v___y_3066_);
lean_dec_ref(v___y_3061_);
lean_dec_ref(v___y_3056_);
lean_dec(v___y_3050_);
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3044_);
lean_dec_ref(v___y_3043_);
lean_dec(v___y_3042_);
lean_dec_ref(v_dec_3021_);
return v___x_3073_;
}
}
v___jp_3084_:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3119_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17));
v___x_3120_ = l_Lean_Core_mkFreshUserName(v___x_3119_, v___y_3117_, v___y_3118_);
if (lean_obj_tag(v___x_3120_) == 0)
{
if (lean_obj_tag(v___y_3109_) == 1)
{
if (lean_obj_tag(v_snd_3111_) == 1)
{
lean_object* v_a_3121_; lean_object* v_val_3122_; lean_object* v_val_3123_; lean_object* v___f_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
lean_dec_ref(v___y_3108_);
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
lean_inc(v_a_3121_);
lean_dec_ref(v___x_3120_);
v_val_3122_ = lean_ctor_get(v___y_3109_, 0);
lean_inc(v_val_3122_);
lean_dec_ref(v___y_3109_);
v_val_3123_ = lean_ctor_get(v_snd_3111_, 0);
lean_inc(v_val_3123_);
lean_dec_ref(v_snd_3111_);
v___f_3124_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__12___boxed), 16, 7);
lean_closure_set(v___f_3124_, 0, v___y_3093_);
lean_closure_set(v___f_3124_, 1, v___y_3101_);
lean_closure_set(v___f_3124_, 2, v___x_3037_);
lean_closure_set(v___f_3124_, 3, v___y_3104_);
lean_closure_set(v___f_3124_, 4, v___y_3085_);
lean_closure_set(v___f_3124_, 5, v_val_3123_);
lean_closure_set(v___f_3124_, 6, v___y_3103_);
v___x_3125_ = l_Lean_TSyntax_getId(v___y_3106_);
lean_dec(v___y_3106_);
v___x_3126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3125_);
lean_ctor_set(v___x_3126_, 1, v___y_3107_);
v___x_3127_ = l_Lean_TSyntax_getId(v_val_3122_);
lean_dec(v_val_3122_);
v___x_3128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3127_);
lean_ctor_set(v___x_3128_, 1, v___f_3124_);
v___x_3129_ = lean_unsigned_to_nat(2u);
v___x_3130_ = lean_mk_empty_array_with_capacity(v___x_3129_);
v___x_3131_ = lean_array_push(v___x_3130_, v___x_3126_);
v___x_3132_ = lean_array_push(v___x_3131_, v___x_3128_);
lean_inc_ref(v___y_3102_);
v___y_3042_ = v___y_3086_;
v___y_3043_ = v___y_3087_;
v___y_3044_ = v___y_3088_;
v___y_3045_ = v___y_3089_;
v___y_3046_ = v___y_3090_;
v___y_3047_ = v___y_3091_;
v___y_3048_ = v___y_3092_;
v___y_3049_ = v_a_3121_;
v___y_3050_ = v___y_3094_;
v___y_3051_ = v___y_3095_;
v___y_3052_ = v___y_3096_;
v___y_3053_ = v___y_3097_;
v___y_3054_ = v___y_3098_;
v___y_3055_ = v___y_3099_;
v___y_3056_ = v___y_3100_;
v___y_3057_ = v___y_3102_;
v___y_3058_ = v___y_3105_;
v___y_3059_ = v___y_3115_;
v___y_3060_ = v___y_3112_;
v___y_3061_ = v_fst_3110_;
v___y_3062_ = v___y_3114_;
v___y_3063_ = v___y_3118_;
v___y_3064_ = v___y_3117_;
v___y_3065_ = v___y_3116_;
v___y_3066_ = v___y_3102_;
v___y_3067_ = v___y_3113_;
v___y_3068_ = v___x_3132_;
goto v___jp_3041_;
}
else
{
lean_object* v_a_3133_; lean_object* v___x_3134_; 
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec(v___y_3101_);
lean_dec(v___y_3093_);
lean_dec_ref(v___y_3085_);
v_a_3133_ = lean_ctor_get(v___x_3120_, 0);
lean_inc(v_a_3133_);
lean_dec_ref(v___x_3120_);
v___x_3134_ = lean_apply_2(v___y_3108_, v___y_3109_, v_snd_3111_);
lean_inc_ref(v___y_3102_);
v___y_3042_ = v___y_3086_;
v___y_3043_ = v___y_3087_;
v___y_3044_ = v___y_3088_;
v___y_3045_ = v___y_3089_;
v___y_3046_ = v___y_3090_;
v___y_3047_ = v___y_3091_;
v___y_3048_ = v___y_3092_;
v___y_3049_ = v_a_3133_;
v___y_3050_ = v___y_3094_;
v___y_3051_ = v___y_3095_;
v___y_3052_ = v___y_3096_;
v___y_3053_ = v___y_3097_;
v___y_3054_ = v___y_3098_;
v___y_3055_ = v___y_3099_;
v___y_3056_ = v___y_3100_;
v___y_3057_ = v___y_3102_;
v___y_3058_ = v___y_3105_;
v___y_3059_ = v___y_3115_;
v___y_3060_ = v___y_3112_;
v___y_3061_ = v_fst_3110_;
v___y_3062_ = v___y_3114_;
v___y_3063_ = v___y_3118_;
v___y_3064_ = v___y_3117_;
v___y_3065_ = v___y_3116_;
v___y_3066_ = v___y_3102_;
v___y_3067_ = v___y_3113_;
v___y_3068_ = v___x_3134_;
goto v___jp_3041_;
}
}
else
{
lean_object* v_a_3135_; lean_object* v___x_3136_; 
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec(v___y_3101_);
lean_dec(v___y_3093_);
lean_dec_ref(v___y_3085_);
v_a_3135_ = lean_ctor_get(v___x_3120_, 0);
lean_inc(v_a_3135_);
lean_dec_ref(v___x_3120_);
v___x_3136_ = lean_apply_2(v___y_3108_, v___y_3109_, v_snd_3111_);
lean_inc_ref(v___y_3102_);
v___y_3042_ = v___y_3086_;
v___y_3043_ = v___y_3087_;
v___y_3044_ = v___y_3088_;
v___y_3045_ = v___y_3089_;
v___y_3046_ = v___y_3090_;
v___y_3047_ = v___y_3091_;
v___y_3048_ = v___y_3092_;
v___y_3049_ = v_a_3135_;
v___y_3050_ = v___y_3094_;
v___y_3051_ = v___y_3095_;
v___y_3052_ = v___y_3096_;
v___y_3053_ = v___y_3097_;
v___y_3054_ = v___y_3098_;
v___y_3055_ = v___y_3099_;
v___y_3056_ = v___y_3100_;
v___y_3057_ = v___y_3102_;
v___y_3058_ = v___y_3105_;
v___y_3059_ = v___y_3115_;
v___y_3060_ = v___y_3112_;
v___y_3061_ = v_fst_3110_;
v___y_3062_ = v___y_3114_;
v___y_3063_ = v___y_3118_;
v___y_3064_ = v___y_3117_;
v___y_3065_ = v___y_3116_;
v___y_3066_ = v___y_3102_;
v___y_3067_ = v___y_3113_;
v___y_3068_ = v___x_3136_;
goto v___jp_3041_;
}
}
else
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3144_; 
lean_dec(v_snd_3111_);
lean_dec_ref(v_fst_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
lean_dec_ref(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3098_);
lean_dec(v___y_3096_);
lean_dec(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec(v___y_3091_);
lean_dec(v___y_3090_);
lean_dec(v___y_3088_);
lean_dec_ref(v___y_3087_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec_ref(v_dec_3021_);
v_a_3137_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3139_ = v___x_3120_;
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3120_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3142_; 
if (v_isShared_3140_ == 0)
{
v___x_3142_ = v___x_3139_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_3137_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
}
v___jp_3145_:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3182_ = lean_box(0);
lean_inc(v___y_3181_);
lean_inc_ref(v___y_3180_);
lean_inc(v___y_3179_);
lean_inc_ref(v___y_3178_);
lean_inc(v___y_3177_);
lean_inc_ref(v___y_3176_);
v___x_3183_ = lean_apply_8(v___y_3167_, v___x_3182_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, lean_box(0));
if (lean_obj_tag(v___x_3183_) == 0)
{
lean_object* v_a_3184_; lean_object* v_m_3185_; lean_object* v_u_3186_; lean_object* v_v_3187_; lean_object* v___x_3188_; 
v_a_3184_ = lean_ctor_get(v___x_3183_, 0);
lean_inc(v_a_3184_);
lean_dec_ref(v___x_3183_);
v_m_3185_ = lean_ctor_get(v___y_3164_, 0);
v_u_3186_ = lean_ctor_get(v___y_3164_, 1);
v_v_3187_ = lean_ctor_get(v___y_3164_, 2);
lean_inc(v_u_3186_);
v___x_3188_ = l_Lean_Meta_mkProdMkN(v_a_3184_, v_u_3186_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_object* v_a_3189_; 
v_a_3189_ = lean_ctor_get(v___x_3188_, 0);
lean_inc(v_a_3189_);
lean_dec_ref(v___x_3188_);
if (lean_obj_tag(v___y_3170_) == 0)
{
lean_object* v_fst_3190_; lean_object* v_snd_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3210_; 
v_fst_3190_ = lean_ctor_get(v_a_3189_, 0);
v_snd_3191_ = lean_ctor_get(v_a_3189_, 1);
v_isSharedCheck_3210_ = !lean_is_exclusive(v_a_3189_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3193_ = v_a_3189_;
v_isShared_3194_ = v_isSharedCheck_3210_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_snd_3191_);
lean_inc(v_fst_3190_);
lean_dec(v_a_3189_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3210_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3198_; 
v___x_3195_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__1));
v___x_3196_ = lean_box(0);
lean_inc(v_v_3187_);
if (v_isShared_3194_ == 0)
{
lean_ctor_set_tag(v___x_3193_, 1);
lean_ctor_set(v___x_3193_, 1, v___x_3196_);
lean_ctor_set(v___x_3193_, 0, v_v_3187_);
v___x_3198_ = v___x_3193_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_v_3187_);
lean_ctor_set(v_reuseFailAlloc_3209_, 1, v___x_3196_);
v___x_3198_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
lean_inc(v_u_3186_);
v___x_3199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3199_, 0, v_u_3186_);
lean_ctor_set(v___x_3199_, 1, v___x_3198_);
v___x_3200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3200_, 0, v___y_3168_);
lean_ctor_set(v___x_3200_, 1, v___x_3199_);
v___x_3201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3201_, 0, v___y_3174_);
lean_ctor_set(v___x_3201_, 1, v___x_3200_);
lean_inc_ref(v___x_3201_);
v___x_3202_ = l_Lean_mkConst(v___x_3195_, v___x_3201_);
lean_inc_ref(v___y_3173_);
lean_inc_ref(v___y_3163_);
lean_inc_ref(v_m_3185_);
v___x_3203_ = l_Lean_mkApp3(v___x_3202_, v_m_3185_, v___y_3163_, v___y_3173_);
v___x_3204_ = l_Lean_Elab_Term_mkInstMVar(v___x_3203_, v___x_3182_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
if (lean_obj_tag(v___x_3204_) == 0)
{
lean_object* v_a_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v_a_3205_ = lean_ctor_get(v___x_3204_, 0);
lean_inc(v_a_3205_);
lean_dec_ref(v___x_3204_);
v___x_3206_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__3));
v___x_3207_ = l_Lean_mkConst(v___x_3206_, v___x_3201_);
lean_inc(v_snd_3191_);
lean_inc_ref(v_m_3185_);
v___x_3208_ = l_Lean_mkApp7(v___x_3207_, v_m_3185_, v___y_3163_, v___y_3173_, v_a_3205_, v_snd_3191_, v___y_3172_, v_fst_3190_);
lean_inc(v_u_3186_);
v___y_3085_ = v___y_3146_;
v___y_3086_ = v___y_3147_;
v___y_3087_ = v___y_3148_;
v___y_3088_ = v___y_3149_;
v___y_3089_ = v___y_3150_;
v___y_3090_ = v___y_3151_;
v___y_3091_ = v___y_3152_;
v___y_3092_ = v___y_3153_;
v___y_3093_ = v___y_3154_;
v___y_3094_ = v_u_3186_;
v___y_3095_ = v___y_3155_;
v___y_3096_ = v___x_3182_;
v___y_3097_ = v_v_3187_;
v___y_3098_ = v___y_3156_;
v___y_3099_ = v___y_3157_;
v___y_3100_ = v___y_3158_;
v___y_3101_ = v___y_3159_;
v___y_3102_ = v_snd_3191_;
v___y_3103_ = v___y_3162_;
v___y_3104_ = v___y_3161_;
v___y_3105_ = v___y_3160_;
v___y_3106_ = v___y_3165_;
v___y_3107_ = v___y_3166_;
v___y_3108_ = v___y_3171_;
v___y_3109_ = v___y_3170_;
v_fst_3110_ = v___x_3208_;
v_snd_3111_ = v___x_3182_;
v___y_3112_ = v___y_3175_;
v___y_3113_ = v___y_3176_;
v___y_3114_ = v___y_3177_;
v___y_3115_ = v___y_3178_;
v___y_3116_ = v___y_3179_;
v___y_3117_ = v___y_3180_;
v___y_3118_ = v___y_3181_;
goto v___jp_3084_;
}
else
{
lean_dec_ref(v___x_3201_);
lean_dec(v_snd_3191_);
lean_dec(v_fst_3190_);
lean_dec_ref(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
lean_dec_ref(v_dec_3021_);
return v___x_3204_;
}
}
}
}
else
{
lean_object* v_fst_3211_; lean_object* v_snd_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3247_; 
v_fst_3211_ = lean_ctor_get(v_a_3189_, 0);
v_snd_3212_ = lean_ctor_get(v_a_3189_, 1);
v_isSharedCheck_3247_ = !lean_is_exclusive(v_a_3189_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3214_ = v_a_3189_;
v_isShared_3215_ = v_isSharedCheck_3247_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_snd_3212_);
lean_inc(v_fst_3211_);
lean_dec(v_a_3189_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3247_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3219_; 
v___x_3216_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__4));
v___x_3217_ = lean_box(0);
lean_inc(v___y_3174_);
if (v_isShared_3215_ == 0)
{
lean_ctor_set_tag(v___x_3214_, 1);
lean_ctor_set(v___x_3214_, 1, v___x_3217_);
lean_ctor_set(v___x_3214_, 0, v___y_3174_);
v___x_3219_ = v___x_3214_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v___y_3174_);
lean_ctor_set(v_reuseFailAlloc_3246_, 1, v___x_3217_);
v___x_3219_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
lean_inc(v___y_3168_);
v___x_3220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3220_, 0, v___y_3168_);
lean_ctor_set(v___x_3220_, 1, v___x_3219_);
v___x_3221_ = l_Lean_mkConst(v___x_3216_, v___x_3220_);
lean_inc_ref(v___y_3163_);
lean_inc_ref(v___y_3173_);
v___x_3222_ = l_Lean_mkAppB(v___x_3221_, v___y_3173_, v___y_3163_);
v___x_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
v___x_3224_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__6));
v___x_3225_ = l_Lean_Meta_mkFreshExprMVar(v___x_3223_, v___y_3169_, v___x_3224_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v_a_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
lean_inc_n(v_a_3226_, 2);
lean_dec_ref(v___x_3225_);
v___x_3227_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__8));
lean_inc(v_v_3187_);
v___x_3228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3228_, 0, v_v_3187_);
lean_ctor_set(v___x_3228_, 1, v___x_3217_);
lean_inc(v_u_3186_);
v___x_3229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3229_, 0, v_u_3186_);
lean_ctor_set(v___x_3229_, 1, v___x_3228_);
v___x_3230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3230_, 0, v___y_3168_);
lean_ctor_set(v___x_3230_, 1, v___x_3229_);
v___x_3231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3231_, 0, v___y_3174_);
lean_ctor_set(v___x_3231_, 1, v___x_3230_);
lean_inc_ref(v___x_3231_);
v___x_3232_ = l_Lean_mkConst(v___x_3227_, v___x_3231_);
lean_inc_ref(v___y_3173_);
lean_inc_ref(v___y_3163_);
lean_inc_ref(v_m_3185_);
v___x_3233_ = l_Lean_mkApp4(v___x_3232_, v_m_3185_, v___y_3163_, v___y_3173_, v_a_3226_);
v___x_3234_ = l_Lean_Elab_Term_mkInstMVar(v___x_3233_, v___x_3182_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_object* v_a_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3245_; 
v_a_3235_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3237_ = v___x_3234_;
v_isShared_3238_ = v_isSharedCheck_3245_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_dec(v___x_3234_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3245_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3243_; 
v___x_3239_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__10));
v___x_3240_ = l_Lean_mkConst(v___x_3239_, v___x_3231_);
lean_inc(v_snd_3212_);
lean_inc(v_a_3226_);
lean_inc_ref(v_m_3185_);
v___x_3241_ = l_Lean_mkApp8(v___x_3240_, v_m_3185_, v___y_3163_, v___y_3173_, v_a_3226_, v_a_3235_, v_snd_3212_, v___y_3172_, v_fst_3211_);
if (v_isShared_3238_ == 0)
{
lean_ctor_set_tag(v___x_3237_, 1);
lean_ctor_set(v___x_3237_, 0, v_a_3226_);
v___x_3243_ = v___x_3237_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v_a_3226_);
v___x_3243_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
lean_inc(v_u_3186_);
v___y_3085_ = v___y_3146_;
v___y_3086_ = v___y_3147_;
v___y_3087_ = v___y_3148_;
v___y_3088_ = v___y_3149_;
v___y_3089_ = v___y_3150_;
v___y_3090_ = v___y_3151_;
v___y_3091_ = v___y_3152_;
v___y_3092_ = v___y_3153_;
v___y_3093_ = v___y_3154_;
v___y_3094_ = v_u_3186_;
v___y_3095_ = v___y_3155_;
v___y_3096_ = v___x_3182_;
v___y_3097_ = v_v_3187_;
v___y_3098_ = v___y_3156_;
v___y_3099_ = v___y_3157_;
v___y_3100_ = v___y_3158_;
v___y_3101_ = v___y_3159_;
v___y_3102_ = v_snd_3212_;
v___y_3103_ = v___y_3162_;
v___y_3104_ = v___y_3161_;
v___y_3105_ = v___y_3160_;
v___y_3106_ = v___y_3165_;
v___y_3107_ = v___y_3166_;
v___y_3108_ = v___y_3171_;
v___y_3109_ = v___y_3170_;
v_fst_3110_ = v___x_3241_;
v_snd_3111_ = v___x_3243_;
v___y_3112_ = v___y_3175_;
v___y_3113_ = v___y_3176_;
v___y_3114_ = v___y_3177_;
v___y_3115_ = v___y_3178_;
v___y_3116_ = v___y_3179_;
v___y_3117_ = v___y_3180_;
v___y_3118_ = v___y_3181_;
goto v___jp_3084_;
}
}
}
else
{
lean_dec_ref(v___x_3231_);
lean_dec(v_a_3226_);
lean_dec(v_snd_3212_);
lean_dec(v_fst_3211_);
lean_dec_ref(v___y_3170_);
lean_dec_ref(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
lean_dec_ref(v_dec_3021_);
return v___x_3234_;
}
}
else
{
lean_dec(v_snd_3212_);
lean_dec(v_fst_3211_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
lean_dec_ref(v_dec_3021_);
return v___x_3225_;
}
}
}
}
}
else
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3255_; 
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
lean_dec_ref(v_dec_3021_);
v_a_3248_ = lean_ctor_get(v___x_3188_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3250_ = v___x_3188_;
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3188_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
}
else
{
lean_object* v_a_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3263_; 
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
lean_dec_ref(v_dec_3021_);
v_a_3256_ = lean_ctor_get(v___x_3183_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3183_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3258_ = v___x_3183_;
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
else
{
lean_inc(v_a_3256_);
lean_dec(v___x_3183_);
v___x_3258_ = lean_box(0);
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
v_resetjp_3257_:
{
lean_object* v___x_3261_; 
if (v_isShared_3259_ == 0)
{
v___x_3261_ = v___x_3258_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_a_3256_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
}
}
v___jp_3264_:
{
lean_object* v___x_3298_; 
v___x_3298_ = l_Lean_Elab_Do_mkPUnit___redArg(v___y_3280_);
if (lean_obj_tag(v___x_3298_) == 0)
{
lean_object* v_a_3299_; lean_object* v_resultName_3300_; lean_object* v_resultType_3301_; lean_object* v___x_3302_; 
v_a_3299_ = lean_ctor_get(v___x_3298_, 0);
lean_inc(v_a_3299_);
lean_dec_ref(v___x_3298_);
v_resultName_3300_ = lean_ctor_get(v_dec_3021_, 0);
v_resultType_3301_ = lean_ctor_get(v_dec_3021_, 1);
lean_inc_ref(v_resultType_3301_);
v___x_3302_ = l_Lean_Meta_isExprDefEq(v_resultType_3301_, v_a_3299_, v___y_3288_, v___y_3292_, v___y_3285_, v___y_3287_);
if (lean_obj_tag(v___x_3302_) == 0)
{
lean_object* v_a_3303_; uint8_t v___x_3304_; 
v_a_3303_ = lean_ctor_get(v___x_3302_, 0);
lean_inc(v_a_3303_);
lean_dec_ref(v___x_3302_);
v___x_3304_ = lean_unbox(v_a_3303_);
lean_dec(v_a_3303_);
if (v___x_3304_ == 0)
{
lean_object* v___x_3305_; 
v___x_3305_ = l_Lean_Elab_Do_mkPUnit___redArg(v___y_3280_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_object* v_a_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v_a_3306_ = lean_ctor_get(v___x_3305_, 0);
lean_inc(v_a_3306_);
lean_dec_ref(v___x_3305_);
v___x_3307_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___closed__12, &l_Lean_Elab_Do_elabDoFor___closed__12_once, _init_l_Lean_Elab_Do_elabDoFor___closed__12);
v___x_3308_ = l_Lean_MessageData_ofExpr(v_a_3306_);
v___x_3309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3307_);
lean_ctor_set(v___x_3309_, 1, v___x_3308_);
v___x_3310_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___closed__14, &l_Lean_Elab_Do_elabDoFor___closed__14_once, _init_l_Lean_Elab_Do_elabDoFor___closed__14);
v___x_3311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3309_);
lean_ctor_set(v___x_3311_, 1, v___x_3310_);
lean_inc_ref(v_resultType_3301_);
v___x_3312_ = l_Lean_MessageData_ofExpr(v_resultType_3301_);
v___x_3313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3311_);
lean_ctor_set(v___x_3313_, 1, v___x_3312_);
v___x_3314_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___closed__16, &l_Lean_Elab_Do_elabDoFor___closed__16_once, _init_l_Lean_Elab_Do_elabDoFor___closed__16);
v___x_3315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3313_);
lean_ctor_set(v___x_3315_, 1, v___x_3314_);
v___x_3316_ = l_Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6(v___x_3315_, v___y_3280_, v___y_3283_, v___y_3279_, v___y_3288_, v___y_3292_, v___y_3285_, v___y_3287_);
if (lean_obj_tag(v___x_3316_) == 0)
{
lean_dec_ref(v___x_3316_);
lean_inc_ref(v_resultType_3301_);
lean_inc_ref(v___y_3274_);
lean_inc(v_resultName_3300_);
v___y_3146_ = v___y_3265_;
v___y_3147_ = v___y_3297_;
v___y_3148_ = v___y_3266_;
v___y_3149_ = v___y_3267_;
v___y_3150_ = v___y_3268_;
v___y_3151_ = v___y_3269_;
v___y_3152_ = v___y_3270_;
v___y_3153_ = v___y_3271_;
v___y_3154_ = v___y_3272_;
v___y_3155_ = v_resultName_3300_;
v___y_3156_ = v___y_3273_;
v___y_3157_ = v___y_3274_;
v___y_3158_ = v___y_3275_;
v___y_3159_ = v___y_3276_;
v___y_3160_ = v_resultType_3301_;
v___y_3161_ = v___y_3278_;
v___y_3162_ = v___y_3277_;
v___y_3163_ = v___y_3281_;
v___y_3164_ = v___y_3282_;
v___y_3165_ = v___y_3289_;
v___y_3166_ = v___y_3290_;
v___y_3167_ = v___y_3274_;
v___y_3168_ = v___y_3291_;
v___y_3169_ = v___y_3293_;
v___y_3170_ = v___y_3284_;
v___y_3171_ = v___y_3294_;
v___y_3172_ = v___y_3295_;
v___y_3173_ = v___y_3296_;
v___y_3174_ = v___y_3286_;
v___y_3175_ = v___y_3280_;
v___y_3176_ = v___y_3283_;
v___y_3177_ = v___y_3279_;
v___y_3178_ = v___y_3288_;
v___y_3179_ = v___y_3292_;
v___y_3180_ = v___y_3285_;
v___y_3181_ = v___y_3287_;
goto v___jp_3145_;
}
else
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec(v___y_3289_);
lean_dec(v___y_3286_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3281_);
lean_dec_ref(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec_ref(v___y_3274_);
lean_dec(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3266_);
lean_dec_ref(v___y_3265_);
lean_dec_ref(v_dec_3021_);
v_a_3317_ = lean_ctor_get(v___x_3316_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___x_3316_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3316_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3322_; 
if (v_isShared_3320_ == 0)
{
v___x_3322_ = v___x_3319_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3317_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
}
else
{
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec(v___y_3289_);
lean_dec(v___y_3286_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3281_);
lean_dec_ref(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec_ref(v___y_3274_);
lean_dec(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3266_);
lean_dec_ref(v___y_3265_);
lean_dec_ref(v_dec_3021_);
return v___x_3305_;
}
}
else
{
lean_inc_ref(v_resultType_3301_);
lean_inc_ref(v___y_3274_);
lean_inc(v_resultName_3300_);
v___y_3146_ = v___y_3265_;
v___y_3147_ = v___y_3297_;
v___y_3148_ = v___y_3266_;
v___y_3149_ = v___y_3267_;
v___y_3150_ = v___y_3268_;
v___y_3151_ = v___y_3269_;
v___y_3152_ = v___y_3270_;
v___y_3153_ = v___y_3271_;
v___y_3154_ = v___y_3272_;
v___y_3155_ = v_resultName_3300_;
v___y_3156_ = v___y_3273_;
v___y_3157_ = v___y_3274_;
v___y_3158_ = v___y_3275_;
v___y_3159_ = v___y_3276_;
v___y_3160_ = v_resultType_3301_;
v___y_3161_ = v___y_3278_;
v___y_3162_ = v___y_3277_;
v___y_3163_ = v___y_3281_;
v___y_3164_ = v___y_3282_;
v___y_3165_ = v___y_3289_;
v___y_3166_ = v___y_3290_;
v___y_3167_ = v___y_3274_;
v___y_3168_ = v___y_3291_;
v___y_3169_ = v___y_3293_;
v___y_3170_ = v___y_3284_;
v___y_3171_ = v___y_3294_;
v___y_3172_ = v___y_3295_;
v___y_3173_ = v___y_3296_;
v___y_3174_ = v___y_3286_;
v___y_3175_ = v___y_3280_;
v___y_3176_ = v___y_3283_;
v___y_3177_ = v___y_3279_;
v___y_3178_ = v___y_3288_;
v___y_3179_ = v___y_3292_;
v___y_3180_ = v___y_3285_;
v___y_3181_ = v___y_3287_;
goto v___jp_3145_;
}
}
else
{
lean_object* v_a_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3332_; 
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec(v___y_3289_);
lean_dec(v___y_3286_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3281_);
lean_dec_ref(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec_ref(v___y_3274_);
lean_dec(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3266_);
lean_dec_ref(v___y_3265_);
lean_dec_ref(v_dec_3021_);
v_a_3325_ = lean_ctor_get(v___x_3302_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3327_ = v___x_3302_;
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_a_3325_);
lean_dec(v___x_3302_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3330_; 
if (v_isShared_3328_ == 0)
{
v___x_3330_ = v___x_3327_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_a_3325_);
v___x_3330_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
return v___x_3330_;
}
}
}
}
else
{
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec(v___y_3289_);
lean_dec(v___y_3286_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3281_);
lean_dec_ref(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec_ref(v___y_3274_);
lean_dec(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3266_);
lean_dec_ref(v___y_3265_);
lean_dec_ref(v_dec_3021_);
return v___x_3298_;
}
}
v___jp_3333_:
{
uint8_t v_returnsEarly_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___f_3370_; 
v_returnsEarly_3367_ = lean_ctor_get_uint8(v___y_3361_, sizeof(void*)*2 + 2);
lean_dec_ref(v___y_3361_);
v___x_3368_ = lean_box(v_returnsEarly_3367_);
v___x_3369_ = lean_box(v___y_3346_);
lean_inc_ref(v___y_3343_);
lean_inc_ref(v___y_3334_);
lean_inc_ref(v___y_3366_);
v___f_3370_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__2___boxed), 14, 6);
lean_closure_set(v___f_3370_, 0, v___y_3366_);
lean_closure_set(v___f_3370_, 1, v___y_3334_);
lean_closure_set(v___f_3370_, 2, v___x_3368_);
lean_closure_set(v___f_3370_, 3, v___x_3037_);
lean_closure_set(v___f_3370_, 4, v___y_3343_);
lean_closure_set(v___f_3370_, 5, v___x_3369_);
if (v_returnsEarly_3367_ == 0)
{
size_t v_sz_3371_; size_t v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
lean_dec(v___y_3353_);
v_sz_3371_ = lean_array_size(v___y_3366_);
v___x_3372_ = ((size_t)0ULL);
lean_inc_ref(v___y_3366_);
v___x_3373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__7(v_sz_3371_, v___x_3372_, v___y_3366_);
v___x_3374_ = lean_array_to_list(v___x_3373_);
v___y_3265_ = v___y_3335_;
v___y_3266_ = v___y_3366_;
v___y_3267_ = v___y_3336_;
v___y_3268_ = v_returnsEarly_3367_;
v___y_3269_ = v___y_3337_;
v___y_3270_ = v___y_3338_;
v___y_3271_ = v___y_3339_;
v___y_3272_ = v___y_3340_;
v___y_3273_ = v___y_3341_;
v___y_3274_ = v___f_3370_;
v___y_3275_ = v___y_3343_;
v___y_3276_ = v___y_3344_;
v___y_3277_ = v___y_3347_;
v___y_3278_ = v___y_3348_;
v___y_3279_ = v___y_3349_;
v___y_3280_ = v___y_3350_;
v___y_3281_ = v___y_3351_;
v___y_3282_ = v___y_3334_;
v___y_3283_ = v___y_3352_;
v___y_3284_ = v___y_3354_;
v___y_3285_ = v___y_3355_;
v___y_3286_ = v___y_3356_;
v___y_3287_ = v___y_3357_;
v___y_3288_ = v___y_3358_;
v___y_3289_ = v___y_3359_;
v___y_3290_ = v___y_3342_;
v___y_3291_ = v___y_3360_;
v___y_3292_ = v___y_3363_;
v___y_3293_ = v___y_3362_;
v___y_3294_ = v___y_3345_;
v___y_3295_ = v___y_3365_;
v___y_3296_ = v___y_3364_;
v___y_3297_ = v___x_3374_;
goto v___jp_3264_;
}
else
{
size_t v_sz_3375_; size_t v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v_sz_3375_ = lean_array_size(v___y_3366_);
v___x_3376_ = ((size_t)0ULL);
lean_inc_ref(v___y_3366_);
v___x_3377_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__7(v_sz_3375_, v___x_3376_, v___y_3366_);
v___x_3378_ = lean_array_to_list(v___x_3377_);
v___x_3379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3379_, 0, v___y_3353_);
lean_ctor_set(v___x_3379_, 1, v___x_3378_);
v___y_3265_ = v___y_3335_;
v___y_3266_ = v___y_3366_;
v___y_3267_ = v___y_3336_;
v___y_3268_ = v_returnsEarly_3367_;
v___y_3269_ = v___y_3337_;
v___y_3270_ = v___y_3338_;
v___y_3271_ = v___y_3339_;
v___y_3272_ = v___y_3340_;
v___y_3273_ = v___y_3341_;
v___y_3274_ = v___f_3370_;
v___y_3275_ = v___y_3343_;
v___y_3276_ = v___y_3344_;
v___y_3277_ = v___y_3347_;
v___y_3278_ = v___y_3348_;
v___y_3279_ = v___y_3349_;
v___y_3280_ = v___y_3350_;
v___y_3281_ = v___y_3351_;
v___y_3282_ = v___y_3334_;
v___y_3283_ = v___y_3352_;
v___y_3284_ = v___y_3354_;
v___y_3285_ = v___y_3355_;
v___y_3286_ = v___y_3356_;
v___y_3287_ = v___y_3357_;
v___y_3288_ = v___y_3358_;
v___y_3289_ = v___y_3359_;
v___y_3290_ = v___y_3342_;
v___y_3291_ = v___y_3360_;
v___y_3292_ = v___y_3363_;
v___y_3293_ = v___y_3362_;
v___y_3294_ = v___y_3345_;
v___y_3295_ = v___y_3365_;
v___y_3296_ = v___y_3364_;
v___y_3297_ = v___x_3379_;
goto v___jp_3264_;
}
}
v___jp_3380_:
{
lean_object* v_x_3389_; lean_object* v___x_3390_; uint8_t v___x_3391_; 
v_x_3389_ = l_Lean_Syntax_getArg(v___x_3038_, v___x_3033_);
v___x_3390_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__16));
lean_inc(v_x_3389_);
v___x_3391_ = l_Lean_Syntax_isOfKind(v_x_3389_, v___x_3390_);
if (v___x_3391_ == 0)
{
lean_object* v___x_3392_; 
lean_dec(v_x_3389_);
lean_dec(v_h_x3f_3381_);
lean_dec(v___x_3038_);
lean_dec_ref(v_dec_3021_);
lean_dec(v_stx_3020_);
v___x_3392_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
return v___x_3392_;
}
else
{
lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3393_ = lean_mk_empty_array_with_capacity(v___x_3033_);
lean_inc(v_x_3389_);
v___x_3394_ = lean_array_push(v___x_3393_, v_x_3389_);
v___x_3395_ = l_Lean_Elab_Do_checkMutVarsForShadowing(v___x_3394_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_);
lean_dec_ref(v___x_3394_);
if (lean_obj_tag(v___x_3395_) == 0)
{
lean_object* v___x_3396_; 
lean_dec_ref(v___x_3395_);
v___x_3396_ = l_Lean_Meta_mkFreshLevelMVar(v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_object* v_a_3397_; lean_object* v___x_3398_; 
v_a_3397_ = lean_ctor_get(v___x_3396_, 0);
lean_inc(v_a_3397_);
lean_dec_ref(v___x_3396_);
v___x_3398_ = l_Lean_Meta_mkFreshLevelMVar(v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; uint8_t v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_a_3399_);
lean_dec_ref(v___x_3398_);
lean_inc(v_a_3397_);
v___x_3400_ = l_Lean_Level_succ___override(v_a_3397_);
v___x_3401_ = l_Lean_mkSort(v___x_3400_);
v___x_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3401_);
v___x_3403_ = 0;
v___x_3404_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__18));
v___x_3405_ = l_Lean_Meta_mkFreshExprMVar(v___x_3402_, v___x_3403_, v___x_3404_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3478_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3408_ = v___x_3405_;
v_isShared_3409_ = v_isSharedCheck_3478_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v___x_3405_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3478_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3413_; 
lean_inc(v_a_3399_);
v___x_3410_ = l_Lean_Level_succ___override(v_a_3399_);
v___x_3411_ = l_Lean_mkSort(v___x_3410_);
if (v_isShared_3409_ == 0)
{
lean_ctor_set_tag(v___x_3408_, 1);
lean_ctor_set(v___x_3408_, 0, v___x_3411_);
v___x_3413_ = v___x_3408_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v___x_3411_);
v___x_3413_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3414_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__20));
v___x_3415_ = l_Lean_Meta_mkFreshExprMVar(v___x_3413_, v___x_3403_, v___x_3414_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3476_; 
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3418_ = v___x_3415_;
v_isShared_3419_ = v_isSharedCheck_3476_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3415_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3476_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3423_; 
v___x_3420_ = lean_unsigned_to_nat(3u);
v___x_3421_ = l_Lean_Syntax_getArg(v___x_3038_, v___x_3420_);
lean_dec(v___x_3038_);
lean_inc(v_a_3416_);
if (v_isShared_3419_ == 0)
{
lean_ctor_set_tag(v___x_3418_, 1);
v___x_3423_ = v___x_3418_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_a_3416_);
v___x_3423_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3424_ = lean_box(0);
v___x_3425_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_3421_, v___x_3423_, v___x_3040_, v___x_3040_, v___x_3424_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v_a_3426_; lean_object* v_body_3427_; lean_object* v___x_3428_; 
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
lean_inc(v_a_3426_);
lean_dec_ref(v___x_3425_);
v_body_3427_ = l_Lean_Syntax_getArg(v_stx_3020_, v___x_3420_);
lean_dec(v_stx_3020_);
lean_inc(v_body_3427_);
v___x_3428_ = l_Lean_Elab_Do_inferControlInfoSeq(v_body_3427_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v_a_3429_; lean_object* v___x_3430_; 
v_a_3429_ = lean_ctor_get(v___x_3428_, 0);
lean_inc(v_a_3429_);
lean_dec_ref(v___x_3428_);
v___x_3430_ = l_Lean_Elab_Do_getReturnCont___redArg(v___y_3382_);
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v_a_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; 
v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
lean_inc(v_a_3431_);
lean_dec_ref(v___x_3430_);
v___x_3432_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__22));
v___x_3433_ = l_Lean_Core_mkFreshUserName(v___x_3432_, v___y_3387_, v___y_3388_);
if (lean_obj_tag(v___x_3433_) == 0)
{
lean_object* v_a_3434_; lean_object* v_monadInfo_3435_; lean_object* v_mutVars_3436_; lean_object* v___f_3437_; lean_object* v___f_3438_; lean_object* v___x_3439_; lean_object* v___f_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; uint8_t v___x_3443_; 
v_a_3434_ = lean_ctor_get(v___x_3433_, 0);
lean_inc(v_a_3434_);
lean_dec_ref(v___x_3433_);
v_monadInfo_3435_ = lean_ctor_get(v___y_3382_, 0);
v_mutVars_3436_ = lean_ctor_get(v___y_3382_, 1);
lean_inc(v_a_3406_);
v___f_3437_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__0___boxed), 10, 1);
lean_closure_set(v___f_3437_, 0, v_a_3406_);
lean_inc_ref(v___f_3437_);
lean_inc(v_x_3389_);
v___f_3438_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__1___boxed), 5, 3);
lean_closure_set(v___f_3438_, 0, v_x_3389_);
lean_closure_set(v___f_3438_, 1, v___f_3437_);
lean_closure_set(v___f_3438_, 2, v___x_3033_);
v___x_3439_ = lean_box(v___x_3040_);
lean_inc(v_a_3431_);
v___f_3440_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__3___boxed), 12, 3);
lean_closure_set(v___f_3440_, 0, v_a_3431_);
lean_closure_set(v___f_3440_, 1, v___x_3033_);
lean_closure_set(v___f_3440_, 2, v___x_3439_);
v___x_3441_ = lean_array_get_size(v_mutVars_3436_);
v___x_3442_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_3443_ = lean_nat_dec_lt(v___x_3037_, v___x_3441_);
if (v___x_3443_ == 0)
{
lean_inc(v_a_3406_);
lean_inc(v_a_3426_);
lean_inc(v_a_3397_);
lean_inc(v_x_3389_);
lean_inc(v_a_3399_);
lean_inc(v_h_x3f_3381_);
lean_inc(v_a_3434_);
lean_inc(v_a_3416_);
v___y_3334_ = v_monadInfo_3435_;
v___y_3335_ = v_a_3416_;
v___y_3336_ = v_a_3434_;
v___y_3337_ = v_body_3427_;
v___y_3338_ = v_h_x3f_3381_;
v___y_3339_ = v___f_3440_;
v___y_3340_ = v_a_3399_;
v___y_3341_ = v_x_3389_;
v___y_3342_ = v___f_3437_;
v___y_3343_ = v_a_3431_;
v___y_3344_ = v_a_3397_;
v___y_3345_ = v___f_3438_;
v___y_3346_ = v___x_3391_;
v___y_3347_ = v_a_3426_;
v___y_3348_ = v_a_3406_;
v___y_3349_ = v___y_3384_;
v___y_3350_ = v___y_3382_;
v___y_3351_ = v_a_3416_;
v___y_3352_ = v___y_3383_;
v___y_3353_ = v_a_3434_;
v___y_3354_ = v_h_x3f_3381_;
v___y_3355_ = v___y_3387_;
v___y_3356_ = v_a_3399_;
v___y_3357_ = v___y_3388_;
v___y_3358_ = v___y_3385_;
v___y_3359_ = v_x_3389_;
v___y_3360_ = v_a_3397_;
v___y_3361_ = v_a_3429_;
v___y_3362_ = v___x_3403_;
v___y_3363_ = v___y_3386_;
v___y_3364_ = v_a_3406_;
v___y_3365_ = v_a_3426_;
v___y_3366_ = v___x_3442_;
goto v___jp_3333_;
}
else
{
uint8_t v___x_3444_; 
v___x_3444_ = lean_nat_dec_le(v___x_3441_, v___x_3441_);
if (v___x_3444_ == 0)
{
if (v___x_3443_ == 0)
{
lean_inc(v_a_3406_);
lean_inc(v_a_3426_);
lean_inc(v_a_3397_);
lean_inc(v_x_3389_);
lean_inc(v_a_3399_);
lean_inc(v_h_x3f_3381_);
lean_inc(v_a_3434_);
lean_inc(v_a_3416_);
v___y_3334_ = v_monadInfo_3435_;
v___y_3335_ = v_a_3416_;
v___y_3336_ = v_a_3434_;
v___y_3337_ = v_body_3427_;
v___y_3338_ = v_h_x3f_3381_;
v___y_3339_ = v___f_3440_;
v___y_3340_ = v_a_3399_;
v___y_3341_ = v_x_3389_;
v___y_3342_ = v___f_3437_;
v___y_3343_ = v_a_3431_;
v___y_3344_ = v_a_3397_;
v___y_3345_ = v___f_3438_;
v___y_3346_ = v___x_3391_;
v___y_3347_ = v_a_3426_;
v___y_3348_ = v_a_3406_;
v___y_3349_ = v___y_3384_;
v___y_3350_ = v___y_3382_;
v___y_3351_ = v_a_3416_;
v___y_3352_ = v___y_3383_;
v___y_3353_ = v_a_3434_;
v___y_3354_ = v_h_x3f_3381_;
v___y_3355_ = v___y_3387_;
v___y_3356_ = v_a_3399_;
v___y_3357_ = v___y_3388_;
v___y_3358_ = v___y_3385_;
v___y_3359_ = v_x_3389_;
v___y_3360_ = v_a_3397_;
v___y_3361_ = v_a_3429_;
v___y_3362_ = v___x_3403_;
v___y_3363_ = v___y_3386_;
v___y_3364_ = v_a_3406_;
v___y_3365_ = v_a_3426_;
v___y_3366_ = v___x_3442_;
goto v___jp_3333_;
}
else
{
size_t v___x_3445_; size_t v___x_3446_; lean_object* v___x_3447_; 
v___x_3445_ = ((size_t)0ULL);
v___x_3446_ = lean_usize_of_nat(v___x_3441_);
v___x_3447_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__8(v_a_3429_, v_mutVars_3436_, v___x_3445_, v___x_3446_, v___x_3442_);
lean_inc(v_a_3406_);
lean_inc(v_a_3426_);
lean_inc(v_a_3397_);
lean_inc(v_x_3389_);
lean_inc(v_a_3399_);
lean_inc(v_h_x3f_3381_);
lean_inc(v_a_3434_);
lean_inc(v_a_3416_);
v___y_3334_ = v_monadInfo_3435_;
v___y_3335_ = v_a_3416_;
v___y_3336_ = v_a_3434_;
v___y_3337_ = v_body_3427_;
v___y_3338_ = v_h_x3f_3381_;
v___y_3339_ = v___f_3440_;
v___y_3340_ = v_a_3399_;
v___y_3341_ = v_x_3389_;
v___y_3342_ = v___f_3437_;
v___y_3343_ = v_a_3431_;
v___y_3344_ = v_a_3397_;
v___y_3345_ = v___f_3438_;
v___y_3346_ = v___x_3391_;
v___y_3347_ = v_a_3426_;
v___y_3348_ = v_a_3406_;
v___y_3349_ = v___y_3384_;
v___y_3350_ = v___y_3382_;
v___y_3351_ = v_a_3416_;
v___y_3352_ = v___y_3383_;
v___y_3353_ = v_a_3434_;
v___y_3354_ = v_h_x3f_3381_;
v___y_3355_ = v___y_3387_;
v___y_3356_ = v_a_3399_;
v___y_3357_ = v___y_3388_;
v___y_3358_ = v___y_3385_;
v___y_3359_ = v_x_3389_;
v___y_3360_ = v_a_3397_;
v___y_3361_ = v_a_3429_;
v___y_3362_ = v___x_3403_;
v___y_3363_ = v___y_3386_;
v___y_3364_ = v_a_3406_;
v___y_3365_ = v_a_3426_;
v___y_3366_ = v___x_3447_;
goto v___jp_3333_;
}
}
else
{
size_t v___x_3448_; size_t v___x_3449_; lean_object* v___x_3450_; 
v___x_3448_ = ((size_t)0ULL);
v___x_3449_ = lean_usize_of_nat(v___x_3441_);
v___x_3450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__8(v_a_3429_, v_mutVars_3436_, v___x_3448_, v___x_3449_, v___x_3442_);
lean_inc(v_a_3406_);
lean_inc(v_a_3426_);
lean_inc(v_a_3397_);
lean_inc(v_x_3389_);
lean_inc(v_a_3399_);
lean_inc(v_h_x3f_3381_);
lean_inc(v_a_3434_);
lean_inc(v_a_3416_);
v___y_3334_ = v_monadInfo_3435_;
v___y_3335_ = v_a_3416_;
v___y_3336_ = v_a_3434_;
v___y_3337_ = v_body_3427_;
v___y_3338_ = v_h_x3f_3381_;
v___y_3339_ = v___f_3440_;
v___y_3340_ = v_a_3399_;
v___y_3341_ = v_x_3389_;
v___y_3342_ = v___f_3437_;
v___y_3343_ = v_a_3431_;
v___y_3344_ = v_a_3397_;
v___y_3345_ = v___f_3438_;
v___y_3346_ = v___x_3391_;
v___y_3347_ = v_a_3426_;
v___y_3348_ = v_a_3406_;
v___y_3349_ = v___y_3384_;
v___y_3350_ = v___y_3382_;
v___y_3351_ = v_a_3416_;
v___y_3352_ = v___y_3383_;
v___y_3353_ = v_a_3434_;
v___y_3354_ = v_h_x3f_3381_;
v___y_3355_ = v___y_3387_;
v___y_3356_ = v_a_3399_;
v___y_3357_ = v___y_3388_;
v___y_3358_ = v___y_3385_;
v___y_3359_ = v_x_3389_;
v___y_3360_ = v_a_3397_;
v___y_3361_ = v_a_3429_;
v___y_3362_ = v___x_3403_;
v___y_3363_ = v___y_3386_;
v___y_3364_ = v_a_3406_;
v___y_3365_ = v_a_3426_;
v___y_3366_ = v___x_3450_;
goto v___jp_3333_;
}
}
}
else
{
lean_object* v_a_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3458_; 
lean_dec(v_a_3431_);
lean_dec(v_a_3429_);
lean_dec(v_body_3427_);
lean_dec(v_a_3426_);
lean_dec(v_a_3416_);
lean_dec(v_a_3406_);
lean_dec(v_a_3399_);
lean_dec(v_a_3397_);
lean_dec(v_x_3389_);
lean_dec(v_h_x3f_3381_);
lean_dec_ref(v_dec_3021_);
v_a_3451_ = lean_ctor_get(v___x_3433_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3433_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3453_ = v___x_3433_;
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_a_3451_);
lean_dec(v___x_3433_);
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
else
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3466_; 
lean_dec(v_a_3429_);
lean_dec(v_body_3427_);
lean_dec(v_a_3426_);
lean_dec(v_a_3416_);
lean_dec(v_a_3406_);
lean_dec(v_a_3399_);
lean_dec(v_a_3397_);
lean_dec(v_x_3389_);
lean_dec(v_h_x3f_3381_);
lean_dec_ref(v_dec_3021_);
v_a_3459_ = lean_ctor_get(v___x_3430_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3461_ = v___x_3430_;
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3430_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3464_; 
if (v_isShared_3462_ == 0)
{
v___x_3464_ = v___x_3461_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3459_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
}
}
else
{
lean_object* v_a_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3474_; 
lean_dec(v_body_3427_);
lean_dec(v_a_3426_);
lean_dec(v_a_3416_);
lean_dec(v_a_3406_);
lean_dec(v_a_3399_);
lean_dec(v_a_3397_);
lean_dec(v_x_3389_);
lean_dec(v_h_x3f_3381_);
lean_dec_ref(v_dec_3021_);
v_a_3467_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3469_ = v___x_3428_;
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_a_3467_);
lean_dec(v___x_3428_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3472_; 
if (v_isShared_3470_ == 0)
{
v___x_3472_ = v___x_3469_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_a_3467_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
}
}
else
{
lean_dec(v_a_3416_);
lean_dec(v_a_3406_);
lean_dec(v_a_3399_);
lean_dec(v_a_3397_);
lean_dec(v_x_3389_);
lean_dec(v_h_x3f_3381_);
lean_dec_ref(v_dec_3021_);
lean_dec(v_stx_3020_);
return v___x_3425_;
}
}
}
}
else
{
lean_dec(v_a_3406_);
lean_dec(v_a_3399_);
lean_dec(v_a_3397_);
lean_dec(v_x_3389_);
lean_dec(v_h_x3f_3381_);
lean_dec(v___x_3038_);
lean_dec_ref(v_dec_3021_);
lean_dec(v_stx_3020_);
return v___x_3415_;
}
}
}
}
else
{
lean_dec(v_a_3399_);
lean_dec(v_a_3397_);
lean_dec(v_x_3389_);
lean_dec(v_h_x3f_3381_);
lean_dec(v___x_3038_);
lean_dec_ref(v_dec_3021_);
lean_dec(v_stx_3020_);
return v___x_3405_;
}
}
else
{
lean_object* v_a_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3486_; 
lean_dec(v_a_3397_);
lean_dec(v_x_3389_);
lean_dec(v_h_x3f_3381_);
lean_dec(v___x_3038_);
lean_dec_ref(v_dec_3021_);
lean_dec(v_stx_3020_);
v_a_3479_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3481_ = v___x_3398_;
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_a_3479_);
lean_dec(v___x_3398_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3484_; 
if (v_isShared_3482_ == 0)
{
v___x_3484_ = v___x_3481_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_a_3479_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
}
}
else
{
lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3494_; 
lean_dec(v_x_3389_);
lean_dec(v_h_x3f_3381_);
lean_dec(v___x_3038_);
lean_dec_ref(v_dec_3021_);
lean_dec(v_stx_3020_);
v_a_3487_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3489_ = v___x_3396_;
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_dec(v___x_3396_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3492_; 
if (v_isShared_3490_ == 0)
{
v___x_3492_ = v___x_3489_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v_a_3487_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
}
else
{
lean_object* v_a_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3502_; 
lean_dec(v_x_3389_);
lean_dec(v_h_x3f_3381_);
lean_dec(v___x_3038_);
lean_dec_ref(v_dec_3021_);
lean_dec(v_stx_3020_);
v_a_3495_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3497_ = v___x_3395_;
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_a_3495_);
lean_dec(v___x_3395_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v___x_3500_; 
if (v_isShared_3498_ == 0)
{
v___x_3500_ = v___x_3497_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_a_3495_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___boxed(lean_object* v_stx_3512_, lean_object* v_dec_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_){
_start:
{
lean_object* v_res_3522_; 
v_res_3522_ = l_Lean_Elab_Do_elabDoFor(v_stx_3512_, v_dec_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_, v_a_3519_, v_a_3520_);
lean_dec(v_a_3520_);
lean_dec_ref(v_a_3519_);
lean_dec(v_a_3518_);
lean_dec_ref(v_a_3517_);
lean_dec(v_a_3516_);
lean_dec_ref(v_a_3515_);
lean_dec_ref(v_a_3514_);
return v_res_3522_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2(lean_object* v_00_u03b1_3523_, lean_object* v_msg_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_){
_start:
{
lean_object* v___x_3532_; 
v___x_3532_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v_msg_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___boxed(lean_object* v_00_u03b1_3533_, lean_object* v_msg_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_){
_start:
{
lean_object* v_res_3542_; 
v_res_3542_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2(v_00_u03b1_3533_, v_msg_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_);
lean_dec(v___y_3540_);
lean_dec_ref(v___y_3539_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3537_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
return v_res_3542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5(lean_object* v_00_u03b1_3543_, lean_object* v_name_3544_, lean_object* v_type_3545_, lean_object* v_k_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
lean_object* v___x_3555_; 
v___x_3555_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(v_name_3544_, v_type_3545_, v_k_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
return v___x_3555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___boxed(lean_object* v_00_u03b1_3556_, lean_object* v_name_3557_, lean_object* v_type_3558_, lean_object* v_k_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_){
_start:
{
lean_object* v_res_3568_; 
v_res_3568_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5(v_00_u03b1_3556_, v_name_3557_, v_type_3558_, v_k_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
lean_dec(v___y_3564_);
lean_dec_ref(v___y_3563_);
lean_dec(v___y_3562_);
lean_dec_ref(v___y_3561_);
lean_dec_ref(v___y_3560_);
return v_res_3568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3(lean_object* v_msgData_3569_, lean_object* v_macroStack_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_){
_start:
{
lean_object* v___x_3578_; 
v___x_3578_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(v_msgData_3569_, v_macroStack_3570_, v___y_3575_);
return v___x_3578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___boxed(lean_object* v_msgData_3579_, lean_object* v_macroStack_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_){
_start:
{
lean_object* v_res_3588_; 
v_res_3588_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3(v_msgData_3579_, v_macroStack_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
lean_dec(v___y_3582_);
lean_dec_ref(v___y_3581_);
return v_res_3588_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14(lean_object* v_ref_3589_, lean_object* v_msgData_3590_, uint8_t v_severity_3591_, uint8_t v_isSilent_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_){
_start:
{
lean_object* v___x_3601_; 
v___x_3601_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___redArg(v_ref_3589_, v_msgData_3590_, v_severity_3591_, v_isSilent_3592_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
return v___x_3601_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14___boxed(lean_object* v_ref_3602_, lean_object* v_msgData_3603_, lean_object* v_severity_3604_, lean_object* v_isSilent_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_){
_start:
{
uint8_t v_severity_boxed_3614_; uint8_t v_isSilent_boxed_3615_; lean_object* v_res_3616_; 
v_severity_boxed_3614_ = lean_unbox(v_severity_3604_);
v_isSilent_boxed_3615_ = lean_unbox(v_isSilent_3605_);
v_res_3616_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_Do_elabDoFor_spec__6_spec__10_spec__14(v_ref_3602_, v_msgData_3603_, v_severity_boxed_3614_, v_isSilent_boxed_3615_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec(v___y_3610_);
lean_dec_ref(v___y_3609_);
lean_dec(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec_ref(v___y_3606_);
lean_dec(v_ref_3602_);
return v_res_3616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1(){
_start:
{
lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; 
v___x_3624_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_3625_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
v___x_3626_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1));
v___x_3627_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___boxed), 10, 0);
v___x_3628_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3624_, v___x_3625_, v___x_3626_, v___x_3627_);
return v___x_3628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___boxed(lean_object* v_a_3629_){
_start:
{
lean_object* v_res_3630_; 
v_res_3630_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1();
return v_res_3630_;
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
res = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1();
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
