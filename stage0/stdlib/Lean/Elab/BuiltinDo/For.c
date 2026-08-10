// Lean compiler output
// Module: Lean.Elab.BuiltinDo.For
// Imports: public import Lean.Elab.BuiltinDo.Basic meta import Lean.Parser.Do import Init.Control.Do import Init.While import Lean.Meta.ProdN
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
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkProdMkN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_mkPureApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDoSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_enterLoopBody___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_bindMutVarsFromTuple(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray2___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_Do_MutVar_getId(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_getLocalDeclFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Elab_Term_addTermInfo_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSome(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_mkMonadApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_continueWithUnit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSimpleThunk(lean_object*);
lean_object* l_Lean_Meta_getFVarFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_mkBindApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_exprToSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkInstMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_ensureUnitAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_checkMutVarsForShadowing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_getReturnCont___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doFor"};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__0 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 12, 178, 2, 144, 97, 71, 235)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__1 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__2_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__2_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__2_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75_value),LEAN_SCALAR_PTR_LITERAL(220, 154, 41, 109, 103, 76, 110, 63)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__2 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__3 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "in"};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__4 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__4_value;
static const lean_array_object l_Lean_Elab_Do_expandDoFor___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__5 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__6_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__6_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__6_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__6 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__6_value;
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "for"};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__7 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__7_value;
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
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
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "The `invariant` clause takes a `for` loop over a single collection."};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__15 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__15_value;
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "doForInvariant"};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__16 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__17_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__17_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__17_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__16_value),LEAN_SCALAR_PTR_LITERAL(21, 233, 74, 150, 27, 16, 165, 242)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__17 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__17_value;
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__18 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__18_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__19 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__19_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "expandDoFor"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 157, 21, 52, 135, 185, 36, 254)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__0_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__0_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__0_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 129, .m_capacity = 129, .m_length = 128, .m_data = "The `invariant` clause is stated over this class, which says that iterating the container produces its elements without effects."};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__2;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__3;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__4_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "PureForIn"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__5 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(147, 246, 122, 181, 55, 202, 108, 55)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__6 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__6_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "PureForIn'"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__7 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(53, 225, 86, 37, 42, 243, 162, 173)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__8 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 95, .m_capacity = 95, .m_length = 94, .m_data = "the `invariant` clause elaborates to a `vcgen` gadget; add `import Std.Internal.Do` to use it."};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__1;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ForIn"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__2_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "forInWithInvariant"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__4_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__2_value),LEAN_SCALAR_PTR_LITERAL(1, 144, 23, 37, 138, 194, 167, 30)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__4_value_aux_3),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__3_value),LEAN_SCALAR_PTR_LITERAL(216, 106, 59, 179, 156, 229, 113, 6)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__4_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__5 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__5_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ForIn'"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__6 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__6_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "forInWithInvariant'"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__7 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__8_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__6_value),LEAN_SCALAR_PTR_LITERAL(213, 93, 110, 114, 180, 94, 138, 151)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__7_value),LEAN_SCALAR_PTR_LITERAL(190, 73, 23, 142, 83, 242, 60, 31)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__8 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__8_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "anonymousCtor"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__9 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__9_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__10 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__10_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__11 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__11_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__12 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__13_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__13_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__12_value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__13 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__13_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 108, .m_capacity = 108, .m_length = 107, .m_data = "The `invariant` clause takes at least two binders: the elements consumed so far and the elements remaining."};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__14 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__14_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__15;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__16 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__17_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__17_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__17_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__16_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__17 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__17_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 164, .m_capacity = 164, .m_length = 162, .m_data = "The `invariant` clause takes no type ascription covering all its binders; ascribe the type on an individual binder, as in `invariant (pref : List α) suff => ...`."};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__18 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__18_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__19;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unit"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__3___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(87, 186, 243, 194, 96, 12, 218, 7)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoFor___lam__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___closed__3;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = " but the info said there is no early return"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoFor___lam__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___closed__5;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Early returning "};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoFor___lam__3___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___closed__7;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "<not-available>"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___closed__8 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__8_value)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___closed__9 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoFor___lam__3___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "r"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(201, 206, 29, 183, 206, 15, 98, 41)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(168, 60, 211, 188, 58, 220, 100, 184)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__2_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Break"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "runK"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__4_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "match_1"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___closed__5 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__4___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__3_value),LEAN_SCALAR_PTR_LITERAL(25, 204, 143, 3, 84, 67, 92, 151)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__4___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 178, 64, 100, 79, 118, 122, 28)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__5_value),LEAN_SCALAR_PTR_LITERAL(199, 194, 234, 57, 172, 104, 157, 179)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__6_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prod"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___closed__7 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__7_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fst"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___closed__8 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__4___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__7_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__4___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__8_value),LEAN_SCALAR_PTR_LITERAL(170, 44, 236, 58, 247, 164, 254, 114)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___closed__9 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__4___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "done"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__6___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__6___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "yield"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__7___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__7___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ForInStep"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__0_value),LEAN_SCALAR_PTR_LITERAL(153, 23, 255, 201, 194, 179, 65, 111)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__10___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__11___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Membership"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__12___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__12___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mem"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__12___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__12___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__12___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__12___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 217, 109, 94, 255, 55, 82, 109)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__12___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__12___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__12___closed__1_value),LEAN_SCALAR_PTR_LITERAL(224, 90, 126, 237, 128, 148, 153, 69)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__12___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__12___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__1;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__2 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__3 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__4 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__5 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__5_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__6 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__6_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__7 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6___closed__0 = (const lean_object*)&l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__2_value),LEAN_SCALAR_PTR_LITERAL(223, 152, 230, 155, 97, 233, 45, 158)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "forIn"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__2_value),LEAN_SCALAR_PTR_LITERAL(223, 152, 230, 155, 97, 233, 45, 158)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__1_value),LEAN_SCALAR_PTR_LITERAL(9, 12, 142, 239, 44, 138, 10, 93)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__12___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 217, 109, 94, 255, 55, 82, 109)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "d"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__4_value),LEAN_SCALAR_PTR_LITERAL(48, 234, 148, 175, 115, 149, 2, 231)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__5 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 251, 229, 162, 252, 35, 196, 120)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__6_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "forIn'"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__7 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 251, 229, 162, 252, 35, 196, 120)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__7_value),LEAN_SCALAR_PTR_LITERAL(10, 254, 232, 131, 195, 189, 138, 93)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__8 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__8_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "α"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__9 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__9_value),LEAN_SCALAR_PTR_LITERAL(102, 24, 27, 80, 217, 159, 184, 13)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__10 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__10_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "ρ"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__11 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__11_value),LEAN_SCALAR_PTR_LITERAL(148, 87, 172, 24, 54, 35, 28, 246)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__12 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__12_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "__r"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__13 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__13_value),LEAN_SCALAR_PTR_LITERAL(38, 26, 183, 93, 43, 136, 227, 87)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__14 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__14_value;
static const lean_array_object l_Lean_Elab_Do_elabDoFor___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__15 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__15_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v___x_402_, 2);
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
lean_dec_ref_known(v___x_217_, 2);
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
lean_dec_ref_known(v___x_236_, 3);
lean_dec(v___x_232_);
lean_dec_ref_known(v___x_229_, 2);
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
uint8_t v___x_193532__boxed_428_; lean_object* v_res_429_; 
v___x_193532__boxed_428_ = lean_unbox(v___x_416_);
v_res_429_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(v___x_413_, v___x_414_, v___x_415_, v___x_193532__boxed_428_, v___x_417_, v___x_418_, v___x_419_, v___f_420_, v_fst_421_, v___x_422_, v_snd_423_, v_x_424_, v_h_x3f_425_, v___y_426_, v___y_427_);
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
uint8_t v___x_194138__boxed_440_; lean_object* v_res_441_; 
v___x_194138__boxed_440_ = lean_unbox(v___x_436_);
v_res_441_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0(v___x_194138__boxed_440_, v_____do__lift_437_, v___y_438_, v___y_439_);
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
lean_dec_ref_known(v___x_505_, 2);
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
lean_dec_ref_known(v___x_529_, 2);
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
lean_dec_ref_known(v___x_546_, 1);
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
lean_dec_ref_known(v_a_480_, 1);
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
lean_dec_ref_known(v___y_479_, 2);
v_a_492_ = lean_ctor_get(v_a_480_, 0);
lean_inc(v_a_492_);
lean_dec_ref_known(v_a_480_, 1);
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
uint8_t v___x_194174__boxed_559_; lean_object* v_res_560_; 
v___x_194174__boxed_559_ = lean_unbox(v___x_554_);
v_res_560_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_194174__boxed_559_, v_a_555_, v_b_556_, v___y_557_, v___y_558_);
lean_dec_ref(v___y_557_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg(uint8_t v___x_561_, lean_object* v_a_562_, lean_object* v_b_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v_array_566_; lean_object* v_start_567_; lean_object* v_stop_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_662_; 
v_array_566_ = lean_ctor_get(v_a_562_, 0);
v_start_567_ = lean_ctor_get(v_a_562_, 1);
v_stop_568_ = lean_ctor_get(v_a_562_, 2);
v_isSharedCheck_662_ = !lean_is_exclusive(v_a_562_);
if (v_isSharedCheck_662_ == 0)
{
v___x_570_ = v_a_562_;
v_isShared_571_ = v_isSharedCheck_662_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_stop_568_);
lean_inc(v_start_567_);
lean_inc(v_array_566_);
lean_dec(v_a_562_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_662_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
uint8_t v___x_572_; 
v___x_572_ = lean_nat_dec_lt(v_start_567_, v_stop_568_);
if (v___x_572_ == 0)
{
lean_object* v___x_573_; 
lean_del_object(v___x_570_);
lean_dec(v_stop_568_);
lean_dec(v_start_567_);
lean_dec_ref(v_array_566_);
v___x_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_573_, 0, v_b_563_);
lean_ctor_set(v___x_573_, 1, v___y_565_);
return v___x_573_;
}
else
{
lean_object* v_fst_574_; lean_object* v_snd_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_661_; 
v_fst_574_ = lean_ctor_get(v_b_563_, 0);
v_snd_575_ = lean_ctor_get(v_b_563_, 1);
v_isSharedCheck_661_ = !lean_is_exclusive(v_b_563_);
if (v_isSharedCheck_661_ == 0)
{
v___x_577_ = v_b_563_;
v_isShared_578_ = v_isSharedCheck_661_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_snd_575_);
lean_inc(v_fst_574_);
lean_dec(v_b_563_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_661_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_579_ = lean_unsigned_to_nat(1u);
v___x_580_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0));
v___x_581_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1));
v___x_582_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2));
v___x_583_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
v___x_584_ = lean_nat_add(v_start_567_, v___x_579_);
lean_inc_ref(v_array_566_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 1, v___x_584_);
v___x_586_ = v___x_570_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_array_566_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_660_, 2, v_stop_568_);
v___x_586_ = v_reuseFailAlloc_660_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___y_588_; lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_612_ = lean_array_fget(v_array_566_, v_start_567_);
lean_dec(v_start_567_);
lean_dec_ref(v_array_566_);
lean_inc(v___x_612_);
v___x_613_ = l_Lean_Syntax_isOfKind(v___x_612_, v___x_583_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; 
lean_dec(v___x_612_);
v___x_614_ = l_Lean_Macro_throwUnsupported___redArg(v___y_565_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v___x_617_; 
v_a_615_ = lean_ctor_get(v___x_614_, 1);
lean_inc(v_a_615_);
lean_dec_ref_known(v___x_614_, 2);
if (v_isShared_578_ == 0)
{
v___x_617_ = v___x_577_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_fst_574_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_snd_575_);
v___x_617_ = v_reuseFailAlloc_619_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
v_a_562_ = v___x_586_;
v_b_563_ = v___x_617_;
v___y_565_ = v_a_615_;
goto _start;
}
}
else
{
lean_object* v_a_620_; lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_dec_ref(v___x_586_);
lean_del_object(v___x_577_);
lean_dec(v_snd_575_);
lean_dec(v_fst_574_);
v_a_620_ = lean_ctor_get(v___x_614_, 0);
v_a_621_ = lean_ctor_get(v___x_614_, 1);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_614_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_inc(v_a_620_);
lean_dec(v___x_614_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_620_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
else
{
lean_object* v___x_629_; lean_object* v___f_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_629_ = lean_box(v___x_561_);
v___f_630_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_630_, 0, v___x_629_);
v___x_631_ = lean_unsigned_to_nat(3u);
v___x_632_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__5));
v___x_633_ = lean_unsigned_to_nat(0u);
v___x_634_ = l_Lean_Syntax_getArg(v___x_612_, v___x_633_);
v___x_635_ = l_Lean_Syntax_isNone(v___x_634_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_636_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_634_);
v___x_637_ = l_Lean_Syntax_matchesNull(v___x_634_, v___x_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; 
lean_dec(v___x_634_);
lean_dec_ref(v___f_630_);
lean_dec(v___x_612_);
v___x_638_ = l_Lean_Macro_throwUnsupported___redArg(v___y_565_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_641_; 
v_a_639_ = lean_ctor_get(v___x_638_, 1);
lean_inc(v_a_639_);
lean_dec_ref_known(v___x_638_, 2);
if (v_isShared_578_ == 0)
{
v___x_641_ = v___x_577_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_fst_574_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_snd_575_);
v___x_641_ = v_reuseFailAlloc_643_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
v_a_562_ = v___x_586_;
v_b_563_ = v___x_641_;
v___y_565_ = v_a_639_;
goto _start;
}
}
else
{
lean_object* v_a_644_; lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
lean_dec_ref(v___x_586_);
lean_del_object(v___x_577_);
lean_dec(v_snd_575_);
lean_dec(v_fst_574_);
v_a_644_ = lean_ctor_get(v___x_638_, 0);
v_a_645_ = lean_ctor_get(v___x_638_, 1);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_638_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_inc(v_a_644_);
lean_dec(v___x_638_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_644_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
else
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
lean_del_object(v___x_577_);
v___x_653_ = l_Lean_Syntax_getArg(v___x_634_, v___x_633_);
lean_dec(v___x_634_);
v___x_654_ = lean_box(0);
v___x_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_653_);
v___x_656_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(v___x_612_, v___x_579_, v___x_631_, v___x_561_, v___x_580_, v___x_581_, v___x_582_, v___f_630_, v_fst_574_, v___x_632_, v_snd_575_, v___x_654_, v___x_655_, v___y_564_, v___y_565_);
lean_dec_ref_known(v___x_655_, 1);
lean_dec(v___x_612_);
v___y_588_ = v___x_656_;
goto v___jp_587_;
}
}
else
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
lean_dec(v___x_634_);
lean_del_object(v___x_577_);
v___x_657_ = lean_box(0);
v___x_658_ = lean_box(0);
v___x_659_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(v___x_612_, v___x_579_, v___x_631_, v___x_561_, v___x_580_, v___x_581_, v___x_582_, v___f_630_, v_fst_574_, v___x_632_, v_snd_575_, v___x_657_, v___x_658_, v___y_564_, v___y_565_);
lean_dec(v___x_612_);
v___y_588_ = v___x_659_;
goto v___jp_587_;
}
}
v___jp_587_:
{
if (lean_obj_tag(v___y_588_) == 0)
{
lean_object* v_a_589_; 
v_a_589_ = lean_ctor_get(v___y_588_, 0);
lean_inc(v_a_589_);
if (lean_obj_tag(v_a_589_) == 0)
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_598_; 
lean_dec_ref(v___x_586_);
v_a_590_ = lean_ctor_get(v___y_588_, 1);
v_isSharedCheck_598_ = !lean_is_exclusive(v___y_588_);
if (v_isSharedCheck_598_ == 0)
{
lean_object* v_unused_599_; 
v_unused_599_ = lean_ctor_get(v___y_588_, 0);
lean_dec(v_unused_599_);
v___x_592_ = v___y_588_;
v_isShared_593_ = v_isSharedCheck_598_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___y_588_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_598_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v_a_594_; lean_object* v___x_596_; 
v_a_594_ = lean_ctor_get(v_a_589_, 0);
lean_inc(v_a_594_);
lean_dec_ref_known(v_a_589_, 1);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v_a_594_);
v___x_596_ = v___x_592_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_594_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_a_590_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
else
{
lean_object* v_a_600_; lean_object* v_a_601_; 
v_a_600_ = lean_ctor_get(v___y_588_, 1);
lean_inc(v_a_600_);
lean_dec_ref_known(v___y_588_, 2);
v_a_601_ = lean_ctor_get(v_a_589_, 0);
lean_inc(v_a_601_);
lean_dec_ref_known(v_a_589_, 1);
v_a_562_ = v___x_586_;
v_b_563_ = v_a_601_;
v___y_565_ = v_a_600_;
goto _start;
}
}
else
{
lean_object* v_a_603_; lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec_ref(v___x_586_);
v_a_603_ = lean_ctor_get(v___y_588_, 0);
v_a_604_ = lean_ctor_get(v___y_588_, 1);
v_isSharedCheck_611_ = !lean_is_exclusive(v___y_588_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___y_588_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_inc(v_a_603_);
lean_dec(v___y_588_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_603_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___boxed(lean_object* v___x_663_, lean_object* v_a_664_, lean_object* v_b_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
uint8_t v___x_194389__boxed_668_; lean_object* v_res_669_; 
v___x_194389__boxed_668_ = lean_unbox(v___x_663_);
v_res_669_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg(v___x_194389__boxed_668_, v_a_664_, v_b_665_, v___y_666_, v___y_667_);
lean_dec_ref(v___y_666_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor(lean_object* v_stx_733_, lean_object* v_a_734_, lean_object* v_a_735_){
_start:
{
lean_object* v___x_736_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___y_823_; lean_object* v___y_824_; lean_object* v___y_825_; uint8_t v___x_841_; 
v___x_736_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
lean_inc(v_stx_733_);
v___x_841_ = l_Lean_Syntax_isOfKind(v_stx_733_, v___x_736_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; 
lean_dec(v_stx_733_);
v___x_842_ = l_Lean_Macro_throwUnsupported___redArg(v_a_735_);
return v___x_842_;
}
else
{
lean_object* v___x_843_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v_tk_867_; lean_object* v___x_868_; lean_object* v___x_869_; uint8_t v___x_870_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v_x_878_; lean_object* v_body_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; lean_object* v_h_x3f_925_; lean_object* v___y_926_; lean_object* v___y_927_; 
v___x_843_ = lean_unsigned_to_nat(0u);
v_tk_867_ = l_Lean_Syntax_getArg(v_stx_733_, v___x_843_);
v___x_868_ = lean_unsigned_to_nat(1u);
v___x_869_ = l_Lean_Syntax_getArg(v_stx_733_, v___x_868_);
lean_inc(v___x_869_);
v___x_870_ = l_Lean_Syntax_matchesNull(v___x_869_, v___x_868_);
if (v___x_870_ == 0)
{
lean_object* v___x_988_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___y_995_; lean_object* v___y_996_; lean_object* v_inv_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v___x_988_ = lean_unsigned_to_nat(2u);
v___x_1033_ = l_Lean_Syntax_getArg(v_stx_733_, v___x_988_);
v___x_1034_ = l_Lean_Syntax_isNone(v___x_1033_);
if (v___x_1034_ == 0)
{
uint8_t v___x_1035_; 
lean_inc(v___x_1033_);
v___x_1035_ = l_Lean_Syntax_matchesNull(v___x_1033_, v___x_868_);
if (v___x_1035_ == 0)
{
lean_object* v___x_1036_; 
lean_dec(v___x_1033_);
lean_dec(v___x_869_);
lean_dec(v_tk_867_);
lean_dec(v_stx_733_);
v___x_1036_ = l_Lean_Macro_throwUnsupported___redArg(v_a_735_);
return v___x_1036_;
}
else
{
lean_object* v_inv_1037_; lean_object* v___x_1038_; uint8_t v___x_1039_; 
v_inv_1037_ = l_Lean_Syntax_getArg(v___x_1033_, v___x_843_);
lean_dec(v___x_1033_);
v___x_1038_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v_inv_1037_);
v___x_1039_ = l_Lean_Syntax_isOfKind(v_inv_1037_, v___x_1038_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; 
lean_dec(v_inv_1037_);
lean_dec(v___x_869_);
lean_dec(v_tk_867_);
lean_dec(v_stx_733_);
v___x_1040_ = l_Lean_Macro_throwUnsupported___redArg(v_a_735_);
return v___x_1040_;
}
else
{
lean_object* v___x_1041_; 
v___x_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1041_, 0, v_inv_1037_);
v_inv_1009_ = v___x_1041_;
v___y_1010_ = v_a_734_;
v___y_1011_ = v_a_735_;
goto v___jp_1008_;
}
}
}
else
{
lean_object* v___x_1042_; 
lean_dec(v___x_1033_);
v___x_1042_ = lean_box(0);
v_inv_1009_ = v___x_1042_;
v___y_1010_ = v_a_734_;
v___y_1011_ = v_a_735_;
goto v___jp_1008_;
}
v___jp_989_:
{
lean_object* v___x_997_; lean_object* v___x_998_; uint8_t v___x_999_; 
v___x_997_ = lean_box(0);
v___x_998_ = lean_array_get(v___x_997_, v___y_991_, v___x_843_);
lean_inc(v___x_998_);
v___x_999_ = l_Lean_Syntax_isOfKind(v___x_998_, v___y_990_);
if (v___x_999_ == 0)
{
lean_object* v___x_1000_; 
lean_dec(v___x_998_);
lean_dec(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v_tk_867_);
v___x_1000_ = l_Lean_Macro_throwUnsupported___redArg(v___y_996_);
return v___x_1000_;
}
else
{
lean_object* v___x_1001_; uint8_t v___x_1002_; 
v___x_1001_ = l_Lean_Syntax_getArg(v___x_998_, v___x_843_);
v___x_1002_ = l_Lean_Syntax_isNone(v___x_1001_);
if (v___x_1002_ == 0)
{
uint8_t v___x_1003_; 
lean_inc(v___x_1001_);
v___x_1003_ = l_Lean_Syntax_matchesNull(v___x_1001_, v___x_988_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; 
lean_dec(v___x_1001_);
lean_dec(v___x_998_);
lean_dec(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v_tk_867_);
v___x_1004_ = l_Lean_Macro_throwUnsupported___redArg(v___y_996_);
return v___x_1004_;
}
else
{
lean_object* v_h_x3f_1005_; lean_object* v___x_1006_; 
v_h_x3f_1005_ = l_Lean_Syntax_getArg(v___x_1001_, v___x_843_);
lean_dec(v___x_1001_);
v___x_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1006_, 0, v_h_x3f_1005_);
v___y_919_ = v___y_991_;
v___y_920_ = v___y_990_;
v___y_921_ = v___y_992_;
v___y_922_ = v___y_993_;
v___y_923_ = v___y_994_;
v___y_924_ = v___x_998_;
v_h_x3f_925_ = v___x_1006_;
v___y_926_ = v___y_995_;
v___y_927_ = v___y_996_;
goto v___jp_918_;
}
}
else
{
lean_object* v___x_1007_; 
lean_dec(v___x_1001_);
v___x_1007_ = lean_box(0);
v___y_919_ = v___y_991_;
v___y_920_ = v___y_990_;
v___y_921_ = v___y_992_;
v___y_922_ = v___y_993_;
v___y_923_ = v___y_994_;
v___y_924_ = v___x_998_;
v_h_x3f_925_ = v___x_1007_;
v___y_926_ = v___y_995_;
v___y_927_ = v___y_996_;
goto v___jp_918_;
}
}
}
v___jp_1008_:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v_body_1014_; lean_object* v___x_1015_; lean_object* v_decls_1016_; lean_object* v_decls_1017_; 
v___x_1012_ = lean_unsigned_to_nat(3u);
v___x_1013_ = lean_unsigned_to_nat(4u);
v_body_1014_ = l_Lean_Syntax_getArg(v_stx_733_, v___x_1013_);
lean_dec(v_stx_733_);
v___x_1015_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
v_decls_1016_ = l_Lean_Syntax_getArgs(v___x_869_);
lean_dec(v___x_869_);
v_decls_1017_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_1016_);
lean_dec_ref(v_decls_1016_);
if (lean_obj_tag(v_inv_1009_) == 1)
{
lean_object* v_val_1018_; lean_object* v___x_1019_; uint8_t v___x_1020_; 
v_val_1018_ = lean_ctor_get(v_inv_1009_, 0);
v___x_1019_ = lean_array_get_size(v_decls_1017_);
v___x_1020_ = lean_nat_dec_lt(v___x_868_, v___x_1019_);
if (v___x_1020_ == 0)
{
v___y_990_ = v___x_1015_;
v___y_991_ = v_decls_1017_;
v___y_992_ = v_body_1014_;
v___y_993_ = v_inv_1009_;
v___y_994_ = v___x_1012_;
v___y_995_ = v___y_1010_;
v___y_996_ = v___y_1011_;
goto v___jp_989_;
}
else
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__15));
v___x_1022_ = l_Lean_Macro_throwErrorAt___redArg(v_val_1018_, v___x_1021_, v___y_1010_, v___y_1011_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 1);
lean_inc(v_a_1023_);
lean_dec_ref_known(v___x_1022_, 2);
v___y_990_ = v___x_1015_;
v___y_991_ = v_decls_1017_;
v___y_992_ = v_body_1014_;
v___y_993_ = v_inv_1009_;
v___y_994_ = v___x_1012_;
v___y_995_ = v___y_1010_;
v___y_996_ = v_a_1023_;
goto v___jp_989_;
}
else
{
lean_object* v_a_1024_; lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
lean_dec_ref_known(v_inv_1009_, 1);
lean_dec_ref(v_decls_1017_);
lean_dec(v_body_1014_);
lean_dec(v_tk_867_);
v_a_1024_ = lean_ctor_get(v___x_1022_, 0);
v_a_1025_ = lean_ctor_get(v___x_1022_, 1);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_1022_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_inc(v_a_1024_);
lean_dec(v___x_1022_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1024_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_a_1025_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
}
else
{
v___y_990_ = v___x_1015_;
v___y_991_ = v_decls_1017_;
v___y_992_ = v_body_1014_;
v___y_993_ = v_inv_1009_;
v___y_994_ = v___x_1012_;
v___y_995_ = v___y_1010_;
v___y_996_ = v___y_1011_;
goto v___jp_989_;
}
}
}
else
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___y_1057_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; uint8_t v___y_1095_; lean_object* v_x_1096_; lean_object* v_body_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; uint8_t v___y_1142_; lean_object* v_h_x3f_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; uint8_t v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1227_; lean_object* v___y_1228_; uint8_t v___y_1229_; lean_object* v_inv_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1288_; lean_object* v___y_1289_; uint8_t v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v_x_1294_; lean_object* v_body_1295_; lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; uint8_t v___y_1339_; lean_object* v___y_1340_; lean_object* v_h_x3f_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; uint8_t v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; uint8_t v___x_1494_; lean_object* v___y_1496_; lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v___y_1499_; lean_object* v___y_1500_; lean_object* v_x_1501_; lean_object* v_body_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v_h_x3f_1547_; lean_object* v___y_1548_; lean_object* v___y_1549_; 
v___x_1043_ = l_Lean_Syntax_getArg(v___x_869_, v___x_843_);
v___x_1044_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
lean_inc(v___x_1043_);
v___x_1494_ = l_Lean_Syntax_isOfKind(v___x_1043_, v___x_1044_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1610_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v_inv_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___x_1653_; uint8_t v___x_1654_; 
lean_dec(v___x_1043_);
v___x_1610_ = lean_unsigned_to_nat(2u);
v___x_1653_ = l_Lean_Syntax_getArg(v_stx_733_, v___x_1610_);
v___x_1654_ = l_Lean_Syntax_isNone(v___x_1653_);
if (v___x_1654_ == 0)
{
uint8_t v___x_1655_; 
lean_inc(v___x_1653_);
v___x_1655_ = l_Lean_Syntax_matchesNull(v___x_1653_, v___x_868_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; 
lean_dec(v___x_1653_);
lean_dec(v___x_869_);
lean_dec(v_tk_867_);
lean_dec(v_stx_733_);
v___x_1656_ = l_Lean_Macro_throwUnsupported___redArg(v_a_735_);
return v___x_1656_;
}
else
{
lean_object* v_inv_1657_; lean_object* v___x_1658_; uint8_t v___x_1659_; 
v_inv_1657_ = l_Lean_Syntax_getArg(v___x_1653_, v___x_843_);
lean_dec(v___x_1653_);
v___x_1658_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v_inv_1657_);
v___x_1659_ = l_Lean_Syntax_isOfKind(v_inv_1657_, v___x_1658_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; 
lean_dec(v_inv_1657_);
lean_dec(v___x_869_);
lean_dec(v_tk_867_);
lean_dec(v_stx_733_);
v___x_1660_ = l_Lean_Macro_throwUnsupported___redArg(v_a_735_);
return v___x_1660_;
}
else
{
lean_object* v___x_1661_; 
v___x_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1661_, 0, v_inv_1657_);
v_inv_1630_ = v___x_1661_;
v___y_1631_ = v_a_734_;
v___y_1632_ = v_a_735_;
goto v___jp_1629_;
}
}
}
else
{
lean_object* v___x_1662_; 
lean_dec(v___x_1653_);
v___x_1662_ = lean_box(0);
v_inv_1630_ = v___x_1662_;
v___y_1631_ = v_a_734_;
v___y_1632_ = v_a_735_;
goto v___jp_1629_;
}
v___jp_1611_:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; uint8_t v___x_1620_; 
v___x_1618_ = lean_box(0);
v___x_1619_ = lean_array_get(v___x_1618_, v___y_1615_, v___x_843_);
lean_inc(v___x_1619_);
v___x_1620_ = l_Lean_Syntax_isOfKind(v___x_1619_, v___x_1044_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; 
lean_dec(v___x_1619_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec(v_tk_867_);
v___x_1621_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1617_);
return v___x_1621_;
}
else
{
lean_object* v___x_1622_; uint8_t v___x_1623_; 
v___x_1622_ = l_Lean_Syntax_getArg(v___x_1619_, v___x_843_);
v___x_1623_ = l_Lean_Syntax_isNone(v___x_1622_);
if (v___x_1623_ == 0)
{
uint8_t v___x_1624_; 
lean_inc(v___x_1622_);
v___x_1624_ = l_Lean_Syntax_matchesNull(v___x_1622_, v___x_1610_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1625_; 
lean_dec(v___x_1622_);
lean_dec(v___x_1619_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec(v_tk_867_);
v___x_1625_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1617_);
return v___x_1625_;
}
else
{
lean_object* v_h_x3f_1626_; lean_object* v___x_1627_; 
v_h_x3f_1626_ = l_Lean_Syntax_getArg(v___x_1622_, v___x_843_);
lean_dec(v___x_1622_);
v___x_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1627_, 0, v_h_x3f_1626_);
v___y_1542_ = v___y_1612_;
v___y_1543_ = v___x_1619_;
v___y_1544_ = v___y_1614_;
v___y_1545_ = v___y_1613_;
v___y_1546_ = v___y_1615_;
v_h_x3f_1547_ = v___x_1627_;
v___y_1548_ = v___y_1616_;
v___y_1549_ = v___y_1617_;
goto v___jp_1541_;
}
}
else
{
lean_object* v___x_1628_; 
lean_dec(v___x_1622_);
v___x_1628_ = lean_box(0);
v___y_1542_ = v___y_1612_;
v___y_1543_ = v___x_1619_;
v___y_1544_ = v___y_1614_;
v___y_1545_ = v___y_1613_;
v___y_1546_ = v___y_1615_;
v_h_x3f_1547_ = v___x_1628_;
v___y_1548_ = v___y_1616_;
v___y_1549_ = v___y_1617_;
goto v___jp_1541_;
}
}
}
v___jp_1629_:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v_body_1635_; lean_object* v_decls_1636_; lean_object* v_decls_1637_; 
v___x_1633_ = lean_unsigned_to_nat(3u);
v___x_1634_ = lean_unsigned_to_nat(4u);
v_body_1635_ = l_Lean_Syntax_getArg(v_stx_733_, v___x_1634_);
lean_dec(v_stx_733_);
v_decls_1636_ = l_Lean_Syntax_getArgs(v___x_869_);
lean_dec(v___x_869_);
v_decls_1637_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_1636_);
lean_dec_ref(v_decls_1636_);
if (lean_obj_tag(v_inv_1630_) == 1)
{
lean_object* v_val_1638_; lean_object* v___x_1639_; uint8_t v___x_1640_; 
v_val_1638_ = lean_ctor_get(v_inv_1630_, 0);
v___x_1639_ = lean_array_get_size(v_decls_1637_);
v___x_1640_ = lean_nat_dec_lt(v___x_868_, v___x_1639_);
if (v___x_1640_ == 0)
{
v___y_1612_ = v___x_1633_;
v___y_1613_ = v_inv_1630_;
v___y_1614_ = v_body_1635_;
v___y_1615_ = v_decls_1637_;
v___y_1616_ = v___y_1631_;
v___y_1617_ = v___y_1632_;
goto v___jp_1611_;
}
else
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1641_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__15));
v___x_1642_ = l_Lean_Macro_throwErrorAt___redArg(v_val_1638_, v___x_1641_, v___y_1631_, v___y_1632_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 1);
lean_inc(v_a_1643_);
lean_dec_ref_known(v___x_1642_, 2);
v___y_1612_ = v___x_1633_;
v___y_1613_ = v_inv_1630_;
v___y_1614_ = v_body_1635_;
v___y_1615_ = v_decls_1637_;
v___y_1616_ = v___y_1631_;
v___y_1617_ = v_a_1643_;
goto v___jp_1611_;
}
else
{
lean_object* v_a_1644_; lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
lean_dec_ref_known(v_inv_1630_, 1);
lean_dec_ref(v_decls_1637_);
lean_dec(v_body_1635_);
lean_dec(v_tk_867_);
v_a_1644_ = lean_ctor_get(v___x_1642_, 0);
v_a_1645_ = lean_ctor_get(v___x_1642_, 1);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1642_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_inc(v_a_1644_);
lean_dec(v___x_1642_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1644_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
}
else
{
v___y_1612_ = v___x_1633_;
v___y_1613_ = v_inv_1630_;
v___y_1614_ = v_body_1635_;
v___y_1615_ = v_decls_1637_;
v___y_1616_ = v___y_1631_;
v___y_1617_ = v___y_1632_;
goto v___jp_1611_;
}
}
}
else
{
lean_object* v___x_1663_; uint8_t v___x_1664_; 
v___x_1663_ = l_Lean_Syntax_getArg(v___x_1043_, v___x_843_);
v___x_1664_ = l_Lean_Syntax_isNone(v___x_1663_);
if (v___x_1664_ == 0)
{
lean_object* v___x_1665_; uint8_t v___x_1666_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v_x_1673_; lean_object* v_body_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; 
v___x_1665_ = lean_unsigned_to_nat(2u);
v___x_1666_ = l_Lean_Syntax_matchesNull(v___x_1663_, v___x_1665_);
if (v___x_1666_ == 0)
{
lean_object* v___x_1713_; lean_object* v___y_1715_; lean_object* v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v_h_x3f_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1786_; lean_object* v___y_1787_; lean_object* v_inv_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___x_1822_; uint8_t v___x_1823_; 
lean_dec(v___x_1043_);
v___x_1713_ = lean_unsigned_to_nat(3u);
v___x_1822_ = l_Lean_Syntax_getArg(v_stx_733_, v___x_1665_);
v___x_1823_ = l_Lean_Syntax_isNone(v___x_1822_);
if (v___x_1823_ == 0)
{
uint8_t v___x_1824_; 
lean_inc(v___x_1822_);
v___x_1824_ = l_Lean_Syntax_matchesNull(v___x_1822_, v___x_868_);
if (v___x_1824_ == 0)
{
lean_object* v___x_1825_; 
lean_dec(v___x_1822_);
lean_dec(v___x_869_);
lean_dec(v_tk_867_);
lean_dec(v_stx_733_);
v___x_1825_ = l_Lean_Macro_throwUnsupported___redArg(v_a_735_);
return v___x_1825_;
}
else
{
lean_object* v_inv_1826_; lean_object* v___x_1827_; uint8_t v___x_1828_; 
v_inv_1826_ = l_Lean_Syntax_getArg(v___x_1822_, v___x_843_);
lean_dec(v___x_1822_);
v___x_1827_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v_inv_1826_);
v___x_1828_ = l_Lean_Syntax_isOfKind(v_inv_1826_, v___x_1827_);
if (v___x_1828_ == 0)
{
lean_object* v___x_1829_; 
lean_dec(v_inv_1826_);
lean_dec(v___x_869_);
lean_dec(v_tk_867_);
lean_dec(v_stx_733_);
v___x_1829_ = l_Lean_Macro_throwUnsupported___redArg(v_a_735_);
return v___x_1829_;
}
else
{
lean_object* v___x_1830_; 
v___x_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1830_, 0, v_inv_1826_);
v_inv_1800_ = v___x_1830_;
v___y_1801_ = v_a_734_;
v___y_1802_ = v_a_735_;
goto v___jp_1799_;
}
}
}
else
{
lean_object* v___x_1831_; 
lean_dec(v___x_1822_);
v___x_1831_ = lean_box(0);
v_inv_1800_ = v___x_1831_;
v___y_1801_ = v_a_734_;
v___y_1802_ = v_a_735_;
goto v___jp_1799_;
}
v___jp_1714_:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v_doElems_1724_; uint8_t v___x_1725_; 
v___x_1722_ = l_Lean_Syntax_getArg(v___y_1715_, v___x_868_);
v___x_1723_ = l_Lean_Syntax_getArg(v___y_1715_, v___x_1713_);
lean_dec(v___y_1715_);
v_doElems_1724_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_1725_ = l_Lean_Syntax_isIdent(v___x_1722_);
if (v___x_1725_ == 0)
{
lean_object* v___x_1726_; uint8_t v___x_1727_; 
v___x_1726_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_1722_);
v___x_1727_ = l_Lean_Syntax_isOfKind(v___x_1722_, v___x_1726_);
if (v___x_1727_ == 0)
{
lean_object* v___x_1728_; 
v___x_1728_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1722_, v___x_1727_, v___y_1720_, v___y_1721_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v_a_1730_; lean_object* v_ref_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
lean_inc_n(v_a_1729_, 2);
v_a_1730_ = lean_ctor_get(v___x_1728_, 1);
lean_inc(v_a_1730_);
lean_dec_ref_known(v___x_1728_, 2);
v_ref_1731_ = lean_ctor_get(v___y_1720_, 5);
v___x_1732_ = l_Lean_SourceInfo_fromRef(v_ref_1731_, v___x_1727_);
v___x_1733_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_1734_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1735_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
v___x_1736_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_1737_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_n(v___x_1732_, 15);
v___x_1738_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1732_);
lean_ctor_set(v___x_1738_, 1, v___x_1737_);
v___x_1739_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_1740_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1732_);
lean_ctor_set(v___x_1740_, 1, v___x_1734_);
lean_ctor_set(v___x_1740_, 2, v___x_1739_);
v___x_1741_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_1740_, 4);
v___x_1742_ = l_Lean_Syntax_node2(v___x_1732_, v___x_1741_, v___x_1740_, v_a_1729_);
v___x_1743_ = l_Lean_Syntax_node1(v___x_1732_, v___x_1734_, v___x_1742_);
v___x_1744_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_1745_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1732_);
lean_ctor_set(v___x_1745_, 1, v___x_1744_);
v___x_1746_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_1747_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_1748_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_1749_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1732_);
lean_ctor_set(v___x_1749_, 1, v___x_1748_);
v___x_1750_ = l_Lean_Syntax_node1(v___x_1732_, v___x_1734_, v___x_1722_);
v___x_1751_ = l_Lean_Syntax_node1(v___x_1732_, v___x_1734_, v___x_1750_);
v___x_1752_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_1753_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1732_);
lean_ctor_set(v___x_1753_, 1, v___x_1752_);
v___x_1754_ = l_Lean_Syntax_node4(v___x_1732_, v___x_1747_, v___x_1749_, v___x_1751_, v___x_1753_, v___y_1716_);
v___x_1755_ = l_Lean_Syntax_node1(v___x_1732_, v___x_1734_, v___x_1754_);
v___x_1756_ = l_Lean_Syntax_node1(v___x_1732_, v___x_1746_, v___x_1755_);
v___x_1757_ = l_Lean_Syntax_node7(v___x_1732_, v___x_1736_, v___x_1738_, v___x_1740_, v___x_1740_, v___x_1740_, v___x_1743_, v___x_1745_, v___x_1756_);
v___x_1758_ = l_Lean_Syntax_node2(v___x_1732_, v___x_1735_, v___x_1757_, v___x_1740_);
v___x_1759_ = l_Lean_Syntax_node1(v___x_1732_, v___x_1734_, v___x_1758_);
v___x_1760_ = l_Lean_Syntax_node1(v___x_1732_, v___x_1733_, v___x_1759_);
v___y_1668_ = v___x_1723_;
v___y_1669_ = v_doElems_1724_;
v___y_1670_ = v___y_1717_;
v___y_1671_ = v_h_x3f_1719_;
v___y_1672_ = v___y_1718_;
v_x_1673_ = v_a_1729_;
v_body_1674_ = v___x_1760_;
v___y_1675_ = v___y_1720_;
v___y_1676_ = v_a_1730_;
goto v___jp_1667_;
}
else
{
lean_object* v_a_1761_; lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_dec(v___x_1723_);
lean_dec(v___x_1722_);
lean_dec(v_h_x3f_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec(v_tk_867_);
v_a_1761_ = lean_ctor_get(v___x_1728_, 0);
v_a_1762_ = lean_ctor_get(v___x_1728_, 1);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1728_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_inc(v_a_1761_);
lean_dec(v___x_1728_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1761_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
else
{
lean_object* v___x_1770_; 
v___x_1770_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1722_, v___x_1725_, v___y_1720_, v___y_1721_);
lean_dec(v___x_1722_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v_a_1772_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
v_a_1772_ = lean_ctor_get(v___x_1770_, 1);
lean_inc(v_a_1772_);
lean_dec_ref_known(v___x_1770_, 2);
v___y_1668_ = v___x_1723_;
v___y_1669_ = v_doElems_1724_;
v___y_1670_ = v___y_1717_;
v___y_1671_ = v_h_x3f_1719_;
v___y_1672_ = v___y_1718_;
v_x_1673_ = v_a_1771_;
v_body_1674_ = v___y_1716_;
v___y_1675_ = v___y_1720_;
v___y_1676_ = v_a_1772_;
goto v___jp_1667_;
}
else
{
lean_object* v_a_1773_; lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1781_; 
lean_dec(v___x_1723_);
lean_dec(v_h_x3f_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec(v_tk_867_);
v_a_1773_ = lean_ctor_get(v___x_1770_, 0);
v_a_1774_ = lean_ctor_get(v___x_1770_, 1);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1776_ = v___x_1770_;
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_inc(v_a_1773_);
lean_dec(v___x_1770_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1779_; 
if (v_isShared_1777_ == 0)
{
v___x_1779_ = v___x_1776_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_a_1773_);
lean_ctor_set(v_reuseFailAlloc_1780_, 1, v_a_1774_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
}
}
else
{
v___y_1668_ = v___x_1723_;
v___y_1669_ = v_doElems_1724_;
v___y_1670_ = v___y_1717_;
v___y_1671_ = v_h_x3f_1719_;
v___y_1672_ = v___y_1718_;
v_x_1673_ = v___x_1722_;
v_body_1674_ = v___y_1716_;
v___y_1675_ = v___y_1720_;
v___y_1676_ = v___y_1721_;
goto v___jp_1667_;
}
}
v___jp_1782_:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; uint8_t v___x_1790_; 
v___x_1788_ = lean_box(0);
v___x_1789_ = lean_array_get(v___x_1788_, v___y_1785_, v___x_843_);
lean_inc(v___x_1789_);
v___x_1790_ = l_Lean_Syntax_isOfKind(v___x_1789_, v___x_1044_);
if (v___x_1790_ == 0)
{
lean_object* v___x_1791_; 
lean_dec(v___x_1789_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec(v_tk_867_);
v___x_1791_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1787_);
return v___x_1791_;
}
else
{
lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1792_ = l_Lean_Syntax_getArg(v___x_1789_, v___x_843_);
v___x_1793_ = l_Lean_Syntax_isNone(v___x_1792_);
if (v___x_1793_ == 0)
{
uint8_t v___x_1794_; 
lean_inc(v___x_1792_);
v___x_1794_ = l_Lean_Syntax_matchesNull(v___x_1792_, v___x_1665_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; 
lean_dec(v___x_1792_);
lean_dec(v___x_1789_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec(v_tk_867_);
v___x_1795_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1787_);
return v___x_1795_;
}
else
{
lean_object* v_h_x3f_1796_; lean_object* v___x_1797_; 
v_h_x3f_1796_ = l_Lean_Syntax_getArg(v___x_1792_, v___x_843_);
lean_dec(v___x_1792_);
v___x_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1797_, 0, v_h_x3f_1796_);
v___y_1715_ = v___x_1789_;
v___y_1716_ = v___y_1783_;
v___y_1717_ = v___y_1784_;
v___y_1718_ = v___y_1785_;
v_h_x3f_1719_ = v___x_1797_;
v___y_1720_ = v___y_1786_;
v___y_1721_ = v___y_1787_;
goto v___jp_1714_;
}
}
else
{
lean_object* v___x_1798_; 
lean_dec(v___x_1792_);
v___x_1798_ = lean_box(0);
v___y_1715_ = v___x_1789_;
v___y_1716_ = v___y_1783_;
v___y_1717_ = v___y_1784_;
v___y_1718_ = v___y_1785_;
v_h_x3f_1719_ = v___x_1798_;
v___y_1720_ = v___y_1786_;
v___y_1721_ = v___y_1787_;
goto v___jp_1714_;
}
}
}
v___jp_1799_:
{
lean_object* v___x_1803_; lean_object* v_body_1804_; lean_object* v_decls_1805_; lean_object* v_decls_1806_; 
v___x_1803_ = lean_unsigned_to_nat(4u);
v_body_1804_ = l_Lean_Syntax_getArg(v_stx_733_, v___x_1803_);
lean_dec(v_stx_733_);
v_decls_1805_ = l_Lean_Syntax_getArgs(v___x_869_);
lean_dec(v___x_869_);
v_decls_1806_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_1805_);
lean_dec_ref(v_decls_1805_);
if (lean_obj_tag(v_inv_1800_) == 1)
{
lean_object* v_val_1807_; lean_object* v___x_1808_; uint8_t v___x_1809_; 
v_val_1807_ = lean_ctor_get(v_inv_1800_, 0);
v___x_1808_ = lean_array_get_size(v_decls_1806_);
v___x_1809_ = lean_nat_dec_lt(v___x_868_, v___x_1808_);
if (v___x_1809_ == 0)
{
v___y_1783_ = v_body_1804_;
v___y_1784_ = v_inv_1800_;
v___y_1785_ = v_decls_1806_;
v___y_1786_ = v___y_1801_;
v___y_1787_ = v___y_1802_;
goto v___jp_1782_;
}
else
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__15));
v___x_1811_ = l_Lean_Macro_throwErrorAt___redArg(v_val_1807_, v___x_1810_, v___y_1801_, v___y_1802_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 1);
lean_inc(v_a_1812_);
lean_dec_ref_known(v___x_1811_, 2);
v___y_1783_ = v_body_1804_;
v___y_1784_ = v_inv_1800_;
v___y_1785_ = v_decls_1806_;
v___y_1786_ = v___y_1801_;
v___y_1787_ = v_a_1812_;
goto v___jp_1782_;
}
else
{
lean_object* v_a_1813_; lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1821_; 
lean_dec_ref_known(v_inv_1800_, 1);
lean_dec_ref(v_decls_1806_);
lean_dec(v_body_1804_);
lean_dec(v_tk_867_);
v_a_1813_ = lean_ctor_get(v___x_1811_, 0);
v_a_1814_ = lean_ctor_get(v___x_1811_, 1);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1816_ = v___x_1811_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_inc(v_a_1813_);
lean_dec(v___x_1811_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1813_);
lean_ctor_set(v_reuseFailAlloc_1820_, 1, v_a_1814_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
}
else
{
v___y_1783_ = v_body_1804_;
v___y_1784_ = v_inv_1800_;
v___y_1785_ = v_decls_1806_;
v___y_1786_ = v___y_1801_;
v___y_1787_ = v___y_1802_;
goto v___jp_1782_;
}
}
}
else
{
v___y_1425_ = v_a_734_;
v___y_1426_ = v_a_735_;
goto v___jp_1424_;
}
v___jp_1667_:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1677_ = lean_array_get_size(v___y_1672_);
v___x_1678_ = l_Array_toSubarray___redArg(v___y_1672_, v___x_868_, v___x_1677_);
lean_inc_ref(v___y_1669_);
v___x_1679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___y_1669_);
lean_ctor_set(v___x_1679_, 1, v_body_1674_);
v___x_1680_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_1666_, v___x_1678_, v___x_1679_, v___y_1675_, v___y_1676_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_a_1681_; lean_object* v_a_1682_; lean_object* v_fst_1683_; lean_object* v_snd_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1703_; 
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_a_1681_);
v_a_1682_ = lean_ctor_get(v___x_1680_, 1);
lean_inc(v_a_1682_);
lean_dec_ref_known(v___x_1680_, 2);
v_fst_1683_ = lean_ctor_get(v_a_1681_, 0);
v_snd_1684_ = lean_ctor_get(v_a_1681_, 1);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_a_1681_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1686_ = v_a_1681_;
v_isShared_1687_ = v_isSharedCheck_1703_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_snd_1684_);
lean_inc(v_fst_1683_);
lean_dec(v_a_1681_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1703_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v_ref_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1694_; 
v_ref_1688_ = lean_ctor_get(v___y_1675_, 5);
v___x_1689_ = l_Lean_SourceInfo_fromRef(v_ref_1688_, v___x_1666_);
v___x_1690_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
v___x_1691_ = l_Lean_SourceInfo_fromRef(v_tk_867_, v___x_841_);
lean_dec(v_tk_867_);
v___x_1692_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
if (v_isShared_1687_ == 0)
{
lean_ctor_set_tag(v___x_1686_, 2);
lean_ctor_set(v___x_1686_, 1, v___x_1692_);
lean_ctor_set(v___x_1686_, 0, v___x_1691_);
v___x_1694_ = v___x_1686_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1691_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v___x_1692_);
v___x_1694_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1695_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1696_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
if (lean_obj_tag(v___y_1671_) == 1)
{
lean_object* v_val_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v_val_1697_ = lean_ctor_get(v___y_1671_, 0);
lean_inc(v_val_1697_);
lean_dec_ref_known(v___y_1671_, 1);
v___x_1698_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
lean_inc(v___x_1689_);
v___x_1699_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1689_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
v___x_1700_ = l_Array_mkArray2___redArg(v_val_1697_, v___x_1699_);
v___y_1046_ = v___y_1668_;
v___y_1047_ = v_fst_1683_;
v___y_1048_ = v___x_1690_;
v___y_1049_ = v___x_1689_;
v___y_1050_ = v_a_1682_;
v___y_1051_ = v_x_1673_;
v___y_1052_ = v___x_1694_;
v___y_1053_ = v___x_1695_;
v___y_1054_ = v___y_1670_;
v___y_1055_ = v___x_1696_;
v___y_1056_ = v_snd_1684_;
v___y_1057_ = v___x_1700_;
goto v___jp_1045_;
}
else
{
lean_object* v___x_1701_; 
lean_dec(v___y_1671_);
v___x_1701_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___y_1046_ = v___y_1668_;
v___y_1047_ = v_fst_1683_;
v___y_1048_ = v___x_1690_;
v___y_1049_ = v___x_1689_;
v___y_1050_ = v_a_1682_;
v___y_1051_ = v_x_1673_;
v___y_1052_ = v___x_1694_;
v___y_1053_ = v___x_1695_;
v___y_1054_ = v___y_1670_;
v___y_1055_ = v___x_1696_;
v___y_1056_ = v_snd_1684_;
v___y_1057_ = v___x_1701_;
goto v___jp_1045_;
}
}
}
}
else
{
lean_object* v_a_1704_; lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
lean_dec(v_x_1673_);
lean_dec(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec(v___y_1668_);
lean_dec(v_tk_867_);
v_a_1704_ = lean_ctor_get(v___x_1680_, 0);
v_a_1705_ = lean_ctor_get(v___x_1680_, 1);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v___x_1680_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_inc(v_a_1704_);
lean_dec(v___x_1680_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1704_);
lean_ctor_set(v_reuseFailAlloc_1711_, 1, v_a_1705_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
}
else
{
lean_dec(v___x_1663_);
v___y_1425_ = v_a_734_;
v___y_1426_ = v_a_735_;
goto v___jp_1424_;
}
}
v___jp_1045_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
lean_inc_ref(v___y_1055_);
v___x_1058_ = l_Array_append___redArg(v___y_1055_, v___y_1057_);
lean_dec_ref(v___y_1057_);
lean_inc_n(v___y_1053_, 2);
lean_inc_n(v___y_1049_, 4);
v___x_1059_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1059_, 0, v___y_1049_);
lean_ctor_set(v___x_1059_, 1, v___y_1053_);
lean_ctor_set(v___x_1059_, 2, v___x_1058_);
v___x_1060_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_1061_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___y_1049_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = l_Lean_Syntax_node4(v___y_1049_, v___x_1044_, v___x_1059_, v___y_1051_, v___x_1061_, v___y_1046_);
v___x_1063_ = l_Lean_Syntax_node1(v___y_1049_, v___y_1053_, v___x_1062_);
if (lean_obj_tag(v___y_1054_) == 1)
{
lean_object* v_val_1064_; lean_object* v___x_1065_; 
v_val_1064_ = lean_ctor_get(v___y_1054_, 0);
lean_inc(v_val_1064_);
lean_dec_ref_known(v___y_1054_, 1);
v___x_1065_ = l_Array_mkArray1___redArg(v_val_1064_);
v___y_738_ = v___y_1047_;
v___y_739_ = v___y_1048_;
v___y_740_ = v___y_1049_;
v___y_741_ = v___y_1050_;
v___y_742_ = v___y_1052_;
v___y_743_ = v___y_1053_;
v___y_744_ = v___x_1063_;
v___y_745_ = v___y_1055_;
v___y_746_ = v___y_1056_;
v___y_747_ = v___x_1065_;
goto v___jp_737_;
}
else
{
lean_object* v___x_1066_; 
lean_dec(v___y_1054_);
v___x_1066_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___y_738_ = v___y_1047_;
v___y_739_ = v___y_1048_;
v___y_740_ = v___y_1049_;
v___y_741_ = v___y_1050_;
v___y_742_ = v___y_1052_;
v___y_743_ = v___y_1053_;
v___y_744_ = v___x_1063_;
v___y_745_ = v___y_1055_;
v___y_746_ = v___y_1056_;
v___y_747_ = v___x_1066_;
goto v___jp_737_;
}
}
v___jp_1067_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
lean_inc_ref(v___y_1074_);
v___x_1080_ = l_Array_append___redArg(v___y_1074_, v___y_1079_);
lean_dec_ref(v___y_1079_);
lean_inc_n(v___y_1077_, 2);
lean_inc_n(v___y_1073_, 4);
v___x_1081_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1081_, 0, v___y_1073_);
lean_ctor_set(v___x_1081_, 1, v___y_1077_);
lean_ctor_set(v___x_1081_, 2, v___x_1080_);
v___x_1082_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_1083_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___y_1073_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = l_Lean_Syntax_node4(v___y_1073_, v___x_1044_, v___x_1081_, v___y_1069_, v___x_1083_, v___y_1076_);
v___x_1085_ = l_Lean_Syntax_node1(v___y_1073_, v___y_1077_, v___x_1084_);
if (lean_obj_tag(v___y_1070_) == 1)
{
lean_object* v_val_1086_; lean_object* v___x_1087_; 
v_val_1086_ = lean_ctor_get(v___y_1070_, 0);
lean_inc(v_val_1086_);
lean_dec_ref_known(v___y_1070_, 1);
v___x_1087_ = l_Array_mkArray1___redArg(v_val_1086_);
v___y_764_ = v___x_1085_;
v___y_765_ = v___y_1068_;
v___y_766_ = v___y_1072_;
v___y_767_ = v___y_1071_;
v___y_768_ = v___y_1073_;
v___y_769_ = v___y_1074_;
v___y_770_ = v___y_1075_;
v___y_771_ = v___y_1077_;
v___y_772_ = v___y_1078_;
v___y_773_ = v___x_1087_;
goto v___jp_763_;
}
else
{
lean_object* v___x_1088_; 
lean_dec(v___y_1070_);
v___x_1088_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___y_764_ = v___x_1085_;
v___y_765_ = v___y_1068_;
v___y_766_ = v___y_1072_;
v___y_767_ = v___y_1071_;
v___y_768_ = v___y_1073_;
v___y_769_ = v___y_1074_;
v___y_770_ = v___y_1075_;
v___y_771_ = v___y_1077_;
v___y_772_ = v___y_1078_;
v___y_773_ = v___x_1088_;
goto v___jp_763_;
}
}
v___jp_1089_:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1100_ = lean_array_get_size(v___y_1092_);
v___x_1101_ = l_Array_toSubarray___redArg(v___y_1092_, v___x_868_, v___x_1100_);
lean_inc_ref(v___y_1090_);
v___x_1102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___y_1090_);
lean_ctor_set(v___x_1102_, 1, v_body_1097_);
v___x_1103_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___y_1095_, v___x_1101_, v___x_1102_, v___y_1098_, v___y_1099_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; lean_object* v_a_1105_; lean_object* v_fst_1106_; lean_object* v_snd_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1126_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_a_1104_);
v_a_1105_ = lean_ctor_get(v___x_1103_, 1);
lean_inc(v_a_1105_);
lean_dec_ref_known(v___x_1103_, 2);
v_fst_1106_ = lean_ctor_get(v_a_1104_, 0);
v_snd_1107_ = lean_ctor_get(v_a_1104_, 1);
v_isSharedCheck_1126_ = !lean_is_exclusive(v_a_1104_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1109_ = v_a_1104_;
v_isShared_1110_ = v_isSharedCheck_1126_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_snd_1107_);
lean_inc(v_fst_1106_);
lean_dec(v_a_1104_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1126_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v_ref_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1117_; 
v_ref_1111_ = lean_ctor_get(v___y_1098_, 5);
v___x_1112_ = l_Lean_SourceInfo_fromRef(v_ref_1111_, v___y_1095_);
v___x_1113_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
v___x_1114_ = l_Lean_SourceInfo_fromRef(v_tk_867_, v___x_841_);
lean_dec(v_tk_867_);
v___x_1115_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
if (v_isShared_1110_ == 0)
{
lean_ctor_set_tag(v___x_1109_, 2);
lean_ctor_set(v___x_1109_, 1, v___x_1115_);
lean_ctor_set(v___x_1109_, 0, v___x_1114_);
v___x_1117_ = v___x_1109_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1114_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v___x_1115_);
v___x_1117_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1119_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
if (lean_obj_tag(v___y_1093_) == 1)
{
lean_object* v_val_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v_val_1120_ = lean_ctor_get(v___y_1093_, 0);
lean_inc(v_val_1120_);
lean_dec_ref_known(v___y_1093_, 1);
v___x_1121_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
lean_inc(v___x_1112_);
v___x_1122_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1112_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
v___x_1123_ = l_Array_mkArray2___redArg(v_val_1120_, v___x_1122_);
v___y_1068_ = v_snd_1107_;
v___y_1069_ = v_x_1096_;
v___y_1070_ = v___y_1091_;
v___y_1071_ = v___x_1117_;
v___y_1072_ = v___x_1113_;
v___y_1073_ = v___x_1112_;
v___y_1074_ = v___x_1119_;
v___y_1075_ = v_fst_1106_;
v___y_1076_ = v___y_1094_;
v___y_1077_ = v___x_1118_;
v___y_1078_ = v_a_1105_;
v___y_1079_ = v___x_1123_;
goto v___jp_1067_;
}
else
{
lean_object* v___x_1124_; 
lean_dec(v___y_1093_);
v___x_1124_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___y_1068_ = v_snd_1107_;
v___y_1069_ = v_x_1096_;
v___y_1070_ = v___y_1091_;
v___y_1071_ = v___x_1117_;
v___y_1072_ = v___x_1113_;
v___y_1073_ = v___x_1112_;
v___y_1074_ = v___x_1119_;
v___y_1075_ = v_fst_1106_;
v___y_1076_ = v___y_1094_;
v___y_1077_ = v___x_1118_;
v___y_1078_ = v_a_1105_;
v___y_1079_ = v___x_1124_;
goto v___jp_1067_;
}
}
}
}
else
{
lean_object* v_a_1127_; lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_dec(v_x_1096_);
lean_dec(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec(v___y_1091_);
lean_dec(v_tk_867_);
v_a_1127_ = lean_ctor_get(v___x_1103_, 0);
v_a_1128_ = lean_ctor_get(v___x_1103_, 1);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1103_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_inc(v_a_1127_);
lean_dec(v___x_1103_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1127_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
v___jp_1136_:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v_doElems_1148_; uint8_t v___x_1149_; 
v___x_1146_ = l_Lean_Syntax_getArg(v___y_1141_, v___x_868_);
v___x_1147_ = l_Lean_Syntax_getArg(v___y_1141_, v___y_1137_);
lean_dec(v___y_1141_);
v_doElems_1148_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_1149_ = l_Lean_Syntax_isIdent(v___x_1146_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; uint8_t v___x_1151_; 
v___x_1150_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_1146_);
v___x_1151_ = l_Lean_Syntax_isOfKind(v___x_1146_, v___x_1150_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; 
v___x_1152_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1146_, v___y_1142_, v___y_1144_, v___y_1145_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v_a_1153_; lean_object* v_a_1154_; lean_object* v_ref_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
lean_inc_n(v_a_1153_, 2);
v_a_1154_ = lean_ctor_get(v___x_1152_, 1);
lean_inc(v_a_1154_);
lean_dec_ref_known(v___x_1152_, 2);
v_ref_1155_ = lean_ctor_get(v___y_1144_, 5);
v___x_1156_ = l_Lean_SourceInfo_fromRef(v_ref_1155_, v___y_1142_);
v___x_1157_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_1158_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1159_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
v___x_1160_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_1161_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_n(v___x_1156_, 15);
v___x_1162_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1156_);
lean_ctor_set(v___x_1162_, 1, v___x_1161_);
v___x_1163_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_1164_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1156_);
lean_ctor_set(v___x_1164_, 1, v___x_1158_);
lean_ctor_set(v___x_1164_, 2, v___x_1163_);
v___x_1165_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_1164_, 4);
v___x_1166_ = l_Lean_Syntax_node2(v___x_1156_, v___x_1165_, v___x_1164_, v_a_1153_);
v___x_1167_ = l_Lean_Syntax_node1(v___x_1156_, v___x_1158_, v___x_1166_);
v___x_1168_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_1169_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1156_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
v___x_1170_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_1171_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_1172_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_1173_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1156_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
v___x_1174_ = l_Lean_Syntax_node1(v___x_1156_, v___x_1158_, v___x_1146_);
v___x_1175_ = l_Lean_Syntax_node1(v___x_1156_, v___x_1158_, v___x_1174_);
v___x_1176_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_1177_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1156_);
lean_ctor_set(v___x_1177_, 1, v___x_1176_);
v___x_1178_ = l_Lean_Syntax_node4(v___x_1156_, v___x_1171_, v___x_1173_, v___x_1175_, v___x_1177_, v___y_1138_);
v___x_1179_ = l_Lean_Syntax_node1(v___x_1156_, v___x_1158_, v___x_1178_);
v___x_1180_ = l_Lean_Syntax_node1(v___x_1156_, v___x_1170_, v___x_1179_);
v___x_1181_ = l_Lean_Syntax_node7(v___x_1156_, v___x_1160_, v___x_1162_, v___x_1164_, v___x_1164_, v___x_1164_, v___x_1167_, v___x_1169_, v___x_1180_);
v___x_1182_ = l_Lean_Syntax_node2(v___x_1156_, v___x_1159_, v___x_1181_, v___x_1164_);
v___x_1183_ = l_Lean_Syntax_node1(v___x_1156_, v___x_1158_, v___x_1182_);
v___x_1184_ = l_Lean_Syntax_node1(v___x_1156_, v___x_1157_, v___x_1183_);
v___y_1090_ = v_doElems_1148_;
v___y_1091_ = v___y_1139_;
v___y_1092_ = v___y_1140_;
v___y_1093_ = v_h_x3f_1143_;
v___y_1094_ = v___x_1147_;
v___y_1095_ = v___y_1142_;
v_x_1096_ = v_a_1153_;
v_body_1097_ = v___x_1184_;
v___y_1098_ = v___y_1144_;
v___y_1099_ = v_a_1154_;
goto v___jp_1089_;
}
else
{
lean_object* v_a_1185_; lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
lean_dec(v___x_1147_);
lean_dec(v___x_1146_);
lean_dec(v_h_x3f_1143_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec(v___y_1138_);
lean_dec(v_tk_867_);
v_a_1185_ = lean_ctor_get(v___x_1152_, 0);
v_a_1186_ = lean_ctor_get(v___x_1152_, 1);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1152_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_inc(v_a_1185_);
lean_dec(v___x_1152_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1185_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
else
{
lean_object* v___x_1194_; 
v___x_1194_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1146_, v___y_1142_, v___y_1144_, v___y_1145_);
lean_dec(v___x_1146_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v_a_1196_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1195_);
v_a_1196_ = lean_ctor_get(v___x_1194_, 1);
lean_inc(v_a_1196_);
lean_dec_ref_known(v___x_1194_, 2);
v___y_1090_ = v_doElems_1148_;
v___y_1091_ = v___y_1139_;
v___y_1092_ = v___y_1140_;
v___y_1093_ = v_h_x3f_1143_;
v___y_1094_ = v___x_1147_;
v___y_1095_ = v___y_1142_;
v_x_1096_ = v_a_1195_;
v_body_1097_ = v___y_1138_;
v___y_1098_ = v___y_1144_;
v___y_1099_ = v_a_1196_;
goto v___jp_1089_;
}
else
{
lean_object* v_a_1197_; lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
lean_dec(v___x_1147_);
lean_dec(v_h_x3f_1143_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec(v___y_1138_);
lean_dec(v_tk_867_);
v_a_1197_ = lean_ctor_get(v___x_1194_, 0);
v_a_1198_ = lean_ctor_get(v___x_1194_, 1);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1194_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_inc(v_a_1197_);
lean_dec(v___x_1194_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1197_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_a_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
}
else
{
v___y_1090_ = v_doElems_1148_;
v___y_1091_ = v___y_1139_;
v___y_1092_ = v___y_1140_;
v___y_1093_ = v_h_x3f_1143_;
v___y_1094_ = v___x_1147_;
v___y_1095_ = v___y_1142_;
v_x_1096_ = v___x_1146_;
v_body_1097_ = v___y_1138_;
v___y_1098_ = v___y_1144_;
v___y_1099_ = v___y_1145_;
goto v___jp_1089_;
}
}
v___jp_1206_:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; 
v___x_1215_ = lean_box(0);
v___x_1216_ = lean_array_get(v___x_1215_, v___y_1211_, v___x_843_);
lean_inc(v___x_1216_);
v___x_1217_ = l_Lean_Syntax_isOfKind(v___x_1216_, v___x_1044_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; 
lean_dec(v___x_1216_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec(v_tk_867_);
v___x_1218_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1214_);
return v___x_1218_;
}
else
{
lean_object* v___x_1219_; uint8_t v___x_1220_; 
v___x_1219_ = l_Lean_Syntax_getArg(v___x_1216_, v___x_843_);
v___x_1220_ = l_Lean_Syntax_isNone(v___x_1219_);
if (v___x_1220_ == 0)
{
uint8_t v___x_1221_; 
lean_inc(v___x_1219_);
v___x_1221_ = l_Lean_Syntax_matchesNull(v___x_1219_, v___y_1207_);
if (v___x_1221_ == 0)
{
lean_object* v___x_1222_; 
lean_dec(v___x_1219_);
lean_dec(v___x_1216_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec(v_tk_867_);
v___x_1222_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1214_);
return v___x_1222_;
}
else
{
lean_object* v_h_x3f_1223_; lean_object* v___x_1224_; 
v_h_x3f_1223_ = l_Lean_Syntax_getArg(v___x_1219_, v___x_843_);
lean_dec(v___x_1219_);
v___x_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1224_, 0, v_h_x3f_1223_);
v___y_1137_ = v___y_1208_;
v___y_1138_ = v___y_1209_;
v___y_1139_ = v___y_1210_;
v___y_1140_ = v___y_1211_;
v___y_1141_ = v___x_1216_;
v___y_1142_ = v___y_1212_;
v_h_x3f_1143_ = v___x_1224_;
v___y_1144_ = v___y_1213_;
v___y_1145_ = v___y_1214_;
goto v___jp_1136_;
}
}
else
{
lean_object* v___x_1225_; 
lean_dec(v___x_1219_);
v___x_1225_ = lean_box(0);
v___y_1137_ = v___y_1208_;
v___y_1138_ = v___y_1209_;
v___y_1139_ = v___y_1210_;
v___y_1140_ = v___y_1211_;
v___y_1141_ = v___x_1216_;
v___y_1142_ = v___y_1212_;
v_h_x3f_1143_ = v___x_1225_;
v___y_1144_ = v___y_1213_;
v___y_1145_ = v___y_1214_;
goto v___jp_1136_;
}
}
}
v___jp_1226_:
{
lean_object* v___x_1233_; lean_object* v_body_1234_; lean_object* v_decls_1235_; lean_object* v_decls_1236_; 
v___x_1233_ = lean_unsigned_to_nat(4u);
v_body_1234_ = l_Lean_Syntax_getArg(v_stx_733_, v___x_1233_);
lean_dec(v_stx_733_);
v_decls_1235_ = l_Lean_Syntax_getArgs(v___x_869_);
lean_dec(v___x_869_);
v_decls_1236_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_1235_);
lean_dec_ref(v_decls_1235_);
if (lean_obj_tag(v_inv_1230_) == 1)
{
lean_object* v_val_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; 
v_val_1237_ = lean_ctor_get(v_inv_1230_, 0);
v___x_1238_ = lean_array_get_size(v_decls_1236_);
v___x_1239_ = lean_nat_dec_lt(v___x_868_, v___x_1238_);
if (v___x_1239_ == 0)
{
v___y_1207_ = v___y_1227_;
v___y_1208_ = v___y_1228_;
v___y_1209_ = v_body_1234_;
v___y_1210_ = v_inv_1230_;
v___y_1211_ = v_decls_1236_;
v___y_1212_ = v___y_1229_;
v___y_1213_ = v___y_1231_;
v___y_1214_ = v___y_1232_;
goto v___jp_1206_;
}
else
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__15));
v___x_1241_ = l_Lean_Macro_throwErrorAt___redArg(v_val_1237_, v___x_1240_, v___y_1231_, v___y_1232_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 1);
lean_inc(v_a_1242_);
lean_dec_ref_known(v___x_1241_, 2);
v___y_1207_ = v___y_1227_;
v___y_1208_ = v___y_1228_;
v___y_1209_ = v_body_1234_;
v___y_1210_ = v_inv_1230_;
v___y_1211_ = v_decls_1236_;
v___y_1212_ = v___y_1229_;
v___y_1213_ = v___y_1231_;
v___y_1214_ = v_a_1242_;
goto v___jp_1206_;
}
else
{
lean_object* v_a_1243_; lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
lean_dec_ref_known(v_inv_1230_, 1);
lean_dec_ref(v_decls_1236_);
lean_dec(v_body_1234_);
lean_dec(v_tk_867_);
v_a_1243_ = lean_ctor_get(v___x_1241_, 0);
v_a_1244_ = lean_ctor_get(v___x_1241_, 1);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1246_ = v___x_1241_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_inc(v_a_1243_);
lean_dec(v___x_1241_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1243_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_a_1244_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
}
else
{
v___y_1207_ = v___y_1227_;
v___y_1208_ = v___y_1228_;
v___y_1209_ = v_body_1234_;
v___y_1210_ = v_inv_1230_;
v___y_1211_ = v_decls_1236_;
v___y_1212_ = v___y_1229_;
v___y_1213_ = v___y_1231_;
v___y_1214_ = v___y_1232_;
goto v___jp_1206_;
}
}
v___jp_1252_:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
lean_inc_ref_n(v___y_1254_, 4);
v___x_1265_ = l_Array_append___redArg(v___y_1254_, v___y_1264_);
lean_dec_ref(v___y_1264_);
lean_inc_n(v___y_1255_, 5);
lean_inc_n(v___y_1257_, 11);
v___x_1266_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1266_, 0, v___y_1257_);
lean_ctor_set(v___x_1266_, 1, v___y_1255_);
lean_ctor_set(v___x_1266_, 2, v___x_1265_);
v___x_1267_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_1268_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___y_1257_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
v___x_1269_ = l_Lean_Syntax_node4(v___y_1257_, v___x_1044_, v___x_1266_, v___y_1256_, v___x_1268_, v___y_1263_);
v___x_1270_ = l_Lean_Syntax_node1(v___y_1257_, v___y_1255_, v___x_1269_);
v___x_1271_ = l_Array_mkArray1___redArg(v___y_1259_);
v___x_1272_ = l_Array_append___redArg(v___y_1254_, v___x_1271_);
lean_dec_ref(v___x_1271_);
v___x_1273_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1273_, 0, v___y_1257_);
lean_ctor_set(v___x_1273_, 1, v___y_1255_);
lean_ctor_set(v___x_1273_, 2, v___x_1272_);
v___x_1274_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_1275_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___y_1257_);
lean_ctor_set(v___x_1275_, 1, v___x_1274_);
lean_inc_ref(v___x_1275_);
v___x_1276_ = l_Lean_Syntax_node5(v___y_1257_, v___x_736_, v___y_1258_, v___x_1270_, v___x_1273_, v___x_1275_, v___y_1261_);
v___x_1277_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1277_, 0, v___y_1257_);
lean_ctor_set(v___x_1277_, 1, v___y_1255_);
lean_ctor_set(v___x_1277_, 2, v___y_1254_);
lean_inc(v___y_1262_);
v___x_1278_ = l_Lean_Syntax_node2(v___y_1257_, v___y_1262_, v___x_1276_, v___x_1277_);
v___x_1279_ = lean_array_push(v___y_1260_, v___x_1278_);
v___x_1280_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_1281_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_1282_ = l_Array_append___redArg(v___y_1254_, v___x_1279_);
lean_dec_ref(v___x_1279_);
v___x_1283_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1283_, 0, v___y_1257_);
lean_ctor_set(v___x_1283_, 1, v___y_1255_);
lean_ctor_set(v___x_1283_, 2, v___x_1282_);
v___x_1284_ = l_Lean_Syntax_node1(v___y_1257_, v___x_1281_, v___x_1283_);
v___x_1285_ = l_Lean_Syntax_node2(v___y_1257_, v___x_1280_, v___x_1275_, v___x_1284_);
v___x_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
lean_ctor_set(v___x_1286_, 1, v___y_1253_);
return v___x_1286_;
}
v___jp_1287_:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1298_ = lean_array_get_size(v___y_1288_);
v___x_1299_ = l_Array_toSubarray___redArg(v___y_1288_, v___x_868_, v___x_1298_);
lean_inc_ref(v___y_1292_);
v___x_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___y_1292_);
lean_ctor_set(v___x_1300_, 1, v_body_1295_);
v___x_1301_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg(v___y_1290_, v___x_1299_, v___x_1300_, v___y_1296_, v___y_1297_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v_a_1303_; lean_object* v_fst_1304_; lean_object* v_snd_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1324_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_a_1302_);
v_a_1303_ = lean_ctor_get(v___x_1301_, 1);
lean_inc(v_a_1303_);
lean_dec_ref_known(v___x_1301_, 2);
v_fst_1304_ = lean_ctor_get(v_a_1302_, 0);
v_snd_1305_ = lean_ctor_get(v_a_1302_, 1);
v_isSharedCheck_1324_ = !lean_is_exclusive(v_a_1302_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1307_ = v_a_1302_;
v_isShared_1308_ = v_isSharedCheck_1324_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_snd_1305_);
lean_inc(v_fst_1304_);
lean_dec(v_a_1302_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1324_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v_ref_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1315_; 
v_ref_1309_ = lean_ctor_get(v___y_1296_, 5);
v___x_1310_ = l_Lean_SourceInfo_fromRef(v_ref_1309_, v___y_1290_);
v___x_1311_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
v___x_1312_ = l_Lean_SourceInfo_fromRef(v_tk_867_, v___x_841_);
lean_dec(v_tk_867_);
v___x_1313_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
if (v_isShared_1308_ == 0)
{
lean_ctor_set_tag(v___x_1307_, 2);
lean_ctor_set(v___x_1307_, 1, v___x_1313_);
lean_ctor_set(v___x_1307_, 0, v___x_1312_);
v___x_1315_ = v___x_1307_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1312_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v___x_1313_);
v___x_1315_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1317_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
if (lean_obj_tag(v___y_1291_) == 1)
{
lean_object* v_val_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v_val_1318_ = lean_ctor_get(v___y_1291_, 0);
lean_inc(v_val_1318_);
lean_dec_ref_known(v___y_1291_, 1);
v___x_1319_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
lean_inc(v___x_1310_);
v___x_1320_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1310_);
lean_ctor_set(v___x_1320_, 1, v___x_1319_);
v___x_1321_ = l_Array_mkArray2___redArg(v_val_1318_, v___x_1320_);
v___y_1253_ = v_a_1303_;
v___y_1254_ = v___x_1317_;
v___y_1255_ = v___x_1316_;
v___y_1256_ = v_x_1294_;
v___y_1257_ = v___x_1310_;
v___y_1258_ = v___x_1315_;
v___y_1259_ = v___y_1289_;
v___y_1260_ = v_fst_1304_;
v___y_1261_ = v_snd_1305_;
v___y_1262_ = v___x_1311_;
v___y_1263_ = v___y_1293_;
v___y_1264_ = v___x_1321_;
goto v___jp_1252_;
}
else
{
lean_object* v___x_1322_; 
lean_dec(v___y_1291_);
v___x_1322_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___y_1253_ = v_a_1303_;
v___y_1254_ = v___x_1317_;
v___y_1255_ = v___x_1316_;
v___y_1256_ = v_x_1294_;
v___y_1257_ = v___x_1310_;
v___y_1258_ = v___x_1315_;
v___y_1259_ = v___y_1289_;
v___y_1260_ = v_fst_1304_;
v___y_1261_ = v_snd_1305_;
v___y_1262_ = v___x_1311_;
v___y_1263_ = v___y_1293_;
v___y_1264_ = v___x_1322_;
goto v___jp_1252_;
}
}
}
}
else
{
lean_object* v_a_1325_; lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_dec(v_x_1294_);
lean_dec(v___y_1293_);
lean_dec(v___y_1291_);
lean_dec(v___y_1289_);
lean_dec(v_tk_867_);
v_a_1325_ = lean_ctor_get(v___x_1301_, 0);
v_a_1326_ = lean_ctor_get(v___x_1301_, 1);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1301_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_inc(v_a_1325_);
lean_dec(v___x_1301_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1325_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
v___jp_1334_:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v_doElems_1346_; uint8_t v___x_1347_; 
v___x_1344_ = l_Lean_Syntax_getArg(v___y_1340_, v___x_868_);
v___x_1345_ = l_Lean_Syntax_getArg(v___y_1340_, v___y_1337_);
lean_dec(v___y_1340_);
v_doElems_1346_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_1347_ = l_Lean_Syntax_isIdent(v___x_1344_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; uint8_t v___x_1349_; 
v___x_1348_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_1344_);
v___x_1349_ = l_Lean_Syntax_isOfKind(v___x_1344_, v___x_1348_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; 
v___x_1350_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1344_, v___y_1339_, v___y_1342_, v___y_1343_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v_a_1352_; lean_object* v_ref_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc_n(v_a_1351_, 2);
v_a_1352_ = lean_ctor_get(v___x_1350_, 1);
lean_inc(v_a_1352_);
lean_dec_ref_known(v___x_1350_, 2);
v_ref_1353_ = lean_ctor_get(v___y_1342_, 5);
v___x_1354_ = l_Lean_SourceInfo_fromRef(v_ref_1353_, v___y_1339_);
v___x_1355_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_1356_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1357_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
v___x_1358_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_1359_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_n(v___x_1354_, 15);
v___x_1360_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1354_);
lean_ctor_set(v___x_1360_, 1, v___x_1359_);
v___x_1361_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_1362_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1354_);
lean_ctor_set(v___x_1362_, 1, v___x_1356_);
lean_ctor_set(v___x_1362_, 2, v___x_1361_);
v___x_1363_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_1362_, 4);
v___x_1364_ = l_Lean_Syntax_node2(v___x_1354_, v___x_1363_, v___x_1362_, v_a_1351_);
v___x_1365_ = l_Lean_Syntax_node1(v___x_1354_, v___x_1356_, v___x_1364_);
v___x_1366_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_1367_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1354_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
v___x_1368_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_1369_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_1370_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_1371_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1354_);
lean_ctor_set(v___x_1371_, 1, v___x_1370_);
v___x_1372_ = l_Lean_Syntax_node1(v___x_1354_, v___x_1356_, v___x_1344_);
v___x_1373_ = l_Lean_Syntax_node1(v___x_1354_, v___x_1356_, v___x_1372_);
v___x_1374_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_1375_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1354_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
v___x_1376_ = l_Lean_Syntax_node4(v___x_1354_, v___x_1369_, v___x_1371_, v___x_1373_, v___x_1375_, v___y_1335_);
v___x_1377_ = l_Lean_Syntax_node1(v___x_1354_, v___x_1356_, v___x_1376_);
v___x_1378_ = l_Lean_Syntax_node1(v___x_1354_, v___x_1368_, v___x_1377_);
v___x_1379_ = l_Lean_Syntax_node7(v___x_1354_, v___x_1358_, v___x_1360_, v___x_1362_, v___x_1362_, v___x_1362_, v___x_1365_, v___x_1367_, v___x_1378_);
v___x_1380_ = l_Lean_Syntax_node2(v___x_1354_, v___x_1357_, v___x_1379_, v___x_1362_);
v___x_1381_ = l_Lean_Syntax_node1(v___x_1354_, v___x_1356_, v___x_1380_);
v___x_1382_ = l_Lean_Syntax_node1(v___x_1354_, v___x_1355_, v___x_1381_);
v___y_1288_ = v___y_1336_;
v___y_1289_ = v___y_1338_;
v___y_1290_ = v___y_1339_;
v___y_1291_ = v_h_x3f_1341_;
v___y_1292_ = v_doElems_1346_;
v___y_1293_ = v___x_1345_;
v_x_1294_ = v_a_1351_;
v_body_1295_ = v___x_1382_;
v___y_1296_ = v___y_1342_;
v___y_1297_ = v_a_1352_;
goto v___jp_1287_;
}
else
{
lean_object* v_a_1383_; lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
lean_dec(v___x_1345_);
lean_dec(v___x_1344_);
lean_dec(v_h_x3f_1341_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec(v_tk_867_);
v_a_1383_ = lean_ctor_get(v___x_1350_, 0);
v_a_1384_ = lean_ctor_get(v___x_1350_, 1);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1350_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_inc(v_a_1383_);
lean_dec(v___x_1350_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1383_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v_a_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
else
{
lean_object* v___x_1392_; 
v___x_1392_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1344_, v___y_1339_, v___y_1342_, v___y_1343_);
lean_dec(v___x_1344_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1393_; lean_object* v_a_1394_; 
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_a_1393_);
v_a_1394_ = lean_ctor_get(v___x_1392_, 1);
lean_inc(v_a_1394_);
lean_dec_ref_known(v___x_1392_, 2);
v___y_1288_ = v___y_1336_;
v___y_1289_ = v___y_1338_;
v___y_1290_ = v___y_1339_;
v___y_1291_ = v_h_x3f_1341_;
v___y_1292_ = v_doElems_1346_;
v___y_1293_ = v___x_1345_;
v_x_1294_ = v_a_1393_;
v_body_1295_ = v___y_1335_;
v___y_1296_ = v___y_1342_;
v___y_1297_ = v_a_1394_;
goto v___jp_1287_;
}
else
{
lean_object* v_a_1395_; lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
lean_dec(v___x_1345_);
lean_dec(v_h_x3f_1341_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec(v_tk_867_);
v_a_1395_ = lean_ctor_get(v___x_1392_, 0);
v_a_1396_ = lean_ctor_get(v___x_1392_, 1);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1398_ = v___x_1392_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_inc(v_a_1395_);
lean_dec(v___x_1392_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1395_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v_a_1396_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
}
else
{
v___y_1288_ = v___y_1336_;
v___y_1289_ = v___y_1338_;
v___y_1290_ = v___y_1339_;
v___y_1291_ = v_h_x3f_1341_;
v___y_1292_ = v_doElems_1346_;
v___y_1293_ = v___x_1345_;
v_x_1294_ = v___x_1344_;
v_body_1295_ = v___y_1335_;
v___y_1296_ = v___y_1342_;
v___y_1297_ = v___y_1343_;
goto v___jp_1287_;
}
}
v___jp_1404_:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; uint8_t v___x_1415_; 
v___x_1413_ = lean_box(0);
v___x_1414_ = lean_array_get(v___x_1413_, v___y_1407_, v___x_843_);
lean_inc(v___x_1414_);
v___x_1415_ = l_Lean_Syntax_isOfKind(v___x_1414_, v___x_1044_);
if (v___x_1415_ == 0)
{
lean_object* v___x_1416_; 
lean_dec(v___x_1414_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec(v_tk_867_);
v___x_1416_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1412_);
return v___x_1416_;
}
else
{
lean_object* v___x_1417_; uint8_t v___x_1418_; 
v___x_1417_ = l_Lean_Syntax_getArg(v___x_1414_, v___x_843_);
v___x_1418_ = l_Lean_Syntax_isNone(v___x_1417_);
if (v___x_1418_ == 0)
{
uint8_t v___x_1419_; 
lean_inc(v___x_1417_);
v___x_1419_ = l_Lean_Syntax_matchesNull(v___x_1417_, v___y_1408_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1420_; 
lean_dec(v___x_1417_);
lean_dec(v___x_1414_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec(v_tk_867_);
v___x_1420_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1412_);
return v___x_1420_;
}
else
{
lean_object* v_h_x3f_1421_; lean_object* v___x_1422_; 
v_h_x3f_1421_ = l_Lean_Syntax_getArg(v___x_1417_, v___x_843_);
lean_dec(v___x_1417_);
v___x_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1422_, 0, v_h_x3f_1421_);
v___y_1335_ = v___y_1406_;
v___y_1336_ = v___y_1407_;
v___y_1337_ = v___y_1405_;
v___y_1338_ = v___y_1409_;
v___y_1339_ = v___y_1410_;
v___y_1340_ = v___x_1414_;
v_h_x3f_1341_ = v___x_1422_;
v___y_1342_ = v___y_1411_;
v___y_1343_ = v___y_1412_;
goto v___jp_1334_;
}
}
else
{
lean_object* v___x_1423_; 
lean_dec(v___x_1417_);
v___x_1423_ = lean_box(0);
v___y_1335_ = v___y_1406_;
v___y_1336_ = v___y_1407_;
v___y_1337_ = v___y_1405_;
v___y_1338_ = v___y_1409_;
v___y_1339_ = v___y_1410_;
v___y_1340_ = v___x_1414_;
v_h_x3f_1341_ = v___x_1423_;
v___y_1342_ = v___y_1411_;
v___y_1343_ = v___y_1412_;
goto v___jp_1334_;
}
}
}
v___jp_1424_:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; uint8_t v___x_1429_; 
v___x_1427_ = l_Lean_Syntax_getArg(v___x_1043_, v___x_868_);
lean_dec(v___x_1043_);
v___x_1428_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__19));
v___x_1429_ = l_Lean_Syntax_isOfKind(v___x_1427_, v___x_1428_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; uint8_t v___x_1433_; 
v___x_1430_ = lean_unsigned_to_nat(2u);
v___x_1431_ = lean_unsigned_to_nat(3u);
v___x_1432_ = l_Lean_Syntax_getArg(v_stx_733_, v___x_1430_);
v___x_1433_ = l_Lean_Syntax_isNone(v___x_1432_);
if (v___x_1433_ == 0)
{
uint8_t v___x_1434_; 
lean_inc(v___x_1432_);
v___x_1434_ = l_Lean_Syntax_matchesNull(v___x_1432_, v___x_868_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; 
lean_dec(v___x_1432_);
lean_dec(v___x_869_);
lean_dec(v_tk_867_);
lean_dec(v_stx_733_);
v___x_1435_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1426_);
return v___x_1435_;
}
else
{
lean_object* v_inv_1436_; lean_object* v___x_1437_; uint8_t v___x_1438_; 
v_inv_1436_ = l_Lean_Syntax_getArg(v___x_1432_, v___x_843_);
lean_dec(v___x_1432_);
v___x_1437_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v_inv_1436_);
v___x_1438_ = l_Lean_Syntax_isOfKind(v_inv_1436_, v___x_1437_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1439_; 
lean_dec(v_inv_1436_);
lean_dec(v___x_869_);
lean_dec(v_tk_867_);
lean_dec(v_stx_733_);
v___x_1439_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1426_);
return v___x_1439_;
}
else
{
lean_object* v___x_1440_; 
v___x_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1440_, 0, v_inv_1436_);
v___y_1227_ = v___x_1430_;
v___y_1228_ = v___x_1431_;
v___y_1229_ = v___x_1429_;
v_inv_1230_ = v___x_1440_;
v___y_1231_ = v___y_1425_;
v___y_1232_ = v___y_1426_;
goto v___jp_1226_;
}
}
}
else
{
lean_object* v___x_1441_; 
lean_dec(v___x_1432_);
v___x_1441_ = lean_box(0);
v___y_1227_ = v___x_1430_;
v___y_1228_ = v___x_1431_;
v___y_1229_ = v___x_1429_;
v_inv_1230_ = v___x_1441_;
v___y_1231_ = v___y_1425_;
v___y_1232_ = v___y_1426_;
goto v___jp_1226_;
}
}
else
{
lean_object* v___x_1442_; lean_object* v___x_1443_; uint8_t v___x_1444_; 
v___x_1442_ = lean_unsigned_to_nat(2u);
v___x_1443_ = l_Lean_Syntax_getArg(v_stx_733_, v___x_1442_);
v___x_1444_ = l_Lean_Syntax_isNone(v___x_1443_);
if (v___x_1444_ == 0)
{
uint8_t v___x_1445_; 
lean_inc(v___x_1443_);
v___x_1445_ = l_Lean_Syntax_matchesNull(v___x_1443_, v___x_868_);
if (v___x_1445_ == 0)
{
lean_object* v___x_1446_; 
lean_dec(v___x_1443_);
lean_dec(v___x_869_);
lean_dec(v_tk_867_);
lean_dec(v_stx_733_);
v___x_1446_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1426_);
return v___x_1446_;
}
else
{
lean_object* v___x_1447_; lean_object* v___x_1448_; uint8_t v___x_1449_; 
v___x_1447_ = l_Lean_Syntax_getArg(v___x_1443_, v___x_843_);
lean_dec(v___x_1443_);
v___x_1448_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v___x_1447_);
v___x_1449_ = l_Lean_Syntax_isOfKind(v___x_1447_, v___x_1448_);
if (v___x_1449_ == 0)
{
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; 
lean_dec(v___x_1447_);
lean_dec(v___x_869_);
lean_dec(v_tk_867_);
lean_dec(v_stx_733_);
v___x_1450_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1426_);
return v___x_1450_;
}
else
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v_body_1453_; lean_object* v_decls_1454_; lean_object* v_decls_1455_; lean_object* v___x_1456_; uint8_t v___x_1457_; 
v___x_1451_ = lean_unsigned_to_nat(3u);
v___x_1452_ = lean_unsigned_to_nat(4u);
v_body_1453_ = l_Lean_Syntax_getArg(v_stx_733_, v___x_1452_);
lean_dec(v_stx_733_);
v_decls_1454_ = l_Lean_Syntax_getArgs(v___x_869_);
lean_dec(v___x_869_);
v_decls_1455_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_1454_);
lean_dec_ref(v_decls_1454_);
v___x_1456_ = lean_array_get_size(v_decls_1455_);
v___x_1457_ = lean_nat_dec_lt(v___x_868_, v___x_1456_);
if (v___x_1457_ == 0)
{
v___y_1405_ = v___x_1451_;
v___y_1406_ = v_body_1453_;
v___y_1407_ = v_decls_1455_;
v___y_1408_ = v___x_1442_;
v___y_1409_ = v___x_1447_;
v___y_1410_ = v___x_1449_;
v___y_1411_ = v___y_1425_;
v___y_1412_ = v___y_1426_;
goto v___jp_1404_;
}
else
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__15));
v___x_1459_ = l_Lean_Macro_throwErrorAt___redArg(v___x_1447_, v___x_1458_, v___y_1425_, v___y_1426_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 1);
lean_inc(v_a_1460_);
lean_dec_ref_known(v___x_1459_, 2);
v___y_1405_ = v___x_1451_;
v___y_1406_ = v_body_1453_;
v___y_1407_ = v_decls_1455_;
v___y_1408_ = v___x_1442_;
v___y_1409_ = v___x_1447_;
v___y_1410_ = v___x_1449_;
v___y_1411_ = v___y_1425_;
v___y_1412_ = v_a_1460_;
goto v___jp_1404_;
}
else
{
lean_object* v_a_1461_; lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
lean_dec_ref(v_decls_1455_);
lean_dec(v_body_1453_);
lean_dec(v___x_1447_);
lean_dec(v_tk_867_);
v_a_1461_ = lean_ctor_get(v___x_1459_, 0);
v_a_1462_ = lean_ctor_get(v___x_1459_, 1);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1464_ = v___x_1459_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_inc(v_a_1461_);
lean_dec(v___x_1459_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1461_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_a_1462_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
}
}
else
{
lean_object* v___x_1470_; 
lean_dec(v___x_1447_);
lean_dec(v___x_869_);
lean_dec(v_tk_867_);
lean_dec(v_stx_733_);
v___x_1470_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1426_);
return v___x_1470_;
}
}
}
else
{
lean_object* v___x_1471_; 
lean_dec(v___x_1443_);
lean_dec(v___x_869_);
lean_dec(v_tk_867_);
lean_dec(v_stx_733_);
v___x_1471_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1426_);
return v___x_1471_;
}
}
}
v___jp_1472_:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
lean_inc_ref(v___y_1477_);
v___x_1485_ = l_Array_append___redArg(v___y_1477_, v___y_1484_);
lean_dec_ref(v___y_1484_);
lean_inc_n(v___y_1479_, 2);
lean_inc_n(v___y_1476_, 4);
v___x_1486_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1486_, 0, v___y_1476_);
lean_ctor_set(v___x_1486_, 1, v___y_1479_);
lean_ctor_set(v___x_1486_, 2, v___x_1485_);
v___x_1487_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_1488_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1488_, 0, v___y_1476_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
v___x_1489_ = l_Lean_Syntax_node4(v___y_1476_, v___x_1044_, v___x_1486_, v___y_1483_, v___x_1488_, v___y_1482_);
v___x_1490_ = l_Lean_Syntax_node1(v___y_1476_, v___y_1479_, v___x_1489_);
if (lean_obj_tag(v___y_1474_) == 1)
{
lean_object* v_val_1491_; lean_object* v___x_1492_; 
v_val_1491_ = lean_ctor_get(v___y_1474_, 0);
lean_inc(v_val_1491_);
lean_dec_ref_known(v___y_1474_, 1);
v___x_1492_ = l_Array_mkArray1___redArg(v_val_1491_);
v___y_790_ = v___y_1473_;
v___y_791_ = v___y_1475_;
v___y_792_ = v___y_1476_;
v___y_793_ = v___x_1490_;
v___y_794_ = v___y_1477_;
v___y_795_ = v___y_1478_;
v___y_796_ = v___y_1479_;
v___y_797_ = v___y_1481_;
v___y_798_ = v___y_1480_;
v___y_799_ = v___x_1492_;
goto v___jp_789_;
}
else
{
lean_object* v___x_1493_; 
lean_dec(v___y_1474_);
v___x_1493_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___y_790_ = v___y_1473_;
v___y_791_ = v___y_1475_;
v___y_792_ = v___y_1476_;
v___y_793_ = v___x_1490_;
v___y_794_ = v___y_1477_;
v___y_795_ = v___y_1478_;
v___y_796_ = v___y_1479_;
v___y_797_ = v___y_1481_;
v___y_798_ = v___y_1480_;
v___y_799_ = v___x_1493_;
goto v___jp_789_;
}
}
v___jp_1495_:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1505_ = lean_array_get_size(v___y_1498_);
v___x_1506_ = l_Array_toSubarray___redArg(v___y_1498_, v___x_868_, v___x_1505_);
lean_inc_ref(v___y_1497_);
v___x_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___y_1497_);
lean_ctor_set(v___x_1507_, 1, v_body_1502_);
v___x_1508_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_1494_, v___x_1506_, v___x_1507_, v___y_1503_, v___y_1504_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v_a_1509_; lean_object* v_a_1510_; lean_object* v_fst_1511_; lean_object* v_snd_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1531_; 
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
lean_inc(v_a_1509_);
v_a_1510_ = lean_ctor_get(v___x_1508_, 1);
lean_inc(v_a_1510_);
lean_dec_ref_known(v___x_1508_, 2);
v_fst_1511_ = lean_ctor_get(v_a_1509_, 0);
v_snd_1512_ = lean_ctor_get(v_a_1509_, 1);
v_isSharedCheck_1531_ = !lean_is_exclusive(v_a_1509_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1514_ = v_a_1509_;
v_isShared_1515_ = v_isSharedCheck_1531_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_snd_1512_);
lean_inc(v_fst_1511_);
lean_dec(v_a_1509_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1531_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v_ref_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1522_; 
v_ref_1516_ = lean_ctor_get(v___y_1503_, 5);
v___x_1517_ = l_Lean_SourceInfo_fromRef(v_ref_1516_, v___x_1494_);
v___x_1518_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
v___x_1519_ = l_Lean_SourceInfo_fromRef(v_tk_867_, v___x_841_);
lean_dec(v_tk_867_);
v___x_1520_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
if (v_isShared_1515_ == 0)
{
lean_ctor_set_tag(v___x_1514_, 2);
lean_ctor_set(v___x_1514_, 1, v___x_1520_);
lean_ctor_set(v___x_1514_, 0, v___x_1519_);
v___x_1522_ = v___x_1514_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1519_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v___x_1520_);
v___x_1522_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1524_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
if (lean_obj_tag(v___y_1499_) == 1)
{
lean_object* v_val_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v_val_1525_ = lean_ctor_get(v___y_1499_, 0);
lean_inc(v_val_1525_);
lean_dec_ref_known(v___y_1499_, 1);
v___x_1526_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
lean_inc(v___x_1517_);
v___x_1527_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1517_);
lean_ctor_set(v___x_1527_, 1, v___x_1526_);
v___x_1528_ = l_Array_mkArray2___redArg(v_val_1525_, v___x_1527_);
v___y_1473_ = v___x_1518_;
v___y_1474_ = v___y_1496_;
v___y_1475_ = v___x_1522_;
v___y_1476_ = v___x_1517_;
v___y_1477_ = v___x_1524_;
v___y_1478_ = v_a_1510_;
v___y_1479_ = v___x_1523_;
v___y_1480_ = v_snd_1512_;
v___y_1481_ = v_fst_1511_;
v___y_1482_ = v___y_1500_;
v___y_1483_ = v_x_1501_;
v___y_1484_ = v___x_1528_;
goto v___jp_1472_;
}
else
{
lean_object* v___x_1529_; 
lean_dec(v___y_1499_);
v___x_1529_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___y_1473_ = v___x_1518_;
v___y_1474_ = v___y_1496_;
v___y_1475_ = v___x_1522_;
v___y_1476_ = v___x_1517_;
v___y_1477_ = v___x_1524_;
v___y_1478_ = v_a_1510_;
v___y_1479_ = v___x_1523_;
v___y_1480_ = v_snd_1512_;
v___y_1481_ = v_fst_1511_;
v___y_1482_ = v___y_1500_;
v___y_1483_ = v_x_1501_;
v___y_1484_ = v___x_1529_;
goto v___jp_1472_;
}
}
}
}
else
{
lean_object* v_a_1532_; lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1540_; 
lean_dec(v_x_1501_);
lean_dec(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec(v___y_1496_);
lean_dec(v_tk_867_);
v_a_1532_ = lean_ctor_get(v___x_1508_, 0);
v_a_1533_ = lean_ctor_get(v___x_1508_, 1);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1535_ = v___x_1508_;
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_inc(v_a_1532_);
lean_dec(v___x_1508_);
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
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1532_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_a_1533_);
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
v___jp_1541_:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v_doElems_1552_; uint8_t v___x_1553_; 
v___x_1550_ = l_Lean_Syntax_getArg(v___y_1543_, v___x_868_);
v___x_1551_ = l_Lean_Syntax_getArg(v___y_1543_, v___y_1542_);
lean_dec(v___y_1543_);
v_doElems_1552_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_1553_ = l_Lean_Syntax_isIdent(v___x_1550_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; uint8_t v___x_1555_; 
v___x_1554_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_1550_);
v___x_1555_ = l_Lean_Syntax_isOfKind(v___x_1550_, v___x_1554_);
if (v___x_1555_ == 0)
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1550_, v___x_1555_, v___y_1548_, v___y_1549_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v_a_1558_; lean_object* v_ref_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc_n(v_a_1557_, 2);
v_a_1558_ = lean_ctor_get(v___x_1556_, 1);
lean_inc(v_a_1558_);
lean_dec_ref_known(v___x_1556_, 2);
v_ref_1559_ = lean_ctor_get(v___y_1548_, 5);
v___x_1560_ = l_Lean_SourceInfo_fromRef(v_ref_1559_, v___x_1555_);
v___x_1561_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_1562_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1563_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
v___x_1564_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_1565_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_n(v___x_1560_, 15);
v___x_1566_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1560_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
v___x_1567_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_1568_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1560_);
lean_ctor_set(v___x_1568_, 1, v___x_1562_);
lean_ctor_set(v___x_1568_, 2, v___x_1567_);
v___x_1569_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_1568_, 4);
v___x_1570_ = l_Lean_Syntax_node2(v___x_1560_, v___x_1569_, v___x_1568_, v_a_1557_);
v___x_1571_ = l_Lean_Syntax_node1(v___x_1560_, v___x_1562_, v___x_1570_);
v___x_1572_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_1573_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1560_);
lean_ctor_set(v___x_1573_, 1, v___x_1572_);
v___x_1574_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_1575_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_1576_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_1577_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1560_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
v___x_1578_ = l_Lean_Syntax_node1(v___x_1560_, v___x_1562_, v___x_1550_);
v___x_1579_ = l_Lean_Syntax_node1(v___x_1560_, v___x_1562_, v___x_1578_);
v___x_1580_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_1581_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1560_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
v___x_1582_ = l_Lean_Syntax_node4(v___x_1560_, v___x_1575_, v___x_1577_, v___x_1579_, v___x_1581_, v___y_1544_);
v___x_1583_ = l_Lean_Syntax_node1(v___x_1560_, v___x_1562_, v___x_1582_);
v___x_1584_ = l_Lean_Syntax_node1(v___x_1560_, v___x_1574_, v___x_1583_);
v___x_1585_ = l_Lean_Syntax_node7(v___x_1560_, v___x_1564_, v___x_1566_, v___x_1568_, v___x_1568_, v___x_1568_, v___x_1571_, v___x_1573_, v___x_1584_);
v___x_1586_ = l_Lean_Syntax_node2(v___x_1560_, v___x_1563_, v___x_1585_, v___x_1568_);
v___x_1587_ = l_Lean_Syntax_node1(v___x_1560_, v___x_1562_, v___x_1586_);
v___x_1588_ = l_Lean_Syntax_node1(v___x_1560_, v___x_1561_, v___x_1587_);
v___y_1496_ = v___y_1545_;
v___y_1497_ = v_doElems_1552_;
v___y_1498_ = v___y_1546_;
v___y_1499_ = v_h_x3f_1547_;
v___y_1500_ = v___x_1551_;
v_x_1501_ = v_a_1557_;
v_body_1502_ = v___x_1588_;
v___y_1503_ = v___y_1548_;
v___y_1504_ = v_a_1558_;
goto v___jp_1495_;
}
else
{
lean_object* v_a_1589_; lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
lean_dec(v___x_1551_);
lean_dec(v___x_1550_);
lean_dec(v_h_x3f_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec(v___y_1544_);
lean_dec(v_tk_867_);
v_a_1589_ = lean_ctor_get(v___x_1556_, 0);
v_a_1590_ = lean_ctor_get(v___x_1556_, 1);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1556_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_inc(v_a_1589_);
lean_dec(v___x_1556_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1589_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
else
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1550_, v___x_1553_, v___y_1548_, v___y_1549_);
lean_dec(v___x_1550_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v_a_1600_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
v_a_1600_ = lean_ctor_get(v___x_1598_, 1);
lean_inc(v_a_1600_);
lean_dec_ref_known(v___x_1598_, 2);
v___y_1496_ = v___y_1545_;
v___y_1497_ = v_doElems_1552_;
v___y_1498_ = v___y_1546_;
v___y_1499_ = v_h_x3f_1547_;
v___y_1500_ = v___x_1551_;
v_x_1501_ = v_a_1599_;
v_body_1502_ = v___y_1544_;
v___y_1503_ = v___y_1548_;
v___y_1504_ = v_a_1600_;
goto v___jp_1495_;
}
else
{
lean_object* v_a_1601_; lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_dec(v___x_1551_);
lean_dec(v_h_x3f_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec(v___y_1544_);
lean_dec(v_tk_867_);
v_a_1601_ = lean_ctor_get(v___x_1598_, 0);
v_a_1602_ = lean_ctor_get(v___x_1598_, 1);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1598_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_inc(v_a_1601_);
lean_dec(v___x_1598_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1601_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
}
else
{
v___y_1496_ = v___y_1545_;
v___y_1497_ = v_doElems_1552_;
v___y_1498_ = v___y_1546_;
v___y_1499_ = v_h_x3f_1547_;
v___y_1500_ = v___x_1551_;
v_x_1501_ = v___x_1550_;
v_body_1502_ = v___y_1544_;
v___y_1503_ = v___y_1548_;
v___y_1504_ = v___y_1549_;
goto v___jp_1495_;
}
}
}
v___jp_844_:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
lean_inc_ref(v___y_854_);
v___x_858_ = l_Array_append___redArg(v___y_854_, v___y_857_);
lean_dec_ref(v___y_857_);
lean_inc_n(v___y_851_, 2);
lean_inc_n(v___y_845_, 4);
v___x_859_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_859_, 0, v___y_845_);
lean_ctor_set(v___x_859_, 1, v___y_851_);
lean_ctor_set(v___x_859_, 2, v___x_858_);
v___x_860_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___x_861_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_861_, 0, v___y_845_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
lean_inc(v___y_847_);
v___x_862_ = l_Lean_Syntax_node4(v___y_845_, v___y_847_, v___x_859_, v___y_846_, v___x_861_, v___y_850_);
v___x_863_ = l_Lean_Syntax_node1(v___y_845_, v___y_851_, v___x_862_);
if (lean_obj_tag(v___y_848_) == 1)
{
lean_object* v_val_864_; lean_object* v___x_865_; 
v_val_864_ = lean_ctor_get(v___y_848_, 0);
lean_inc(v_val_864_);
lean_dec_ref_known(v___y_848_, 1);
v___x_865_ = l_Array_mkArray1___redArg(v_val_864_);
v___y_816_ = v___y_845_;
v___y_817_ = v___y_849_;
v___y_818_ = v___y_851_;
v___y_819_ = v___y_853_;
v___y_820_ = v___y_852_;
v___y_821_ = v___x_863_;
v___y_822_ = v___y_854_;
v___y_823_ = v___y_855_;
v___y_824_ = v___y_856_;
v___y_825_ = v___x_865_;
goto v___jp_815_;
}
else
{
lean_object* v___x_866_; 
lean_dec(v___y_848_);
v___x_866_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___y_816_ = v___y_845_;
v___y_817_ = v___y_849_;
v___y_818_ = v___y_851_;
v___y_819_ = v___y_853_;
v___y_820_ = v___y_852_;
v___y_821_ = v___x_863_;
v___y_822_ = v___y_854_;
v___y_823_ = v___y_855_;
v___y_824_ = v___y_856_;
v___y_825_ = v___x_866_;
goto v___jp_815_;
}
}
v___jp_871_:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_882_ = lean_array_get_size(v___y_874_);
v___x_883_ = l_Array_toSubarray___redArg(v___y_874_, v___x_868_, v___x_882_);
lean_inc_ref(v___y_872_);
v___x_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_884_, 0, v___y_872_);
lean_ctor_set(v___x_884_, 1, v_body_879_);
v___x_885_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_870_, v___x_883_, v___x_884_, v___y_880_, v___y_881_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v_a_887_; lean_object* v_fst_888_; lean_object* v_snd_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_908_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
v_a_887_ = lean_ctor_get(v___x_885_, 1);
lean_inc(v_a_887_);
lean_dec_ref_known(v___x_885_, 2);
v_fst_888_ = lean_ctor_get(v_a_886_, 0);
v_snd_889_ = lean_ctor_get(v_a_886_, 1);
v_isSharedCheck_908_ = !lean_is_exclusive(v_a_886_);
if (v_isSharedCheck_908_ == 0)
{
v___x_891_ = v_a_886_;
v_isShared_892_ = v_isSharedCheck_908_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_snd_889_);
lean_inc(v_fst_888_);
lean_dec(v_a_886_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_908_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v_ref_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_899_; 
v_ref_893_ = lean_ctor_get(v___y_880_, 5);
v___x_894_ = l_Lean_SourceInfo_fromRef(v_ref_893_, v___x_870_);
v___x_895_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
v___x_896_ = l_Lean_SourceInfo_fromRef(v_tk_867_, v___x_841_);
lean_dec(v_tk_867_);
v___x_897_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
if (v_isShared_892_ == 0)
{
lean_ctor_set_tag(v___x_891_, 2);
lean_ctor_set(v___x_891_, 1, v___x_897_);
lean_ctor_set(v___x_891_, 0, v___x_896_);
v___x_899_ = v___x_891_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v___x_897_);
v___x_899_ = v_reuseFailAlloc_907_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_901_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
if (lean_obj_tag(v___y_877_) == 1)
{
lean_object* v_val_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v_val_902_ = lean_ctor_get(v___y_877_, 0);
lean_inc(v_val_902_);
lean_dec_ref_known(v___y_877_, 1);
v___x_903_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
lean_inc(v___x_894_);
v___x_904_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_894_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = l_Array_mkArray2___redArg(v_val_902_, v___x_904_);
v___y_845_ = v___x_894_;
v___y_846_ = v_x_878_;
v___y_847_ = v___y_873_;
v___y_848_ = v___y_876_;
v___y_849_ = v_snd_889_;
v___y_850_ = v___y_875_;
v___y_851_ = v___x_900_;
v___y_852_ = v___x_895_;
v___y_853_ = v_fst_888_;
v___y_854_ = v___x_901_;
v___y_855_ = v_a_887_;
v___y_856_ = v___x_899_;
v___y_857_ = v___x_905_;
goto v___jp_844_;
}
else
{
lean_object* v___x_906_; 
lean_dec(v___y_877_);
v___x_906_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___y_845_ = v___x_894_;
v___y_846_ = v_x_878_;
v___y_847_ = v___y_873_;
v___y_848_ = v___y_876_;
v___y_849_ = v_snd_889_;
v___y_850_ = v___y_875_;
v___y_851_ = v___x_900_;
v___y_852_ = v___x_895_;
v___y_853_ = v_fst_888_;
v___y_854_ = v___x_901_;
v___y_855_ = v_a_887_;
v___y_856_ = v___x_899_;
v___y_857_ = v___x_906_;
goto v___jp_844_;
}
}
}
}
else
{
lean_object* v_a_909_; lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
lean_dec(v_x_878_);
lean_dec(v___y_877_);
lean_dec(v___y_876_);
lean_dec(v___y_875_);
lean_dec(v_tk_867_);
v_a_909_ = lean_ctor_get(v___x_885_, 0);
v_a_910_ = lean_ctor_get(v___x_885_, 1);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v___x_885_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_inc(v_a_909_);
lean_dec(v___x_885_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_909_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v_a_910_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
v___jp_918_:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v_doElems_930_; uint8_t v___x_931_; 
v___x_928_ = l_Lean_Syntax_getArg(v___y_924_, v___x_868_);
v___x_929_ = l_Lean_Syntax_getArg(v___y_924_, v___y_923_);
lean_dec(v___y_924_);
v_doElems_930_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_931_ = l_Lean_Syntax_isIdent(v___x_928_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; uint8_t v___x_933_; 
v___x_932_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_928_);
v___x_933_ = l_Lean_Syntax_isOfKind(v___x_928_, v___x_932_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; 
v___x_934_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_928_, v___x_933_, v___y_926_, v___y_927_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v_a_935_; lean_object* v_a_936_; lean_object* v_ref_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v_a_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc_n(v_a_935_, 2);
v_a_936_ = lean_ctor_get(v___x_934_, 1);
lean_inc(v_a_936_);
lean_dec_ref_known(v___x_934_, 2);
v_ref_937_ = lean_ctor_get(v___y_926_, 5);
v___x_938_ = l_Lean_SourceInfo_fromRef(v_ref_937_, v___x_933_);
v___x_939_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_940_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_941_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
v___x_942_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_943_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_n(v___x_938_, 15);
v___x_944_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_938_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_946_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_946_, 0, v___x_938_);
lean_ctor_set(v___x_946_, 1, v___x_940_);
lean_ctor_set(v___x_946_, 2, v___x_945_);
v___x_947_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_946_, 4);
v___x_948_ = l_Lean_Syntax_node2(v___x_938_, v___x_947_, v___x_946_, v_a_935_);
v___x_949_ = l_Lean_Syntax_node1(v___x_938_, v___x_940_, v___x_948_);
v___x_950_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_951_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_938_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
v___x_952_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_953_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_954_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_955_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_938_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v___x_956_ = l_Lean_Syntax_node1(v___x_938_, v___x_940_, v___x_928_);
v___x_957_ = l_Lean_Syntax_node1(v___x_938_, v___x_940_, v___x_956_);
v___x_958_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_959_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_938_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = l_Lean_Syntax_node4(v___x_938_, v___x_953_, v___x_955_, v___x_957_, v___x_959_, v___y_921_);
v___x_961_ = l_Lean_Syntax_node1(v___x_938_, v___x_940_, v___x_960_);
v___x_962_ = l_Lean_Syntax_node1(v___x_938_, v___x_952_, v___x_961_);
v___x_963_ = l_Lean_Syntax_node7(v___x_938_, v___x_942_, v___x_944_, v___x_946_, v___x_946_, v___x_946_, v___x_949_, v___x_951_, v___x_962_);
v___x_964_ = l_Lean_Syntax_node2(v___x_938_, v___x_941_, v___x_963_, v___x_946_);
v___x_965_ = l_Lean_Syntax_node1(v___x_938_, v___x_940_, v___x_964_);
v___x_966_ = l_Lean_Syntax_node1(v___x_938_, v___x_939_, v___x_965_);
v___y_872_ = v_doElems_930_;
v___y_873_ = v___y_920_;
v___y_874_ = v___y_919_;
v___y_875_ = v___x_929_;
v___y_876_ = v___y_922_;
v___y_877_ = v_h_x3f_925_;
v_x_878_ = v_a_935_;
v_body_879_ = v___x_966_;
v___y_880_ = v___y_926_;
v___y_881_ = v_a_936_;
goto v___jp_871_;
}
else
{
lean_object* v_a_967_; lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
lean_dec(v___x_929_);
lean_dec(v___x_928_);
lean_dec(v_h_x3f_925_);
lean_dec(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_919_);
lean_dec(v_tk_867_);
v_a_967_ = lean_ctor_get(v___x_934_, 0);
v_a_968_ = lean_ctor_get(v___x_934_, 1);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v___x_934_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_inc(v_a_967_);
lean_dec(v___x_934_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_967_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_a_968_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
else
{
lean_object* v___x_976_; 
v___x_976_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_928_, v___x_931_, v___y_926_, v___y_927_);
lean_dec(v___x_928_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; lean_object* v_a_978_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_a_977_);
v_a_978_ = lean_ctor_get(v___x_976_, 1);
lean_inc(v_a_978_);
lean_dec_ref_known(v___x_976_, 2);
v___y_872_ = v_doElems_930_;
v___y_873_ = v___y_920_;
v___y_874_ = v___y_919_;
v___y_875_ = v___x_929_;
v___y_876_ = v___y_922_;
v___y_877_ = v_h_x3f_925_;
v_x_878_ = v_a_977_;
v_body_879_ = v___y_921_;
v___y_880_ = v___y_926_;
v___y_881_ = v_a_978_;
goto v___jp_871_;
}
else
{
lean_object* v_a_979_; lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_dec(v___x_929_);
lean_dec(v_h_x3f_925_);
lean_dec(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_919_);
lean_dec(v_tk_867_);
v_a_979_ = lean_ctor_get(v___x_976_, 0);
v_a_980_ = lean_ctor_get(v___x_976_, 1);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_976_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_inc(v_a_979_);
lean_dec(v___x_976_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_979_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
}
else
{
v___y_872_ = v_doElems_930_;
v___y_873_ = v___y_920_;
v___y_874_ = v___y_919_;
v___y_875_ = v___x_929_;
v___y_876_ = v___y_922_;
v___y_877_ = v_h_x3f_925_;
v_x_878_ = v___x_928_;
v_body_879_ = v___y_921_;
v___y_880_ = v___y_926_;
v___y_881_ = v___y_927_;
goto v___jp_871_;
}
}
}
v___jp_737_:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
lean_inc_ref_n(v___y_745_, 3);
v___x_748_ = l_Array_append___redArg(v___y_745_, v___y_747_);
lean_dec_ref(v___y_747_);
lean_inc_n(v___y_743_, 3);
lean_inc_n(v___y_740_, 7);
v___x_749_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_749_, 0, v___y_740_);
lean_ctor_set(v___x_749_, 1, v___y_743_);
lean_ctor_set(v___x_749_, 2, v___x_748_);
v___x_750_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_751_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_751_, 0, v___y_740_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
lean_inc_ref(v___x_751_);
v___x_752_ = l_Lean_Syntax_node5(v___y_740_, v___x_736_, v___y_742_, v___y_744_, v___x_749_, v___x_751_, v___y_746_);
v___x_753_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_753_, 0, v___y_740_);
lean_ctor_set(v___x_753_, 1, v___y_743_);
lean_ctor_set(v___x_753_, 2, v___y_745_);
lean_inc(v___y_739_);
v___x_754_ = l_Lean_Syntax_node2(v___y_740_, v___y_739_, v___x_752_, v___x_753_);
v___x_755_ = lean_array_push(v___y_738_, v___x_754_);
v___x_756_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_757_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_758_ = l_Array_append___redArg(v___y_745_, v___x_755_);
lean_dec_ref(v___x_755_);
v___x_759_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_759_, 0, v___y_740_);
lean_ctor_set(v___x_759_, 1, v___y_743_);
lean_ctor_set(v___x_759_, 2, v___x_758_);
v___x_760_ = l_Lean_Syntax_node1(v___y_740_, v___x_757_, v___x_759_);
v___x_761_ = l_Lean_Syntax_node2(v___y_740_, v___x_756_, v___x_751_, v___x_760_);
v___x_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
lean_ctor_set(v___x_762_, 1, v___y_741_);
return v___x_762_;
}
v___jp_763_:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
lean_inc_ref_n(v___y_769_, 3);
v___x_774_ = l_Array_append___redArg(v___y_769_, v___y_773_);
lean_dec_ref(v___y_773_);
lean_inc_n(v___y_771_, 3);
lean_inc_n(v___y_768_, 7);
v___x_775_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_775_, 0, v___y_768_);
lean_ctor_set(v___x_775_, 1, v___y_771_);
lean_ctor_set(v___x_775_, 2, v___x_774_);
v___x_776_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_777_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_777_, 0, v___y_768_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
lean_inc_ref(v___x_777_);
v___x_778_ = l_Lean_Syntax_node5(v___y_768_, v___x_736_, v___y_767_, v___y_764_, v___x_775_, v___x_777_, v___y_765_);
v___x_779_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_779_, 0, v___y_768_);
lean_ctor_set(v___x_779_, 1, v___y_771_);
lean_ctor_set(v___x_779_, 2, v___y_769_);
lean_inc(v___y_766_);
v___x_780_ = l_Lean_Syntax_node2(v___y_768_, v___y_766_, v___x_778_, v___x_779_);
v___x_781_ = lean_array_push(v___y_770_, v___x_780_);
v___x_782_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_783_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_784_ = l_Array_append___redArg(v___y_769_, v___x_781_);
lean_dec_ref(v___x_781_);
v___x_785_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_785_, 0, v___y_768_);
lean_ctor_set(v___x_785_, 1, v___y_771_);
lean_ctor_set(v___x_785_, 2, v___x_784_);
v___x_786_ = l_Lean_Syntax_node1(v___y_768_, v___x_783_, v___x_785_);
v___x_787_ = l_Lean_Syntax_node2(v___y_768_, v___x_782_, v___x_777_, v___x_786_);
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
lean_ctor_set(v___x_788_, 1, v___y_772_);
return v___x_788_;
}
v___jp_789_:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
lean_inc_ref_n(v___y_794_, 3);
v___x_800_ = l_Array_append___redArg(v___y_794_, v___y_799_);
lean_dec_ref(v___y_799_);
lean_inc_n(v___y_796_, 3);
lean_inc_n(v___y_792_, 7);
v___x_801_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_801_, 0, v___y_792_);
lean_ctor_set(v___x_801_, 1, v___y_796_);
lean_ctor_set(v___x_801_, 2, v___x_800_);
v___x_802_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_803_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_803_, 0, v___y_792_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
lean_inc_ref(v___x_803_);
v___x_804_ = l_Lean_Syntax_node5(v___y_792_, v___x_736_, v___y_791_, v___y_793_, v___x_801_, v___x_803_, v___y_798_);
v___x_805_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_805_, 0, v___y_792_);
lean_ctor_set(v___x_805_, 1, v___y_796_);
lean_ctor_set(v___x_805_, 2, v___y_794_);
lean_inc(v___y_790_);
v___x_806_ = l_Lean_Syntax_node2(v___y_792_, v___y_790_, v___x_804_, v___x_805_);
v___x_807_ = lean_array_push(v___y_797_, v___x_806_);
v___x_808_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_809_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_810_ = l_Array_append___redArg(v___y_794_, v___x_807_);
lean_dec_ref(v___x_807_);
v___x_811_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_811_, 0, v___y_792_);
lean_ctor_set(v___x_811_, 1, v___y_796_);
lean_ctor_set(v___x_811_, 2, v___x_810_);
v___x_812_ = l_Lean_Syntax_node1(v___y_792_, v___x_809_, v___x_811_);
v___x_813_ = l_Lean_Syntax_node2(v___y_792_, v___x_808_, v___x_803_, v___x_812_);
v___x_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
lean_ctor_set(v___x_814_, 1, v___y_795_);
return v___x_814_;
}
v___jp_815_:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
lean_inc_ref_n(v___y_822_, 3);
v___x_826_ = l_Array_append___redArg(v___y_822_, v___y_825_);
lean_dec_ref(v___y_825_);
lean_inc_n(v___y_818_, 3);
lean_inc_n(v___y_816_, 7);
v___x_827_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_827_, 0, v___y_816_);
lean_ctor_set(v___x_827_, 1, v___y_818_);
lean_ctor_set(v___x_827_, 2, v___x_826_);
v___x_828_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_829_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_829_, 0, v___y_816_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
lean_inc_ref(v___x_829_);
v___x_830_ = l_Lean_Syntax_node5(v___y_816_, v___x_736_, v___y_824_, v___y_821_, v___x_827_, v___x_829_, v___y_817_);
v___x_831_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_831_, 0, v___y_816_);
lean_ctor_set(v___x_831_, 1, v___y_818_);
lean_ctor_set(v___x_831_, 2, v___y_822_);
lean_inc(v___y_820_);
v___x_832_ = l_Lean_Syntax_node2(v___y_816_, v___y_820_, v___x_830_, v___x_831_);
v___x_833_ = lean_array_push(v___y_819_, v___x_832_);
v___x_834_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_835_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_836_ = l_Array_append___redArg(v___y_822_, v___x_833_);
lean_dec_ref(v___x_833_);
v___x_837_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_837_, 0, v___y_816_);
lean_ctor_set(v___x_837_, 1, v___y_818_);
lean_ctor_set(v___x_837_, 2, v___x_836_);
v___x_838_ = l_Lean_Syntax_node1(v___y_816_, v___x_835_, v___x_837_);
v___x_839_ = l_Lean_Syntax_node2(v___y_816_, v___x_834_, v___x_829_, v___x_838_);
v___x_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
lean_ctor_set(v___x_840_, 1, v___y_823_);
return v___x_840_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor___boxed(lean_object* v_stx_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_Lean_Elab_Do_expandDoFor(v_stx_1832_, v_a_1833_, v_a_1834_);
lean_dec_ref(v_a_1833_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0(uint8_t v___x_1836_, lean_object* v_inst_1837_, lean_object* v_R_1838_, lean_object* v_a_1839_, lean_object* v_b_1840_, lean_object* v_c_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_1836_, v_a_1839_, v_b_1840_, v___y_1842_, v___y_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___boxed(lean_object* v___x_1845_, lean_object* v_inst_1846_, lean_object* v_R_1847_, lean_object* v_a_1848_, lean_object* v_b_1849_, lean_object* v_c_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
uint8_t v___x_197233__boxed_1853_; lean_object* v_res_1854_; 
v___x_197233__boxed_1853_ = lean_unbox(v___x_1845_);
v_res_1854_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0(v___x_197233__boxed_1853_, v_inst_1846_, v_R_1847_, v_a_1848_, v_b_1849_, v_c_1850_, v___y_1851_, v___y_1852_);
lean_dec_ref(v___y_1851_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2(uint8_t v___x_1855_, lean_object* v_inst_1856_, lean_object* v_R_1857_, lean_object* v_a_1858_, lean_object* v_b_1859_, lean_object* v_c_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg(v___x_1855_, v_a_1858_, v_b_1859_, v___y_1861_, v___y_1862_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___boxed(lean_object* v___x_1864_, lean_object* v_inst_1865_, lean_object* v_R_1866_, lean_object* v_a_1867_, lean_object* v_b_1868_, lean_object* v_c_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
uint8_t v___x_197247__boxed_1872_; lean_object* v_res_1873_; 
v___x_197247__boxed_1872_ = lean_unbox(v___x_1864_);
v_res_1873_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2(v___x_197247__boxed_1872_, v_inst_1865_, v_R_1866_, v_a_1867_, v_b_1868_, v_c_1869_, v___y_1870_, v___y_1871_);
lean_dec_ref(v___y_1870_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1(){
_start:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1881_ = l_Lean_Elab_macroAttribute;
v___x_1882_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
v___x_1883_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1));
v___x_1884_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_expandDoFor___boxed), 3, 0);
v___x_1885_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1881_, v___x_1882_, v___x_1883_, v___x_1884_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___boxed(lean_object* v_a_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1();
return v_res_1887_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__2(void){
_start:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1894_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__1));
v___x_1895_ = l_Lean_stringToMessageData(v___x_1894_);
return v___x_1895_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__3(void){
_start:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1896_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__2, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__2_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__2);
v___x_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg(lean_object* v_invClause_1909_, lean_object* v_h_x3f_1910_, lean_object* v_xs_1911_, lean_object* v_00_u03b1_1912_, lean_object* v_mi_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_){
_start:
{
uint8_t v___y_1922_; lean_object* v___y_1923_; 
if (lean_obj_tag(v_h_x3f_1910_) == 0)
{
uint8_t v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = 1;
v___x_2025_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__6));
v___y_1922_ = v___x_2024_;
v___y_1923_ = v___x_2025_;
goto v___jp_1921_;
}
else
{
uint8_t v___x_2026_; lean_object* v___x_2027_; 
v___x_2026_ = 1;
v___x_2027_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__8));
v___y_1922_ = v___x_2026_;
v___y_1923_ = v___x_2027_;
goto v___jp_1921_;
}
v___jp_1921_:
{
lean_object* v___x_1924_; lean_object* v_env_1925_; uint8_t v___x_1926_; 
v___x_1924_ = lean_st_ref_get(v_a_1919_);
v_env_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc_ref(v_env_1925_);
lean_dec(v___x_1924_);
lean_inc(v___y_1923_);
v___x_1926_ = l_Lean_Environment_contains(v_env_1925_, v___y_1923_, v___y_1922_);
if (v___x_1926_ == 0)
{
lean_object* v___x_1927_; lean_object* v___x_1928_; 
lean_dec_ref(v_mi_1913_);
lean_dec_ref(v_00_u03b1_1912_);
lean_dec_ref(v_xs_1911_);
v___x_1927_ = lean_box(0);
v___x_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1927_);
return v___x_1928_;
}
else
{
lean_object* v_fileName_1929_; lean_object* v_fileMap_1930_; lean_object* v_options_1931_; lean_object* v_currRecDepth_1932_; lean_object* v_maxRecDepth_1933_; lean_object* v_ref_1934_; lean_object* v_currNamespace_1935_; lean_object* v_openDecls_1936_; lean_object* v_initHeartbeats_1937_; lean_object* v_maxHeartbeats_1938_; lean_object* v_quotContext_1939_; lean_object* v_currMacroScope_1940_; uint8_t v_diag_1941_; lean_object* v_cancelTk_x3f_1942_; uint8_t v_suppressElabErrors_1943_; lean_object* v_inheritedTraceOptions_1944_; lean_object* v_m_1945_; lean_object* v_ref_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v_fileName_1929_ = lean_ctor_get(v_a_1918_, 0);
v_fileMap_1930_ = lean_ctor_get(v_a_1918_, 1);
v_options_1931_ = lean_ctor_get(v_a_1918_, 2);
v_currRecDepth_1932_ = lean_ctor_get(v_a_1918_, 3);
v_maxRecDepth_1933_ = lean_ctor_get(v_a_1918_, 4);
v_ref_1934_ = lean_ctor_get(v_a_1918_, 5);
v_currNamespace_1935_ = lean_ctor_get(v_a_1918_, 6);
v_openDecls_1936_ = lean_ctor_get(v_a_1918_, 7);
v_initHeartbeats_1937_ = lean_ctor_get(v_a_1918_, 8);
v_maxHeartbeats_1938_ = lean_ctor_get(v_a_1918_, 9);
v_quotContext_1939_ = lean_ctor_get(v_a_1918_, 10);
v_currMacroScope_1940_ = lean_ctor_get(v_a_1918_, 11);
v_diag_1941_ = lean_ctor_get_uint8(v_a_1918_, sizeof(void*)*14);
v_cancelTk_x3f_1942_ = lean_ctor_get(v_a_1918_, 12);
v_suppressElabErrors_1943_ = lean_ctor_get_uint8(v_a_1918_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1944_ = lean_ctor_get(v_a_1918_, 13);
v_m_1945_ = lean_ctor_get(v_mi_1913_, 0);
lean_inc_ref(v_m_1945_);
lean_dec_ref(v_mi_1913_);
v_ref_1946_ = l_Lean_replaceRef(v_invClause_1909_, v_ref_1934_);
lean_inc_ref(v_inheritedTraceOptions_1944_);
lean_inc(v_cancelTk_x3f_1942_);
lean_inc(v_currMacroScope_1940_);
lean_inc(v_quotContext_1939_);
lean_inc(v_maxHeartbeats_1938_);
lean_inc(v_initHeartbeats_1937_);
lean_inc(v_openDecls_1936_);
lean_inc(v_currNamespace_1935_);
lean_inc(v_ref_1946_);
lean_inc(v_maxRecDepth_1933_);
lean_inc(v_currRecDepth_1932_);
lean_inc_ref(v_options_1931_);
lean_inc_ref(v_fileMap_1930_);
lean_inc_ref(v_fileName_1929_);
v___x_1947_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1947_, 0, v_fileName_1929_);
lean_ctor_set(v___x_1947_, 1, v_fileMap_1930_);
lean_ctor_set(v___x_1947_, 2, v_options_1931_);
lean_ctor_set(v___x_1947_, 3, v_currRecDepth_1932_);
lean_ctor_set(v___x_1947_, 4, v_maxRecDepth_1933_);
lean_ctor_set(v___x_1947_, 5, v_ref_1946_);
lean_ctor_set(v___x_1947_, 6, v_currNamespace_1935_);
lean_ctor_set(v___x_1947_, 7, v_openDecls_1936_);
lean_ctor_set(v___x_1947_, 8, v_initHeartbeats_1937_);
lean_ctor_set(v___x_1947_, 9, v_maxHeartbeats_1938_);
lean_ctor_set(v___x_1947_, 10, v_quotContext_1939_);
lean_ctor_set(v___x_1947_, 11, v_currMacroScope_1940_);
lean_ctor_set(v___x_1947_, 12, v_cancelTk_x3f_1942_);
lean_ctor_set(v___x_1947_, 13, v_inheritedTraceOptions_1944_);
lean_ctor_set_uint8(v___x_1947_, sizeof(void*)*14, v_diag_1941_);
lean_ctor_set_uint8(v___x_1947_, sizeof(void*)*14 + 1, v_suppressElabErrors_1943_);
v___x_1948_ = l_Lean_Elab_Term_exprToSyntax(v_m_1945_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v___x_1947_, v_a_1919_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; lean_object* v___x_1950_; 
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_a_1949_);
lean_dec_ref_known(v___x_1948_, 1);
lean_inc(v_a_1919_);
lean_inc_ref(v___x_1947_);
lean_inc(v_a_1917_);
lean_inc_ref(v_a_1916_);
v___x_1950_ = lean_infer_type(v_xs_1911_, v_a_1916_, v_a_1917_, v___x_1947_, v_a_1919_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; lean_object* v___x_1952_; 
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
lean_inc(v_a_1951_);
lean_dec_ref_known(v___x_1950_, 1);
v___x_1952_ = l_Lean_Elab_Term_exprToSyntax(v_a_1951_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v___x_1947_, v_a_1919_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; lean_object* v___x_1954_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1953_);
lean_dec_ref_known(v___x_1952_, 1);
v___x_1954_ = l_Lean_Elab_Term_exprToSyntax(v_00_u03b1_1912_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v___x_1947_, v_a_1919_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; uint8_t v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_a_1955_);
lean_dec_ref_known(v___x_1954_, 1);
v___x_1956_ = 0;
v___x_1957_ = l_Lean_SourceInfo_fromRef(v_ref_1946_, v___x_1956_);
lean_dec(v_ref_1946_);
v___x_1958_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__0));
lean_inc(v___y_1923_);
v___x_1959_ = l_Lean_mkIdent(v___y_1923_);
v___x_1960_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
lean_inc(v___x_1957_);
v___x_1961_ = l_Lean_Syntax_node3(v___x_1957_, v___x_1960_, v_a_1949_, v_a_1953_, v_a_1955_);
v___x_1962_ = l_Lean_Syntax_node2(v___x_1957_, v___x_1958_, v___x_1959_, v___x_1961_);
v___x_1963_ = l_Lean_Elab_Term_elabType(v___x_1962_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v___x_1947_, v_a_1919_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v_a_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
v_a_1964_ = lean_ctor_get(v___x_1963_, 0);
lean_inc(v_a_1964_);
lean_dec_ref_known(v___x_1963_, 1);
v___x_1965_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__3, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__3);
v___x_1966_ = l_Lean_Elab_Term_mkInstMVar(v_a_1964_, v___x_1965_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v___x_1947_, v_a_1919_);
lean_dec_ref_known(v___x_1947_, 14);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1974_; 
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1974_ == 0)
{
lean_object* v_unused_1975_; 
v_unused_1975_ = lean_ctor_get(v___x_1966_, 0);
lean_dec(v_unused_1975_);
v___x_1968_ = v___x_1966_;
v_isShared_1969_ = v_isSharedCheck_1974_;
goto v_resetjp_1967_;
}
else
{
lean_dec(v___x_1966_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1974_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1970_; lean_object* v___x_1972_; 
v___x_1970_ = lean_box(0);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 0, v___x_1970_);
v___x_1972_ = v___x_1968_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1970_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
else
{
lean_object* v_a_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1983_; 
v_a_1976_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1978_ = v___x_1966_;
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_a_1976_);
lean_dec(v___x_1966_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1981_; 
if (v_isShared_1979_ == 0)
{
v___x_1981_ = v___x_1978_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1976_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
lean_dec_ref_known(v___x_1947_, 14);
v_a_1984_ = lean_ctor_get(v___x_1963_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1963_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1963_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
lean_dec(v_a_1953_);
lean_dec(v_a_1949_);
lean_dec_ref_known(v___x_1947_, 14);
lean_dec(v_ref_1946_);
v_a_1992_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1954_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1954_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
else
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
lean_dec(v_a_1949_);
lean_dec_ref_known(v___x_1947_, 14);
lean_dec(v_ref_1946_);
lean_dec_ref(v_00_u03b1_1912_);
v_a_2000_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1952_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1952_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
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
else
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
lean_dec(v_a_1949_);
lean_dec_ref_known(v___x_1947_, 14);
lean_dec(v_ref_1946_);
lean_dec_ref(v_00_u03b1_1912_);
v_a_2008_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1950_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_1950_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_dec_ref_known(v___x_1947_, 14);
lean_dec(v_ref_1946_);
lean_dec_ref(v_00_u03b1_1912_);
lean_dec_ref(v_xs_1911_);
v_a_2016_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_1948_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_1948_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___boxed(lean_object* v_invClause_2028_, lean_object* v_h_x3f_2029_, lean_object* v_xs_2030_, lean_object* v_00_u03b1_2031_, lean_object* v_mi_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg(v_invClause_2028_, v_h_x3f_2029_, v_xs_2030_, v_00_u03b1_2031_, v_mi_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_);
lean_dec(v_a_2038_);
lean_dec_ref(v_a_2037_);
lean_dec(v_a_2036_);
lean_dec_ref(v_a_2035_);
lean_dec(v_a_2034_);
lean_dec_ref(v_a_2033_);
lean_dec(v_h_x3f_2029_);
lean_dec(v_invClause_2028_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn(lean_object* v_invClause_2041_, lean_object* v_h_x3f_2042_, lean_object* v_xs_2043_, lean_object* v_00_u03b1_2044_, lean_object* v_mi_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_){
_start:
{
lean_object* v___x_2054_; 
v___x_2054_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg(v_invClause_2041_, v_h_x3f_2042_, v_xs_2043_, v_00_u03b1_2044_, v_mi_2045_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___boxed(lean_object* v_invClause_2055_, lean_object* v_h_x3f_2056_, lean_object* v_xs_2057_, lean_object* v_00_u03b1_2058_, lean_object* v_mi_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn(v_invClause_2055_, v_h_x3f_2056_, v_xs_2057_, v_00_u03b1_2058_, v_mi_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_);
lean_dec(v_a_2066_);
lean_dec_ref(v_a_2065_);
lean_dec(v_a_2064_);
lean_dec_ref(v_a_2063_);
lean_dec(v_a_2062_);
lean_dec_ref(v_a_2061_);
lean_dec_ref(v_a_2060_);
lean_dec(v_h_x3f_2056_);
lean_dec(v_invClause_2055_);
return v_res_2068_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2069_ = lean_box(0);
v___x_2070_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_2071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
lean_ctor_set(v___x_2071_, 1, v___x_2069_);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg(){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg___closed__0);
v___x_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2073_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg___boxed(lean_object* v___y_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0(lean_object* v_00_u03b1_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
lean_object* v___x_2086_; 
v___x_2086_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___boxed(lean_object* v_00_u03b1_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0(v_00_u03b1_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec_ref(v___y_2088_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___lam__0(lean_object* v_____do__lift_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
uint8_t v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2106_ = 0;
v___x_2107_ = l_Lean_SourceInfo_fromRef(v_____do__lift_2097_, v___x_2106_);
v___x_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___lam__0___boxed(lean_object* v_____do__lift_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___lam__0(v_____do__lift_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v_____do__lift_2109_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1_spec__2(lean_object* v_msgData_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v___x_2125_; lean_object* v_env_2126_; lean_object* v___x_2127_; lean_object* v_mctx_2128_; lean_object* v_lctx_2129_; lean_object* v_options_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2125_ = lean_st_ref_get(v___y_2123_);
v_env_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc_ref(v_env_2126_);
lean_dec(v___x_2125_);
v___x_2127_ = lean_st_ref_get(v___y_2121_);
v_mctx_2128_ = lean_ctor_get(v___x_2127_, 0);
lean_inc_ref(v_mctx_2128_);
lean_dec(v___x_2127_);
v_lctx_2129_ = lean_ctor_get(v___y_2120_, 2);
v_options_2130_ = lean_ctor_get(v___y_2122_, 2);
lean_inc_ref(v_options_2130_);
lean_inc_ref(v_lctx_2129_);
v___x_2131_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2131_, 0, v_env_2126_);
lean_ctor_set(v___x_2131_, 1, v_mctx_2128_);
lean_ctor_set(v___x_2131_, 2, v_lctx_2129_);
lean_ctor_set(v___x_2131_, 3, v_options_2130_);
v___x_2132_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
lean_ctor_set(v___x_2132_, 1, v_msgData_2119_);
v___x_2133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1_spec__2(v_msgData_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1___redArg(lean_object* v_msg_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v_ref_2147_; lean_object* v___x_2148_; lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2157_; 
v_ref_2147_ = lean_ctor_get(v___y_2144_, 5);
v___x_2148_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1_spec__2(v_msg_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2151_ = v___x_2148_;
v_isShared_2152_ = v_isSharedCheck_2157_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2148_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2157_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2153_; lean_object* v___x_2155_; 
lean_inc(v_ref_2147_);
v___x_2153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2153_, 0, v_ref_2147_);
lean_ctor_set(v___x_2153_, 1, v_a_2149_);
if (v_isShared_2152_ == 0)
{
lean_ctor_set_tag(v___x_2151_, 1);
lean_ctor_set(v___x_2151_, 0, v___x_2153_);
v___x_2155_ = v___x_2151_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2153_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1___redArg___boxed(lean_object* v_msg_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1___redArg(v_msg_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1___redArg(lean_object* v_ref_2165_, lean_object* v_msg_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
lean_object* v_fileName_2175_; lean_object* v_fileMap_2176_; lean_object* v_options_2177_; lean_object* v_currRecDepth_2178_; lean_object* v_maxRecDepth_2179_; lean_object* v_ref_2180_; lean_object* v_currNamespace_2181_; lean_object* v_openDecls_2182_; lean_object* v_initHeartbeats_2183_; lean_object* v_maxHeartbeats_2184_; lean_object* v_quotContext_2185_; lean_object* v_currMacroScope_2186_; uint8_t v_diag_2187_; lean_object* v_cancelTk_x3f_2188_; uint8_t v_suppressElabErrors_2189_; lean_object* v_inheritedTraceOptions_2190_; lean_object* v_ref_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v_fileName_2175_ = lean_ctor_get(v___y_2172_, 0);
v_fileMap_2176_ = lean_ctor_get(v___y_2172_, 1);
v_options_2177_ = lean_ctor_get(v___y_2172_, 2);
v_currRecDepth_2178_ = lean_ctor_get(v___y_2172_, 3);
v_maxRecDepth_2179_ = lean_ctor_get(v___y_2172_, 4);
v_ref_2180_ = lean_ctor_get(v___y_2172_, 5);
v_currNamespace_2181_ = lean_ctor_get(v___y_2172_, 6);
v_openDecls_2182_ = lean_ctor_get(v___y_2172_, 7);
v_initHeartbeats_2183_ = lean_ctor_get(v___y_2172_, 8);
v_maxHeartbeats_2184_ = lean_ctor_get(v___y_2172_, 9);
v_quotContext_2185_ = lean_ctor_get(v___y_2172_, 10);
v_currMacroScope_2186_ = lean_ctor_get(v___y_2172_, 11);
v_diag_2187_ = lean_ctor_get_uint8(v___y_2172_, sizeof(void*)*14);
v_cancelTk_x3f_2188_ = lean_ctor_get(v___y_2172_, 12);
v_suppressElabErrors_2189_ = lean_ctor_get_uint8(v___y_2172_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2190_ = lean_ctor_get(v___y_2172_, 13);
v_ref_2191_ = l_Lean_replaceRef(v_ref_2165_, v_ref_2180_);
lean_inc_ref(v_inheritedTraceOptions_2190_);
lean_inc(v_cancelTk_x3f_2188_);
lean_inc(v_currMacroScope_2186_);
lean_inc(v_quotContext_2185_);
lean_inc(v_maxHeartbeats_2184_);
lean_inc(v_initHeartbeats_2183_);
lean_inc(v_openDecls_2182_);
lean_inc(v_currNamespace_2181_);
lean_inc(v_maxRecDepth_2179_);
lean_inc(v_currRecDepth_2178_);
lean_inc_ref(v_options_2177_);
lean_inc_ref(v_fileMap_2176_);
lean_inc_ref(v_fileName_2175_);
v___x_2192_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2192_, 0, v_fileName_2175_);
lean_ctor_set(v___x_2192_, 1, v_fileMap_2176_);
lean_ctor_set(v___x_2192_, 2, v_options_2177_);
lean_ctor_set(v___x_2192_, 3, v_currRecDepth_2178_);
lean_ctor_set(v___x_2192_, 4, v_maxRecDepth_2179_);
lean_ctor_set(v___x_2192_, 5, v_ref_2191_);
lean_ctor_set(v___x_2192_, 6, v_currNamespace_2181_);
lean_ctor_set(v___x_2192_, 7, v_openDecls_2182_);
lean_ctor_set(v___x_2192_, 8, v_initHeartbeats_2183_);
lean_ctor_set(v___x_2192_, 9, v_maxHeartbeats_2184_);
lean_ctor_set(v___x_2192_, 10, v_quotContext_2185_);
lean_ctor_set(v___x_2192_, 11, v_currMacroScope_2186_);
lean_ctor_set(v___x_2192_, 12, v_cancelTk_x3f_2188_);
lean_ctor_set(v___x_2192_, 13, v_inheritedTraceOptions_2190_);
lean_ctor_set_uint8(v___x_2192_, sizeof(void*)*14, v_diag_2187_);
lean_ctor_set_uint8(v___x_2192_, sizeof(void*)*14 + 1, v_suppressElabErrors_2189_);
v___x_2193_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1___redArg(v_msg_2166_, v___y_2170_, v___y_2171_, v___x_2192_, v___y_2173_);
lean_dec_ref_known(v___x_2192_, 14);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1___redArg___boxed(lean_object* v_ref_2194_, lean_object* v_msg_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1___redArg(v_ref_2194_, v_msg_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v_ref_2194_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__2___redArg(lean_object* v_as_2205_, size_t v_sz_2206_, size_t v_i_2207_, lean_object* v_b_2208_){
_start:
{
uint8_t v___x_2210_; 
v___x_2210_ = lean_usize_dec_lt(v_i_2207_, v_sz_2206_);
if (v___x_2210_ == 0)
{
lean_object* v___x_2211_; 
v___x_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2211_, 0, v_b_2208_);
return v___x_2211_;
}
else
{
lean_object* v_a_2212_; lean_object* v_ident_2213_; lean_object* v___x_2214_; size_t v___x_2215_; size_t v___x_2216_; 
v_a_2212_ = lean_array_uget_borrowed(v_as_2205_, v_i_2207_);
v_ident_2213_ = lean_ctor_get(v_a_2212_, 0);
lean_inc(v_ident_2213_);
v___x_2214_ = lean_array_push(v_b_2208_, v_ident_2213_);
v___x_2215_ = ((size_t)1ULL);
v___x_2216_ = lean_usize_add(v_i_2207_, v___x_2215_);
v_i_2207_ = v___x_2216_;
v_b_2208_ = v___x_2214_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__2___redArg___boxed(lean_object* v_as_2218_, lean_object* v_sz_2219_, lean_object* v_i_2220_, lean_object* v_b_2221_, lean_object* v___y_2222_){
_start:
{
size_t v_sz_boxed_2223_; size_t v_i_boxed_2224_; lean_object* v_res_2225_; 
v_sz_boxed_2223_ = lean_unbox_usize(v_sz_2219_);
lean_dec(v_sz_2219_);
v_i_boxed_2224_ = lean_unbox_usize(v_i_2220_);
lean_dec(v_i_2220_);
v_res_2225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__2___redArg(v_as_2218_, v_sz_boxed_2223_, v_i_boxed_2224_, v_b_2221_);
lean_dec_ref(v_as_2218_);
return v_res_2225_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__1(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__0));
v___x_2228_ = l_Lean_stringToMessageData(v___x_2227_);
return v___x_2228_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__15(void){
_start:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2256_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__14));
v___x_2257_ = l_Lean_stringToMessageData(v___x_2256_);
return v___x_2257_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__19(void){
_start:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2265_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__18));
v___x_2266_ = l_Lean_stringToMessageData(v___x_2265_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant(lean_object* v_invClause_2267_, lean_object* v_h_x3f_2268_, lean_object* v_xs_2269_, lean_object* v_00_u03b1_2270_, lean_object* v_preS_2271_, lean_object* v_body_2272_, lean_object* v_00_u03c3_2273_, lean_object* v_loopMutVars_2274_, uint8_t v_returnsEarly_2275_, lean_object* v_mi_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_){
_start:
{
lean_object* v___y_2286_; uint8_t v___y_2287_; lean_object* v___y_2288_; lean_object* v___y_2289_; lean_object* v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; uint8_t v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___y_2347_; lean_object* v___y_2348_; uint8_t v___y_2349_; uint8_t v___y_2350_; lean_object* v___y_2351_; lean_object* v___y_2352_; lean_object* v___y_2353_; lean_object* v___y_2354_; lean_object* v___y_2355_; lean_object* v___y_2356_; lean_object* v___y_2357_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2377_; uint8_t v___y_2378_; uint8_t v___y_2379_; lean_object* v___y_2380_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2393_; uint8_t v___y_2394_; lean_object* v_mutTuplePat_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; uint8_t v___y_2463_; lean_object* v_mutBinders_2464_; lean_object* v___y_2465_; lean_object* v___y_2466_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___y_2471_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; uint8_t v___y_2510_; lean_object* v_mutBinders_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; uint8_t v___y_2543_; lean_object* v_invBody_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v_ref_2551_; lean_object* v___y_2552_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v___y_2566_; lean_object* v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; uint8_t v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___x_2649_; uint8_t v___x_2650_; 
v___x_2649_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v_invClause_2267_);
v___x_2650_ = l_Lean_Syntax_isOfKind(v_invClause_2267_, v___x_2649_);
if (v___x_2650_ == 0)
{
v___y_2601_ = v_a_2277_;
v___y_2602_ = v_a_2278_;
v___y_2603_ = v_a_2279_;
v___y_2604_ = v_a_2280_;
v___y_2605_ = v_a_2281_;
v___y_2606_ = v_a_2282_;
v___y_2607_ = v_a_2283_;
goto v___jp_2600_;
}
else
{
lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; uint8_t v___x_2654_; 
v___x_2651_ = lean_unsigned_to_nat(1u);
v___x_2652_ = l_Lean_Syntax_getArg(v_invClause_2267_, v___x_2651_);
v___x_2653_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__13));
lean_inc(v___x_2652_);
v___x_2654_ = l_Lean_Syntax_isOfKind(v___x_2652_, v___x_2653_);
if (v___x_2654_ == 0)
{
lean_dec(v___x_2652_);
v___y_2601_ = v_a_2277_;
v___y_2602_ = v_a_2278_;
v___y_2603_ = v_a_2279_;
v___y_2604_ = v_a_2280_;
v___y_2605_ = v_a_2281_;
v___y_2606_ = v_a_2282_;
v___y_2607_ = v_a_2283_;
goto v___jp_2600_;
}
else
{
lean_object* v___x_2655_; uint8_t v___x_2656_; 
v___x_2655_ = l_Lean_Syntax_getArg(v___x_2652_, v___x_2651_);
lean_dec(v___x_2652_);
lean_inc(v___x_2655_);
v___x_2656_ = l_Lean_Syntax_matchesNull(v___x_2655_, v___x_2651_);
if (v___x_2656_ == 0)
{
lean_dec(v___x_2655_);
v___y_2601_ = v_a_2277_;
v___y_2602_ = v_a_2278_;
v___y_2603_ = v_a_2279_;
v___y_2604_ = v_a_2280_;
v___y_2605_ = v_a_2281_;
v___y_2606_ = v_a_2282_;
v___y_2607_ = v_a_2283_;
goto v___jp_2600_;
}
else
{
lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; uint8_t v___x_2660_; 
v___x_2657_ = lean_unsigned_to_nat(0u);
v___x_2658_ = l_Lean_Syntax_getArg(v___x_2655_, v___x_2657_);
lean_dec(v___x_2655_);
v___x_2659_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__17));
lean_inc(v___x_2658_);
v___x_2660_ = l_Lean_Syntax_isOfKind(v___x_2658_, v___x_2659_);
if (v___x_2660_ == 0)
{
lean_dec(v___x_2658_);
v___y_2601_ = v_a_2277_;
v___y_2602_ = v_a_2278_;
v___y_2603_ = v_a_2279_;
v___y_2604_ = v_a_2280_;
v___y_2605_ = v_a_2281_;
v___y_2606_ = v_a_2282_;
v___y_2607_ = v_a_2283_;
goto v___jp_2600_;
}
else
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2671_; 
lean_dec_ref(v_mi_2276_);
lean_dec_ref(v_00_u03c3_2273_);
lean_dec_ref(v_body_2272_);
lean_dec_ref(v_preS_2271_);
lean_dec_ref(v_00_u03b1_2270_);
lean_dec_ref(v_xs_2269_);
lean_dec(v_invClause_2267_);
v___x_2661_ = l_Lean_Syntax_getArg(v___x_2658_, v___x_2651_);
lean_dec(v___x_2658_);
v___x_2662_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__19, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__19_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__19);
v___x_2663_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1___redArg(v___x_2661_, v___x_2662_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
lean_dec(v___x_2661_);
v_a_2664_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2666_ = v___x_2663_;
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_dec(v___x_2663_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2669_; 
if (v_isShared_2667_ == 0)
{
v___x_2669_ = v___x_2666_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_a_2664_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
}
}
}
v___jp_2285_:
{
lean_object* v___x_2300_; 
v___x_2300_ = l_Lean_Elab_Term_exprToSyntax(v_xs_2269_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v_a_2301_; lean_object* v___x_2302_; 
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
lean_inc(v_a_2301_);
lean_dec_ref_known(v___x_2300_, 1);
v___x_2302_ = l_Lean_Elab_Term_exprToSyntax(v_preS_2271_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v___x_2304_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
lean_dec_ref_known(v___x_2302_, 1);
v___x_2304_ = l_Lean_Elab_Term_exprToSyntax(v_body_2272_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_a_2305_; lean_object* v_ref_2306_; lean_object* v_m_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_a_2305_);
lean_dec_ref_known(v___x_2304_, 1);
v_ref_2306_ = lean_ctor_get(v___y_2298_, 5);
v_m_2307_ = lean_ctor_get(v_mi_2276_, 0);
lean_inc_ref(v_m_2307_);
lean_dec_ref(v_mi_2276_);
v___x_2308_ = l_Lean_SourceInfo_fromRef(v_ref_2306_, v___y_2287_);
lean_inc(v___x_2308_);
v___x_2309_ = l_Lean_Syntax_node4(v___x_2308_, v___y_2291_, v_a_2301_, v_a_2303_, v_a_2305_, v___y_2286_);
v___x_2310_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__0));
lean_inc_ref(v___y_2290_);
lean_inc_ref(v___y_2292_);
lean_inc_ref(v___y_2288_);
v___x_2311_ = l_Lean_Name_mkStr4(v___y_2288_, v___y_2292_, v___y_2290_, v___x_2310_);
lean_inc(v___y_2289_);
v___x_2312_ = l_Lean_mkIdent(v___y_2289_);
v___x_2313_ = l_Lean_Syntax_node2(v___x_2308_, v___x_2311_, v___x_2312_, v___x_2309_);
v___x_2314_ = l_Lean_Expr_app___override(v_m_2307_, v_00_u03c3_2273_);
v___x_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2314_);
v___x_2316_ = lean_box(0);
v___x_2317_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_2313_, v___x_2315_, v___y_2293_, v___y_2293_, v___x_2316_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
return v___x_2317_;
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_dec(v_a_2303_);
lean_dec(v_a_2301_);
lean_dec(v___y_2291_);
lean_dec(v___y_2286_);
lean_dec_ref(v_mi_2276_);
lean_dec_ref(v_00_u03c3_2273_);
v_a_2318_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2304_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2304_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
else
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2333_; 
lean_dec(v_a_2301_);
lean_dec(v___y_2291_);
lean_dec(v___y_2286_);
lean_dec_ref(v_mi_2276_);
lean_dec_ref(v_00_u03c3_2273_);
lean_dec_ref(v_body_2272_);
v_a_2326_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2328_ = v___x_2302_;
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2302_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2331_; 
if (v_isShared_2329_ == 0)
{
v___x_2331_ = v___x_2328_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2326_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
else
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
lean_dec(v___y_2291_);
lean_dec(v___y_2286_);
lean_dec_ref(v_mi_2276_);
lean_dec_ref(v_00_u03c3_2273_);
lean_dec_ref(v_body_2272_);
lean_dec_ref(v_preS_2271_);
v_a_2334_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2300_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2300_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
v___jp_2342_:
{
lean_object* v___x_2358_; lean_object* v_env_2359_; uint8_t v___x_2360_; 
v___x_2358_ = lean_st_ref_get(v___y_2352_);
v_env_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc_ref(v_env_2359_);
lean_dec(v___x_2358_);
lean_inc(v___y_2357_);
v___x_2360_ = l_Lean_Environment_contains(v_env_2359_, v___y_2357_, v___y_2349_);
if (v___x_2360_ == 0)
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
lean_dec(v___y_2354_);
lean_dec(v___y_2343_);
lean_dec_ref(v_mi_2276_);
lean_dec_ref(v_00_u03c3_2273_);
lean_dec_ref(v_body_2272_);
lean_dec_ref(v_preS_2271_);
lean_dec_ref(v_xs_2269_);
v___x_2361_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__1, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__1);
v___x_2362_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1___redArg(v_invClause_2267_, v___x_2361_, v___y_2348_, v___y_2351_, v___y_2353_, v___y_2356_, v___y_2346_, v___y_2345_, v___y_2352_);
lean_dec(v_invClause_2267_);
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2362_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2362_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2363_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
else
{
lean_dec(v_invClause_2267_);
v___y_2286_ = v___y_2343_;
v___y_2287_ = v___y_2350_;
v___y_2288_ = v___y_2344_;
v___y_2289_ = v___y_2357_;
v___y_2290_ = v___y_2347_;
v___y_2291_ = v___y_2354_;
v___y_2292_ = v___y_2355_;
v___y_2293_ = v___y_2349_;
v___y_2294_ = v___y_2351_;
v___y_2295_ = v___y_2353_;
v___y_2296_ = v___y_2356_;
v___y_2297_ = v___y_2346_;
v___y_2298_ = v___y_2345_;
v___y_2299_ = v___y_2352_;
goto v___jp_2285_;
}
}
v___jp_2371_:
{
lean_object* v___x_2386_; 
v___x_2386_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__4));
v___y_2343_ = v___y_2372_;
v___y_2344_ = v___y_2373_;
v___y_2345_ = v___y_2374_;
v___y_2346_ = v___y_2375_;
v___y_2347_ = v___y_2376_;
v___y_2348_ = v___y_2377_;
v___y_2349_ = v___y_2378_;
v___y_2350_ = v___y_2379_;
v___y_2351_ = v___y_2380_;
v___y_2352_ = v___y_2381_;
v___y_2353_ = v___y_2382_;
v___y_2354_ = v___y_2383_;
v___y_2355_ = v___y_2385_;
v___y_2356_ = v___y_2384_;
v___y_2357_ = v___x_2386_;
goto v___jp_2342_;
}
v___jp_2387_:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2403_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17));
v___x_2404_ = l_Lean_Core_mkFreshUserName(v___x_2403_, v___y_2401_, v___y_2402_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v_a_2405_; lean_object* v_ref_2406_; lean_object* v___x_2407_; lean_object* v_a_2408_; uint8_t v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_a_2405_);
lean_dec_ref_known(v___x_2404_, 1);
v_ref_2406_ = lean_ctor_get(v___y_2401_, 5);
v___x_2407_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___lam__0(v_ref_2406_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc_n(v_a_2408_, 17);
lean_dec_ref(v___x_2407_);
v___x_2409_ = 0;
v___x_2410_ = l_Lean_mkIdentFrom(v_invClause_2267_, v_a_2405_, v___x_2409_);
v___x_2411_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__5));
lean_inc_ref_n(v___y_2391_, 5);
lean_inc_ref_n(v___y_2393_, 5);
lean_inc_ref_n(v___y_2389_, 5);
v___x_2412_ = l_Lean_Name_mkStr4(v___y_2389_, v___y_2393_, v___y_2391_, v___x_2411_);
v___x_2413_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2413_, 0, v_a_2408_);
lean_ctor_set(v___x_2413_, 1, v___x_2411_);
v___x_2414_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_2415_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_2416_ = l_Array_append___redArg(v___x_2415_, v___y_2388_);
lean_dec_ref(v___y_2388_);
lean_inc(v___x_2410_);
v___x_2417_ = lean_array_push(v___x_2416_, v___x_2410_);
v___x_2418_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2418_, 0, v_a_2408_);
lean_ctor_set(v___x_2418_, 1, v___x_2414_);
lean_ctor_set(v___x_2418_, 2, v___x_2417_);
v___x_2419_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2419_, 0, v_a_2408_);
lean_ctor_set(v___x_2419_, 1, v___x_2414_);
lean_ctor_set(v___x_2419_, 2, v___x_2415_);
v___x_2420_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_2421_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2421_, 0, v_a_2408_);
lean_ctor_set(v___x_2421_, 1, v___x_2420_);
v___x_2422_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
v___x_2423_ = l_Lean_Name_mkStr4(v___y_2389_, v___y_2393_, v___y_2391_, v___x_2422_);
v___x_2424_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2424_, 0, v_a_2408_);
lean_ctor_set(v___x_2424_, 1, v___x_2422_);
v___x_2425_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31));
v___x_2426_ = l_Lean_Name_mkStr4(v___y_2389_, v___y_2393_, v___y_2391_, v___x_2425_);
lean_inc_ref_n(v___x_2419_, 3);
v___x_2427_ = l_Lean_Syntax_node2(v_a_2408_, v___x_2426_, v___x_2419_, v___x_2410_);
v___x_2428_ = l_Lean_Syntax_node1(v_a_2408_, v___x_2414_, v___x_2427_);
v___x_2429_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_2430_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2430_, 0, v_a_2408_);
lean_ctor_set(v___x_2430_, 1, v___x_2429_);
v___x_2431_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40));
v___x_2432_ = l_Lean_Name_mkStr4(v___y_2389_, v___y_2393_, v___y_2391_, v___x_2431_);
v___x_2433_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41));
v___x_2434_ = l_Lean_Name_mkStr4(v___y_2389_, v___y_2393_, v___y_2391_, v___x_2433_);
v___x_2435_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_2436_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2436_, 0, v_a_2408_);
lean_ctor_set(v___x_2436_, 1, v___x_2435_);
v___x_2437_ = l_Lean_Syntax_node1(v_a_2408_, v___x_2414_, v_mutTuplePat_2395_);
v___x_2438_ = l_Lean_Syntax_node1(v_a_2408_, v___x_2414_, v___x_2437_);
lean_inc_ref(v___x_2421_);
v___x_2439_ = l_Lean_Syntax_node4(v_a_2408_, v___x_2434_, v___x_2436_, v___x_2438_, v___x_2421_, v___y_2390_);
v___x_2440_ = l_Lean_Syntax_node1(v_a_2408_, v___x_2414_, v___x_2439_);
v___x_2441_ = l_Lean_Syntax_node1(v_a_2408_, v___x_2432_, v___x_2440_);
v___x_2442_ = l_Lean_Syntax_node6(v_a_2408_, v___x_2423_, v___x_2424_, v___x_2419_, v___x_2419_, v___x_2428_, v___x_2430_, v___x_2441_);
lean_inc(v___y_2392_);
v___x_2443_ = l_Lean_Syntax_node4(v_a_2408_, v___y_2392_, v___x_2418_, v___x_2419_, v___x_2421_, v___x_2442_);
v___x_2444_ = l_Lean_Syntax_node2(v_a_2408_, v___x_2412_, v___x_2413_, v___x_2443_);
if (lean_obj_tag(v_h_x3f_2268_) == 0)
{
v___y_2372_ = v___x_2444_;
v___y_2373_ = v___y_2389_;
v___y_2374_ = v___y_2401_;
v___y_2375_ = v___y_2400_;
v___y_2376_ = v___y_2391_;
v___y_2377_ = v___y_2396_;
v___y_2378_ = v___y_2394_;
v___y_2379_ = v___x_2409_;
v___y_2380_ = v___y_2397_;
v___y_2381_ = v___y_2402_;
v___y_2382_ = v___y_2398_;
v___y_2383_ = v___x_2414_;
v___y_2384_ = v___y_2399_;
v___y_2385_ = v___y_2393_;
goto v___jp_2371_;
}
else
{
if (v___y_2394_ == 0)
{
v___y_2372_ = v___x_2444_;
v___y_2373_ = v___y_2389_;
v___y_2374_ = v___y_2401_;
v___y_2375_ = v___y_2400_;
v___y_2376_ = v___y_2391_;
v___y_2377_ = v___y_2396_;
v___y_2378_ = v___y_2394_;
v___y_2379_ = v___x_2409_;
v___y_2380_ = v___y_2397_;
v___y_2381_ = v___y_2402_;
v___y_2382_ = v___y_2398_;
v___y_2383_ = v___x_2414_;
v___y_2384_ = v___y_2399_;
v___y_2385_ = v___y_2393_;
goto v___jp_2371_;
}
else
{
lean_object* v___x_2445_; 
v___x_2445_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__8));
v___y_2343_ = v___x_2444_;
v___y_2344_ = v___y_2389_;
v___y_2345_ = v___y_2401_;
v___y_2346_ = v___y_2400_;
v___y_2347_ = v___y_2391_;
v___y_2348_ = v___y_2396_;
v___y_2349_ = v___y_2394_;
v___y_2350_ = v___x_2409_;
v___y_2351_ = v___y_2397_;
v___y_2352_ = v___y_2402_;
v___y_2353_ = v___y_2398_;
v___y_2354_ = v___x_2414_;
v___y_2355_ = v___y_2393_;
v___y_2356_ = v___y_2399_;
v___y_2357_ = v___x_2445_;
goto v___jp_2342_;
}
}
}
else
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
lean_dec(v_mutTuplePat_2395_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2388_);
lean_dec_ref(v_mi_2276_);
lean_dec_ref(v_00_u03c3_2273_);
lean_dec_ref(v_body_2272_);
lean_dec_ref(v_preS_2271_);
lean_dec_ref(v_xs_2269_);
lean_dec(v_invClause_2267_);
v_a_2446_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2448_ = v___x_2404_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2404_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2451_; 
if (v_isShared_2449_ == 0)
{
v___x_2451_ = v___x_2448_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2446_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
v___jp_2454_:
{
lean_object* v___x_2472_; uint8_t v___x_2473_; 
v___x_2472_ = lean_array_get_size(v_mutBinders_2464_);
v___x_2473_ = lean_nat_dec_eq(v___x_2472_, v___y_2460_);
if (v___x_2473_ == 0)
{
uint8_t v___x_2474_; 
v___x_2474_ = lean_nat_dec_eq(v___x_2472_, v___y_2457_);
if (v___x_2474_ == 0)
{
lean_object* v_ref_2475_; lean_object* v___x_2476_; lean_object* v_a_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
lean_dec(v___y_2460_);
v_ref_2475_ = lean_ctor_get(v___y_2470_, 5);
v___x_2476_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___lam__0(v_ref_2475_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc_n(v_a_2477_, 4);
lean_dec_ref(v___x_2476_);
v___x_2478_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__9));
lean_inc_ref(v___y_2459_);
lean_inc_ref(v___y_2462_);
lean_inc_ref(v___y_2456_);
v___x_2479_ = l_Lean_Name_mkStr4(v___y_2456_, v___y_2462_, v___y_2459_, v___x_2478_);
v___x_2480_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__10));
v___x_2481_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2481_, 0, v_a_2477_);
lean_ctor_set(v___x_2481_, 1, v___x_2480_);
v___x_2482_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_2483_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_2484_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__5));
v___x_2485_ = l_Lean_Syntax_SepArray_ofElems(v___x_2484_, v_mutBinders_2464_);
lean_dec_ref(v_mutBinders_2464_);
v___x_2486_ = l_Array_append___redArg(v___x_2483_, v___x_2485_);
lean_dec_ref(v___x_2485_);
v___x_2487_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2487_, 0, v_a_2477_);
lean_ctor_set(v___x_2487_, 1, v___x_2482_);
lean_ctor_set(v___x_2487_, 2, v___x_2486_);
v___x_2488_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__11));
v___x_2489_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2489_, 0, v_a_2477_);
lean_ctor_set(v___x_2489_, 1, v___x_2488_);
v___x_2490_ = l_Lean_Syntax_node3(v_a_2477_, v___x_2479_, v___x_2481_, v___x_2487_, v___x_2489_);
v___y_2388_ = v___y_2455_;
v___y_2389_ = v___y_2456_;
v___y_2390_ = v___y_2458_;
v___y_2391_ = v___y_2459_;
v___y_2392_ = v___y_2461_;
v___y_2393_ = v___y_2462_;
v___y_2394_ = v___y_2463_;
v_mutTuplePat_2395_ = v___x_2490_;
v___y_2396_ = v___y_2465_;
v___y_2397_ = v___y_2466_;
v___y_2398_ = v___y_2467_;
v___y_2399_ = v___y_2468_;
v___y_2400_ = v___y_2469_;
v___y_2401_ = v___y_2470_;
v___y_2402_ = v___y_2471_;
goto v___jp_2387_;
}
else
{
lean_object* v___x_2491_; 
v___x_2491_ = lean_array_fget(v_mutBinders_2464_, v___y_2460_);
lean_dec(v___y_2460_);
lean_dec_ref(v_mutBinders_2464_);
v___y_2388_ = v___y_2455_;
v___y_2389_ = v___y_2456_;
v___y_2390_ = v___y_2458_;
v___y_2391_ = v___y_2459_;
v___y_2392_ = v___y_2461_;
v___y_2393_ = v___y_2462_;
v___y_2394_ = v___y_2463_;
v_mutTuplePat_2395_ = v___x_2491_;
v___y_2396_ = v___y_2465_;
v___y_2397_ = v___y_2466_;
v___y_2398_ = v___y_2467_;
v___y_2399_ = v___y_2468_;
v___y_2400_ = v___y_2469_;
v___y_2401_ = v___y_2470_;
v___y_2402_ = v___y_2471_;
goto v___jp_2387_;
}
}
else
{
lean_object* v_ref_2492_; lean_object* v___x_2493_; lean_object* v_a_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
lean_dec_ref(v_mutBinders_2464_);
lean_dec(v___y_2460_);
v_ref_2492_ = lean_ctor_get(v___y_2470_, 5);
v___x_2493_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___lam__0(v_ref_2492_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
v_a_2494_ = lean_ctor_get(v___x_2493_, 0);
lean_inc_n(v_a_2494_, 2);
lean_dec_ref(v___x_2493_);
v___x_2495_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__14));
lean_inc_ref(v___y_2459_);
lean_inc_ref(v___y_2462_);
lean_inc_ref(v___y_2456_);
v___x_2496_ = l_Lean_Name_mkStr4(v___y_2456_, v___y_2462_, v___y_2459_, v___x_2495_);
v___x_2497_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15));
v___x_2498_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2498_, 0, v_a_2494_);
lean_ctor_set(v___x_2498_, 1, v___x_2497_);
v___x_2499_ = l_Lean_Syntax_node1(v_a_2494_, v___x_2496_, v___x_2498_);
v___y_2388_ = v___y_2455_;
v___y_2389_ = v___y_2456_;
v___y_2390_ = v___y_2458_;
v___y_2391_ = v___y_2459_;
v___y_2392_ = v___y_2461_;
v___y_2393_ = v___y_2462_;
v___y_2394_ = v___y_2463_;
v_mutTuplePat_2395_ = v___x_2499_;
v___y_2396_ = v___y_2465_;
v___y_2397_ = v___y_2466_;
v___y_2398_ = v___y_2467_;
v___y_2399_ = v___y_2468_;
v___y_2400_ = v___y_2469_;
v___y_2401_ = v___y_2470_;
v___y_2402_ = v___y_2471_;
goto v___jp_2387_;
}
}
v___jp_2500_:
{
size_t v_sz_2519_; size_t v___x_2520_; lean_object* v___x_2521_; 
v_sz_2519_ = lean_array_size(v_loopMutVars_2274_);
v___x_2520_ = ((size_t)0ULL);
v___x_2521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__2___redArg(v_loopMutVars_2274_, v_sz_2519_, v___x_2520_, v_mutBinders_2511_);
if (lean_obj_tag(v___x_2521_) == 0)
{
if (v_returnsEarly_2275_ == 0)
{
lean_object* v_a_2522_; 
lean_dec(v___y_2502_);
v_a_2522_ = lean_ctor_get(v___x_2521_, 0);
lean_inc(v_a_2522_);
lean_dec_ref_known(v___x_2521_, 1);
v___y_2455_ = v___y_2501_;
v___y_2456_ = v___y_2503_;
v___y_2457_ = v___y_2504_;
v___y_2458_ = v___y_2505_;
v___y_2459_ = v___y_2507_;
v___y_2460_ = v___y_2506_;
v___y_2461_ = v___y_2508_;
v___y_2462_ = v___y_2509_;
v___y_2463_ = v___y_2510_;
v_mutBinders_2464_ = v_a_2522_;
v___y_2465_ = v___y_2512_;
v___y_2466_ = v___y_2513_;
v___y_2467_ = v___y_2514_;
v___y_2468_ = v___y_2515_;
v___y_2469_ = v___y_2516_;
v___y_2470_ = v___y_2517_;
v___y_2471_ = v___y_2518_;
goto v___jp_2454_;
}
else
{
lean_object* v_a_2523_; lean_object* v___x_2524_; uint8_t v___x_2525_; 
v_a_2523_ = lean_ctor_get(v___x_2521_, 0);
lean_inc(v_a_2523_);
lean_dec_ref_known(v___x_2521_, 1);
v___x_2524_ = lean_array_get_size(v_loopMutVars_2274_);
v___x_2525_ = lean_nat_dec_eq(v___x_2524_, v___y_2506_);
if (v___x_2525_ == 0)
{
lean_dec(v___y_2502_);
v___y_2455_ = v___y_2501_;
v___y_2456_ = v___y_2503_;
v___y_2457_ = v___y_2504_;
v___y_2458_ = v___y_2505_;
v___y_2459_ = v___y_2507_;
v___y_2460_ = v___y_2506_;
v___y_2461_ = v___y_2508_;
v___y_2462_ = v___y_2509_;
v___y_2463_ = v___y_2510_;
v_mutBinders_2464_ = v_a_2523_;
v___y_2465_ = v___y_2512_;
v___y_2466_ = v___y_2513_;
v___y_2467_ = v___y_2514_;
v___y_2468_ = v___y_2515_;
v___y_2469_ = v___y_2516_;
v___y_2470_ = v___y_2517_;
v___y_2471_ = v___y_2518_;
goto v___jp_2454_;
}
else
{
lean_object* v___x_2526_; 
v___x_2526_ = lean_array_push(v_a_2523_, v___y_2502_);
v___y_2455_ = v___y_2501_;
v___y_2456_ = v___y_2503_;
v___y_2457_ = v___y_2504_;
v___y_2458_ = v___y_2505_;
v___y_2459_ = v___y_2507_;
v___y_2460_ = v___y_2506_;
v___y_2461_ = v___y_2508_;
v___y_2462_ = v___y_2509_;
v___y_2463_ = v___y_2510_;
v_mutBinders_2464_ = v___x_2526_;
v___y_2465_ = v___y_2512_;
v___y_2466_ = v___y_2513_;
v___y_2467_ = v___y_2514_;
v___y_2468_ = v___y_2515_;
v___y_2469_ = v___y_2516_;
v___y_2470_ = v___y_2517_;
v___y_2471_ = v___y_2518_;
goto v___jp_2454_;
}
}
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
lean_dec(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec_ref(v_mi_2276_);
lean_dec_ref(v_00_u03c3_2273_);
lean_dec_ref(v_body_2272_);
lean_dec_ref(v_preS_2271_);
lean_dec_ref(v_xs_2269_);
lean_dec(v_invClause_2267_);
v_a_2527_ = lean_ctor_get(v___x_2521_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2521_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2529_ = v___x_2521_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2521_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2532_; 
if (v_isShared_2530_ == 0)
{
v___x_2532_ = v___x_2529_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_a_2527_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
}
v___jp_2535_:
{
lean_object* v___x_2553_; lean_object* v_a_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2553_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___lam__0(v_ref_2551_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2552_);
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc_n(v_a_2554_, 2);
lean_dec_ref(v___x_2553_);
v___x_2555_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__14));
lean_inc_ref(v___y_2540_);
lean_inc_ref(v___y_2542_);
lean_inc_ref(v___y_2537_);
v___x_2556_ = l_Lean_Name_mkStr4(v___y_2537_, v___y_2542_, v___y_2540_, v___x_2555_);
v___x_2557_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15));
v___x_2558_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2558_, 0, v_a_2554_);
lean_ctor_set(v___x_2558_, 1, v___x_2557_);
v___x_2559_ = l_Lean_Syntax_node1(v_a_2554_, v___x_2556_, v___x_2558_);
v___x_2560_ = lean_mk_empty_array_with_capacity(v___y_2539_);
if (v_returnsEarly_2275_ == 0)
{
v___y_2501_ = v___y_2536_;
v___y_2502_ = v___x_2559_;
v___y_2503_ = v___y_2537_;
v___y_2504_ = v___y_2538_;
v___y_2505_ = v_invBody_2544_;
v___y_2506_ = v___y_2539_;
v___y_2507_ = v___y_2540_;
v___y_2508_ = v___y_2541_;
v___y_2509_ = v___y_2542_;
v___y_2510_ = v___y_2543_;
v_mutBinders_2511_ = v___x_2560_;
v___y_2512_ = v___y_2545_;
v___y_2513_ = v___y_2546_;
v___y_2514_ = v___y_2547_;
v___y_2515_ = v___y_2548_;
v___y_2516_ = v___y_2549_;
v___y_2517_ = v___y_2550_;
v___y_2518_ = v___y_2552_;
goto v___jp_2500_;
}
else
{
lean_object* v___x_2561_; 
lean_inc(v___x_2559_);
v___x_2561_ = lean_array_push(v___x_2560_, v___x_2559_);
v___y_2501_ = v___y_2536_;
v___y_2502_ = v___x_2559_;
v___y_2503_ = v___y_2537_;
v___y_2504_ = v___y_2538_;
v___y_2505_ = v_invBody_2544_;
v___y_2506_ = v___y_2539_;
v___y_2507_ = v___y_2540_;
v___y_2508_ = v___y_2541_;
v___y_2509_ = v___y_2542_;
v___y_2510_ = v___y_2543_;
v_mutBinders_2511_ = v___x_2561_;
v___y_2512_ = v___y_2545_;
v___y_2513_ = v___y_2546_;
v___y_2514_ = v___y_2547_;
v___y_2515_ = v___y_2548_;
v___y_2516_ = v___y_2549_;
v___y_2517_ = v___y_2550_;
v___y_2518_ = v___y_2552_;
goto v___jp_2500_;
}
}
v___jp_2562_:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; uint8_t v___x_2584_; 
lean_inc(v___y_2567_);
lean_inc(v___y_2569_);
v___x_2580_ = l_Array_extract___redArg(v___y_2564_, v___y_2569_, v___y_2567_);
v___x_2581_ = lean_array_get_size(v___y_2564_);
v___x_2582_ = l_Array_extract___redArg(v___y_2564_, v___y_2567_, v___x_2581_);
lean_dec_ref(v___y_2564_);
v___x_2583_ = lean_array_get_size(v___x_2582_);
v___x_2584_ = lean_nat_dec_eq(v___x_2583_, v___y_2569_);
if (v___x_2584_ == 0)
{
lean_object* v_ref_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v_ref_2585_ = lean_ctor_get(v___y_2578_, 5);
v___x_2586_ = l_Lean_SourceInfo_fromRef(v_ref_2585_, v___x_2584_);
v___x_2587_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__5));
lean_inc_ref(v___y_2568_);
lean_inc_ref(v___y_2571_);
lean_inc_ref(v___y_2563_);
v___x_2588_ = l_Lean_Name_mkStr4(v___y_2563_, v___y_2571_, v___y_2568_, v___x_2587_);
lean_inc_n(v___x_2586_, 5);
v___x_2589_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2586_);
lean_ctor_set(v___x_2589_, 1, v___x_2587_);
v___x_2590_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_2591_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_2592_ = l_Array_append___redArg(v___x_2591_, v___x_2582_);
lean_dec_ref(v___x_2582_);
v___x_2593_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2586_);
lean_ctor_set(v___x_2593_, 1, v___x_2590_);
lean_ctor_set(v___x_2593_, 2, v___x_2592_);
v___x_2594_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2586_);
lean_ctor_set(v___x_2594_, 1, v___x_2590_);
lean_ctor_set(v___x_2594_, 2, v___x_2591_);
v___x_2595_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_2596_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2586_);
lean_ctor_set(v___x_2596_, 1, v___x_2595_);
lean_inc(v___y_2570_);
v___x_2597_ = l_Lean_Syntax_node4(v___x_2586_, v___y_2570_, v___x_2593_, v___x_2594_, v___x_2596_, v___y_2565_);
v___x_2598_ = l_Lean_Syntax_node2(v___x_2586_, v___x_2588_, v___x_2589_, v___x_2597_);
v___y_2536_ = v___x_2580_;
v___y_2537_ = v___y_2563_;
v___y_2538_ = v___y_2566_;
v___y_2539_ = v___y_2569_;
v___y_2540_ = v___y_2568_;
v___y_2541_ = v___y_2570_;
v___y_2542_ = v___y_2571_;
v___y_2543_ = v___y_2572_;
v_invBody_2544_ = v___x_2598_;
v___y_2545_ = v___y_2573_;
v___y_2546_ = v___y_2574_;
v___y_2547_ = v___y_2575_;
v___y_2548_ = v___y_2576_;
v___y_2549_ = v___y_2577_;
v___y_2550_ = v___y_2578_;
v_ref_2551_ = v_ref_2585_;
v___y_2552_ = v___y_2579_;
goto v___jp_2535_;
}
else
{
lean_object* v_ref_2599_; 
lean_dec_ref(v___x_2582_);
v_ref_2599_ = lean_ctor_get(v___y_2578_, 5);
v___y_2536_ = v___x_2580_;
v___y_2537_ = v___y_2563_;
v___y_2538_ = v___y_2566_;
v___y_2539_ = v___y_2569_;
v___y_2540_ = v___y_2568_;
v___y_2541_ = v___y_2570_;
v___y_2542_ = v___y_2571_;
v___y_2543_ = v___y_2572_;
v_invBody_2544_ = v___y_2565_;
v___y_2545_ = v___y_2573_;
v___y_2546_ = v___y_2574_;
v___y_2547_ = v___y_2575_;
v___y_2548_ = v___y_2576_;
v___y_2549_ = v___y_2577_;
v___y_2550_ = v___y_2578_;
v_ref_2551_ = v_ref_2599_;
v___y_2552_ = v___y_2579_;
goto v___jp_2535_;
}
}
v___jp_2600_:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; uint8_t v___x_2612_; 
v___x_2608_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0));
v___x_2609_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1));
v___x_2610_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2));
v___x_2611_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v_invClause_2267_);
v___x_2612_ = l_Lean_Syntax_isOfKind(v_invClause_2267_, v___x_2611_);
if (v___x_2612_ == 0)
{
lean_object* v___x_2613_; 
lean_dec_ref(v_mi_2276_);
lean_dec_ref(v_00_u03c3_2273_);
lean_dec_ref(v_body_2272_);
lean_dec_ref(v_preS_2271_);
lean_dec_ref(v_00_u03b1_2270_);
lean_dec_ref(v_xs_2269_);
lean_dec(v_invClause_2267_);
v___x_2613_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v___x_2613_;
}
else
{
lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; uint8_t v___x_2617_; 
v___x_2614_ = lean_unsigned_to_nat(1u);
v___x_2615_ = l_Lean_Syntax_getArg(v_invClause_2267_, v___x_2614_);
v___x_2616_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__13));
lean_inc(v___x_2615_);
v___x_2617_ = l_Lean_Syntax_isOfKind(v___x_2615_, v___x_2616_);
if (v___x_2617_ == 0)
{
lean_object* v___x_2618_; 
lean_dec(v___x_2615_);
lean_dec_ref(v_mi_2276_);
lean_dec_ref(v_00_u03c3_2273_);
lean_dec_ref(v_body_2272_);
lean_dec_ref(v_preS_2271_);
lean_dec_ref(v_00_u03b1_2270_);
lean_dec_ref(v_xs_2269_);
lean_dec(v_invClause_2267_);
v___x_2618_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v___x_2618_;
}
else
{
lean_object* v___x_2619_; lean_object* v___x_2620_; uint8_t v___x_2621_; 
v___x_2619_ = lean_unsigned_to_nat(0u);
v___x_2620_ = l_Lean_Syntax_getArg(v___x_2615_, v___x_2614_);
v___x_2621_ = l_Lean_Syntax_matchesNull(v___x_2620_, v___x_2619_);
if (v___x_2621_ == 0)
{
lean_object* v___x_2622_; 
lean_dec(v___x_2615_);
lean_dec_ref(v_mi_2276_);
lean_dec_ref(v_00_u03c3_2273_);
lean_dec_ref(v_body_2272_);
lean_dec_ref(v_preS_2271_);
lean_dec_ref(v_00_u03b1_2270_);
lean_dec_ref(v_xs_2269_);
lean_dec(v_invClause_2267_);
v___x_2622_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v___x_2622_;
}
else
{
lean_object* v___x_2623_; 
lean_inc_ref(v_mi_2276_);
lean_inc_ref(v_xs_2269_);
v___x_2623_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg(v_invClause_2267_, v_h_x3f_2268_, v_xs_2269_, v_00_u03b1_2270_, v_mi_2276_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v_invBody_2627_; lean_object* v_binders_2628_; lean_object* v___x_2629_; uint8_t v___x_2630_; 
lean_dec_ref_known(v___x_2623_, 1);
v___x_2624_ = l_Lean_Syntax_getArg(v___x_2615_, v___x_2619_);
v___x_2625_ = lean_unsigned_to_nat(2u);
v___x_2626_ = lean_unsigned_to_nat(3u);
v_invBody_2627_ = l_Lean_Syntax_getArg(v___x_2615_, v___x_2626_);
lean_dec(v___x_2615_);
v_binders_2628_ = l_Lean_Syntax_getArgs(v___x_2624_);
lean_dec(v___x_2624_);
v___x_2629_ = lean_array_get_size(v_binders_2628_);
v___x_2630_ = lean_nat_dec_le(v___x_2625_, v___x_2629_);
if (v___x_2630_ == 0)
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
lean_dec_ref(v_binders_2628_);
lean_dec(v_invBody_2627_);
lean_dec_ref(v_mi_2276_);
lean_dec_ref(v_00_u03c3_2273_);
lean_dec_ref(v_body_2272_);
lean_dec_ref(v_preS_2271_);
lean_dec_ref(v_xs_2269_);
v___x_2631_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__15, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__15_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___closed__15);
v___x_2632_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1___redArg(v_invClause_2267_, v___x_2631_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
lean_dec(v_invClause_2267_);
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2632_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2632_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2633_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
else
{
v___y_2563_ = v___x_2608_;
v___y_2564_ = v_binders_2628_;
v___y_2565_ = v_invBody_2627_;
v___y_2566_ = v___x_2614_;
v___y_2567_ = v___x_2625_;
v___y_2568_ = v___x_2610_;
v___y_2569_ = v___x_2619_;
v___y_2570_ = v___x_2616_;
v___y_2571_ = v___x_2609_;
v___y_2572_ = v___x_2621_;
v___y_2573_ = v___y_2601_;
v___y_2574_ = v___y_2602_;
v___y_2575_ = v___y_2603_;
v___y_2576_ = v___y_2604_;
v___y_2577_ = v___y_2605_;
v___y_2578_ = v___y_2606_;
v___y_2579_ = v___y_2607_;
goto v___jp_2562_;
}
}
else
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
lean_dec(v___x_2615_);
lean_dec_ref(v_mi_2276_);
lean_dec_ref(v_00_u03c3_2273_);
lean_dec_ref(v_body_2272_);
lean_dec_ref(v_preS_2271_);
lean_dec_ref(v_xs_2269_);
lean_dec(v_invClause_2267_);
v_a_2641_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v___x_2623_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2623_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2641_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant___boxed(lean_object** _args){
lean_object* v_invClause_2672_ = _args[0];
lean_object* v_h_x3f_2673_ = _args[1];
lean_object* v_xs_2674_ = _args[2];
lean_object* v_00_u03b1_2675_ = _args[3];
lean_object* v_preS_2676_ = _args[4];
lean_object* v_body_2677_ = _args[5];
lean_object* v_00_u03c3_2678_ = _args[6];
lean_object* v_loopMutVars_2679_ = _args[7];
lean_object* v_returnsEarly_2680_ = _args[8];
lean_object* v_mi_2681_ = _args[9];
lean_object* v_a_2682_ = _args[10];
lean_object* v_a_2683_ = _args[11];
lean_object* v_a_2684_ = _args[12];
lean_object* v_a_2685_ = _args[13];
lean_object* v_a_2686_ = _args[14];
lean_object* v_a_2687_ = _args[15];
lean_object* v_a_2688_ = _args[16];
lean_object* v_a_2689_ = _args[17];
_start:
{
uint8_t v_returnsEarly_boxed_2690_; lean_object* v_res_2691_; 
v_returnsEarly_boxed_2690_ = lean_unbox(v_returnsEarly_2680_);
v_res_2691_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant(v_invClause_2672_, v_h_x3f_2673_, v_xs_2674_, v_00_u03b1_2675_, v_preS_2676_, v_body_2677_, v_00_u03c3_2678_, v_loopMutVars_2679_, v_returnsEarly_boxed_2690_, v_mi_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_);
lean_dec(v_a_2688_);
lean_dec_ref(v_a_2687_);
lean_dec(v_a_2686_);
lean_dec_ref(v_a_2685_);
lean_dec(v_a_2684_);
lean_dec_ref(v_a_2683_);
lean_dec_ref(v_a_2682_);
lean_dec_ref(v_loopMutVars_2679_);
lean_dec(v_h_x3f_2673_);
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1(lean_object* v_00_u03b1_2692_, lean_object* v_ref_2693_, lean_object* v_msg_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v___x_2703_; 
v___x_2703_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1___redArg(v_ref_2693_, v_msg_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1___boxed(lean_object* v_00_u03b1_2704_, lean_object* v_ref_2705_, lean_object* v_msg_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1(v_00_u03b1_2704_, v_ref_2705_, v_msg_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v_ref_2705_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__2(lean_object* v_as_2716_, size_t v_sz_2717_, size_t v_i_2718_, lean_object* v_b_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_){
_start:
{
lean_object* v___x_2728_; 
v___x_2728_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__2___redArg(v_as_2716_, v_sz_2717_, v_i_2718_, v_b_2719_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__2___boxed(lean_object* v_as_2729_, lean_object* v_sz_2730_, lean_object* v_i_2731_, lean_object* v_b_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
size_t v_sz_boxed_2741_; size_t v_i_boxed_2742_; lean_object* v_res_2743_; 
v_sz_boxed_2741_ = lean_unbox_usize(v_sz_2730_);
lean_dec(v_sz_2730_);
v_i_boxed_2742_ = lean_unbox_usize(v_i_2731_);
lean_dec(v_i_2731_);
v_res_2743_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__2(v_as_2729_, v_sz_boxed_2741_, v_i_boxed_2742_, v_b_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec_ref(v_as_2729_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1(lean_object* v_00_u03b1_2744_, lean_object* v_msg_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v___x_2754_; 
v___x_2754_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1___redArg(v_msg_2745_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2755_, lean_object* v_msg_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1(v_00_u03b1_2755_, v_msg_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec_ref(v___y_2757_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0(lean_object* v_k_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v_b_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v___x_2776_; 
lean_inc(v___y_2774_);
lean_inc_ref(v___y_2773_);
lean_inc(v___y_2772_);
lean_inc_ref(v___y_2771_);
lean_inc(v___y_2769_);
lean_inc_ref(v___y_2768_);
lean_inc_ref(v___y_2767_);
v___x_2776_ = lean_apply_9(v_k_2766_, v_b_2770_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, lean_box(0));
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0___boxed(lean_object* v_k_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v_b_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0(v_k_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v_b_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
lean_dec(v___y_2783_);
lean_dec_ref(v___y_2782_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec_ref(v___y_2778_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(lean_object* v_name_2788_, uint8_t v_bi_2789_, lean_object* v_type_2790_, lean_object* v_k_2791_, uint8_t v_kind_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
lean_object* v___f_2801_; lean_object* v___x_2802_; 
lean_inc(v___y_2795_);
lean_inc_ref(v___y_2794_);
lean_inc_ref(v___y_2793_);
v___f_2801_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2801_, 0, v_k_2791_);
lean_closure_set(v___f_2801_, 1, v___y_2793_);
lean_closure_set(v___f_2801_, 2, v___y_2794_);
lean_closure_set(v___f_2801_, 3, v___y_2795_);
v___x_2802_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2788_, v_bi_2789_, v_type_2790_, v___f_2801_, v_kind_2792_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
if (lean_obj_tag(v___x_2802_) == 0)
{
return v___x_2802_;
}
else
{
lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2810_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2805_ = v___x_2802_;
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___x_2802_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2808_; 
if (v_isShared_2806_ == 0)
{
v___x_2808_ = v___x_2805_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_a_2803_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___boxed(lean_object* v_name_2811_, lean_object* v_bi_2812_, lean_object* v_type_2813_, lean_object* v_k_2814_, lean_object* v_kind_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_){
_start:
{
uint8_t v_bi_boxed_2824_; uint8_t v_kind_boxed_2825_; lean_object* v_res_2826_; 
v_bi_boxed_2824_ = lean_unbox(v_bi_2812_);
v_kind_boxed_2825_ = lean_unbox(v_kind_2815_);
v_res_2826_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_name_2811_, v_bi_boxed_2824_, v_type_2813_, v_k_2814_, v_kind_boxed_2825_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
lean_dec(v___y_2822_);
lean_dec_ref(v___y_2821_);
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec_ref(v___y_2816_);
return v_res_2826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3(lean_object* v_00_u03b1_2827_, lean_object* v_name_2828_, uint8_t v_bi_2829_, lean_object* v_type_2830_, lean_object* v_k_2831_, uint8_t v_kind_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
lean_object* v___x_2841_; 
v___x_2841_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_name_2828_, v_bi_2829_, v_type_2830_, v_k_2831_, v_kind_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___boxed(lean_object* v_00_u03b1_2842_, lean_object* v_name_2843_, lean_object* v_bi_2844_, lean_object* v_type_2845_, lean_object* v_k_2846_, lean_object* v_kind_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
uint8_t v_bi_boxed_2856_; uint8_t v_kind_boxed_2857_; lean_object* v_res_2858_; 
v_bi_boxed_2856_ = lean_unbox(v_bi_2844_);
v_kind_boxed_2857_ = lean_unbox(v_kind_2847_);
v_res_2858_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3(v_00_u03b1_2842_, v_name_2843_, v_bi_boxed_2856_, v_type_2845_, v_k_2846_, v_kind_boxed_2857_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec_ref(v___y_2848_);
return v_res_2858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__0(lean_object* v_a_2859_, lean_object* v_x_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_){
_start:
{
lean_object* v___x_2869_; 
v___x_2869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2869_, 0, v_a_2859_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__0___boxed(lean_object* v_a_2870_, lean_object* v_x_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
lean_object* v_res_2880_; 
v_res_2880_ = l_Lean_Elab_Do_elabDoFor___lam__0(v_a_2870_, v_x_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec_ref(v_x_2871_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__2(lean_object* v_x_2881_, lean_object* v___f_2882_, lean_object* v___x_2883_, lean_object* v_x_2884_, lean_object* v_x_2885_){
_start:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2886_ = l_Lean_TSyntax_getId(v_x_2881_);
v___x_2887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2886_);
lean_ctor_set(v___x_2887_, 1, v___f_2882_);
v___x_2888_ = lean_mk_empty_array_with_capacity(v___x_2883_);
v___x_2889_ = lean_array_push(v___x_2888_, v___x_2887_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__2___boxed(lean_object* v_x_2890_, lean_object* v___f_2891_, lean_object* v___x_2892_, lean_object* v_x_2893_, lean_object* v_x_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l_Lean_Elab_Do_elabDoFor___lam__2(v_x_2890_, v___f_2891_, v___x_2892_, v_x_2893_, v_x_2894_);
lean_dec(v_x_2894_);
lean_dec(v_x_2893_);
lean_dec(v___x_2892_);
lean_dec(v_x_2890_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__1(lean_object* v_a_2896_, lean_object* v___x_2897_, uint8_t v___x_2898_, lean_object* v_r_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_){
_start:
{
lean_object* v_k_2908_; lean_object* v___x_2909_; 
v_k_2908_ = lean_ctor_get(v_a_2896_, 1);
lean_inc_ref(v_k_2908_);
lean_dec_ref(v_a_2896_);
lean_inc(v___y_2906_);
lean_inc_ref(v___y_2905_);
lean_inc(v___y_2904_);
lean_inc_ref(v___y_2903_);
lean_inc(v___y_2902_);
lean_inc_ref(v___y_2901_);
lean_inc_ref(v___y_2900_);
lean_inc_ref(v_r_2899_);
v___x_2909_ = lean_apply_9(v_k_2908_, v_r_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, lean_box(0));
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v_a_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; uint8_t v___x_2913_; uint8_t v___x_2914_; lean_object* v___x_2915_; 
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
lean_inc(v_a_2910_);
lean_dec_ref_known(v___x_2909_, 1);
v___x_2911_ = lean_mk_empty_array_with_capacity(v___x_2897_);
v___x_2912_ = lean_array_push(v___x_2911_, v_r_2899_);
v___x_2913_ = 0;
v___x_2914_ = 1;
v___x_2915_ = l_Lean_Meta_mkLambdaFVars(v___x_2912_, v_a_2910_, v___x_2913_, v___x_2898_, v___x_2913_, v___x_2898_, v___x_2914_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_);
lean_dec_ref(v___x_2912_);
return v___x_2915_;
}
else
{
lean_dec_ref(v_r_2899_);
return v___x_2909_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__1___boxed(lean_object* v_a_2916_, lean_object* v___x_2917_, lean_object* v___x_2918_, lean_object* v_r_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
uint8_t v___x_73961__boxed_2928_; lean_object* v_res_2929_; 
v___x_73961__boxed_2928_ = lean_unbox(v___x_2918_);
v_res_2929_ = l_Lean_Elab_Do_elabDoFor___lam__1(v_a_2916_, v___x_2917_, v___x_73961__boxed_2928_, v_r_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec(v___x_2917_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__0(lean_object* v___x_2930_, lean_object* v_as_2931_, size_t v_sz_2932_, size_t v_i_2933_, lean_object* v_b_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_){
_start:
{
uint8_t v___x_2942_; 
v___x_2942_ = lean_usize_dec_lt(v_i_2933_, v_sz_2932_);
if (v___x_2942_ == 0)
{
lean_object* v___x_2943_; 
lean_dec_ref(v___x_2930_);
v___x_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2943_, 0, v_b_2934_);
return v___x_2943_;
}
else
{
lean_object* v_a_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v_a_2944_ = lean_array_uget_borrowed(v_as_2931_, v_i_2933_);
v___x_2945_ = l_Lean_Elab_Do_MutVar_getId(v_a_2944_);
v___x_2946_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_2945_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v_a_2947_; lean_object* v_ident_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; uint8_t v___x_2952_; lean_object* v___x_2953_; 
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
lean_inc_n(v_a_2947_, 2);
lean_dec_ref_known(v___x_2946_, 1);
v_ident_2948_ = lean_ctor_get(v_a_2944_, 0);
v___x_2949_ = l_Lean_LocalDecl_toExpr(v_a_2947_);
v___x_2950_ = lean_box(0);
v___x_2951_ = lean_box(0);
v___x_2952_ = 0;
lean_inc_ref(v___x_2949_);
lean_inc(v_ident_2948_);
v___x_2953_ = l_Lean_Elab_Term_addTermInfo_x27(v_ident_2948_, v___x_2949_, v___x_2950_, v___x_2950_, v___x_2951_, v___x_2952_, v___x_2952_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v___x_2954_; lean_object* v___x_2955_; 
lean_dec_ref_known(v___x_2953_, 1);
v___x_2954_ = l_Lean_LocalDecl_type(v_a_2947_);
lean_dec(v_a_2947_);
v___x_2955_ = l_Lean_Meta_getDecLevel(v___x_2954_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; lean_object* v_u_2957_; lean_object* v___x_2958_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
lean_inc(v_a_2956_);
lean_dec_ref_known(v___x_2955_, 1);
v_u_2957_ = lean_ctor_get(v___x_2930_, 1);
lean_inc(v_u_2957_);
v___x_2958_ = l_Lean_Meta_isLevelDefEq(v_a_2956_, v_u_2957_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v___x_2959_; size_t v___x_2960_; size_t v___x_2961_; 
lean_dec_ref_known(v___x_2958_, 1);
v___x_2959_ = lean_array_push(v_b_2934_, v___x_2949_);
v___x_2960_ = ((size_t)1ULL);
v___x_2961_ = lean_usize_add(v_i_2933_, v___x_2960_);
v_i_2933_ = v___x_2961_;
v_b_2934_ = v___x_2959_;
goto _start;
}
else
{
lean_object* v_a_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2970_; 
lean_dec_ref(v___x_2949_);
lean_dec_ref(v_b_2934_);
lean_dec_ref(v___x_2930_);
v_a_2963_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2965_ = v___x_2958_;
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_a_2963_);
lean_dec(v___x_2958_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2968_; 
if (v_isShared_2966_ == 0)
{
v___x_2968_ = v___x_2965_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_a_2963_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
}
else
{
lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2978_; 
lean_dec_ref(v___x_2949_);
lean_dec_ref(v_b_2934_);
lean_dec_ref(v___x_2930_);
v_a_2971_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2973_ = v___x_2955_;
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2955_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2976_; 
if (v_isShared_2974_ == 0)
{
v___x_2976_ = v___x_2973_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_a_2971_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
}
else
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2986_; 
lean_dec_ref(v___x_2949_);
lean_dec(v_a_2947_);
lean_dec_ref(v_b_2934_);
lean_dec_ref(v___x_2930_);
v_a_2979_ = lean_ctor_get(v___x_2953_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2981_ = v___x_2953_;
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2953_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2984_; 
if (v_isShared_2982_ == 0)
{
v___x_2984_ = v___x_2981_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2979_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
}
}
else
{
lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2994_; 
lean_dec_ref(v_b_2934_);
lean_dec_ref(v___x_2930_);
v_a_2987_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2989_ = v___x_2946_;
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_dec(v___x_2946_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2992_; 
if (v_isShared_2990_ == 0)
{
v___x_2992_ = v___x_2989_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_a_2987_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
return v___x_2992_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__0___boxed(lean_object* v___x_2995_, lean_object* v_as_2996_, lean_object* v_sz_2997_, lean_object* v_i_2998_, lean_object* v_b_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
size_t v_sz_boxed_3007_; size_t v_i_boxed_3008_; lean_object* v_res_3009_; 
v_sz_boxed_3007_ = lean_unbox_usize(v_sz_2997_);
lean_dec(v_sz_2997_);
v_i_boxed_3008_ = lean_unbox_usize(v_i_2998_);
lean_dec(v_i_2998_);
v_res_3009_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__0(v___x_2995_, v_as_2996_, v_sz_boxed_3007_, v_i_boxed_3008_, v_b_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec_ref(v_as_2996_);
return v_res_3009_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3010_ = lean_box(1);
v___x_3011_ = l_Lean_MessageData_ofFormat(v___x_3010_);
return v___x_3011_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__3(void){
_start:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3015_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__2));
v___x_3016_ = l_Lean_MessageData_ofFormat(v___x_3015_);
return v___x_3016_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4(lean_object* v_x_3017_, lean_object* v_x_3018_){
_start:
{
if (lean_obj_tag(v_x_3018_) == 0)
{
return v_x_3017_;
}
else
{
lean_object* v_head_3019_; lean_object* v_tail_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3042_; 
v_head_3019_ = lean_ctor_get(v_x_3018_, 0);
v_tail_3020_ = lean_ctor_get(v_x_3018_, 1);
v_isSharedCheck_3042_ = !lean_is_exclusive(v_x_3018_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3022_ = v_x_3018_;
v_isShared_3023_ = v_isSharedCheck_3042_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_tail_3020_);
lean_inc(v_head_3019_);
lean_dec(v_x_3018_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3042_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v_before_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3040_; 
v_before_3024_ = lean_ctor_get(v_head_3019_, 0);
v_isSharedCheck_3040_ = !lean_is_exclusive(v_head_3019_);
if (v_isSharedCheck_3040_ == 0)
{
lean_object* v_unused_3041_; 
v_unused_3041_ = lean_ctor_get(v_head_3019_, 1);
lean_dec(v_unused_3041_);
v___x_3026_ = v_head_3019_;
v_isShared_3027_ = v_isSharedCheck_3040_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_before_3024_);
lean_dec(v_head_3019_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3040_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3028_; lean_object* v___x_3030_; 
v___x_3028_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__0);
if (v_isShared_3027_ == 0)
{
lean_ctor_set_tag(v___x_3026_, 7);
lean_ctor_set(v___x_3026_, 1, v___x_3028_);
lean_ctor_set(v___x_3026_, 0, v_x_3017_);
v___x_3030_ = v___x_3026_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_x_3017_);
lean_ctor_set(v_reuseFailAlloc_3039_, 1, v___x_3028_);
v___x_3030_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
lean_object* v___x_3031_; lean_object* v___x_3033_; 
v___x_3031_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__3);
if (v_isShared_3023_ == 0)
{
lean_ctor_set_tag(v___x_3022_, 7);
lean_ctor_set(v___x_3022_, 1, v___x_3031_);
lean_ctor_set(v___x_3022_, 0, v___x_3030_);
v___x_3033_ = v___x_3022_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3030_);
lean_ctor_set(v_reuseFailAlloc_3038_, 1, v___x_3031_);
v___x_3033_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
v___x_3034_ = l_Lean_MessageData_ofSyntax(v_before_3024_);
v___x_3035_ = l_Lean_indentD(v___x_3034_);
v___x_3036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3033_);
lean_ctor_set(v___x_3036_, 1, v___x_3035_);
v_x_3017_ = v___x_3036_;
v_x_3018_ = v_tail_3020_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3(lean_object* v_opts_3043_, lean_object* v_opt_3044_){
_start:
{
lean_object* v_name_3045_; lean_object* v_defValue_3046_; lean_object* v_map_3047_; lean_object* v___x_3048_; 
v_name_3045_ = lean_ctor_get(v_opt_3044_, 0);
v_defValue_3046_ = lean_ctor_get(v_opt_3044_, 1);
v_map_3047_ = lean_ctor_get(v_opts_3043_, 0);
v___x_3048_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3047_, v_name_3045_);
if (lean_obj_tag(v___x_3048_) == 0)
{
uint8_t v___x_3049_; 
v___x_3049_ = lean_unbox(v_defValue_3046_);
return v___x_3049_;
}
else
{
lean_object* v_val_3050_; 
v_val_3050_ = lean_ctor_get(v___x_3048_, 0);
lean_inc(v_val_3050_);
lean_dec_ref_known(v___x_3048_, 1);
if (lean_obj_tag(v_val_3050_) == 1)
{
uint8_t v_v_3051_; 
v_v_3051_ = lean_ctor_get_uint8(v_val_3050_, 0);
lean_dec_ref_known(v_val_3050_, 0);
return v_v_3051_;
}
else
{
uint8_t v___x_3052_; 
lean_dec(v_val_3050_);
v___x_3052_ = lean_unbox(v_defValue_3046_);
return v___x_3052_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3___boxed(lean_object* v_opts_3053_, lean_object* v_opt_3054_){
_start:
{
uint8_t v_res_3055_; lean_object* v_r_3056_; 
v_res_3055_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3(v_opts_3053_, v_opt_3054_);
lean_dec_ref(v_opt_3054_);
lean_dec_ref(v_opts_3053_);
v_r_3056_ = lean_box(v_res_3055_);
return v_r_3056_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3060_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__1));
v___x_3061_ = l_Lean_MessageData_ofFormat(v___x_3060_);
return v___x_3061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg(lean_object* v_msgData_3062_, lean_object* v_macroStack_3063_, lean_object* v___y_3064_){
_start:
{
lean_object* v_options_3066_; lean_object* v___x_3067_; uint8_t v___x_3068_; 
v_options_3066_ = lean_ctor_get(v___y_3064_, 2);
v___x_3067_ = l_Lean_Elab_pp_macroStack;
v___x_3068_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3(v_options_3066_, v___x_3067_);
if (v___x_3068_ == 0)
{
lean_object* v___x_3069_; 
lean_dec(v_macroStack_3063_);
v___x_3069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3069_, 0, v_msgData_3062_);
return v___x_3069_;
}
else
{
if (lean_obj_tag(v_macroStack_3063_) == 0)
{
lean_object* v___x_3070_; 
v___x_3070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3070_, 0, v_msgData_3062_);
return v___x_3070_;
}
else
{
lean_object* v_head_3071_; lean_object* v_after_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3087_; 
v_head_3071_ = lean_ctor_get(v_macroStack_3063_, 0);
lean_inc(v_head_3071_);
v_after_3072_ = lean_ctor_get(v_head_3071_, 1);
v_isSharedCheck_3087_ = !lean_is_exclusive(v_head_3071_);
if (v_isSharedCheck_3087_ == 0)
{
lean_object* v_unused_3088_; 
v_unused_3088_ = lean_ctor_get(v_head_3071_, 0);
lean_dec(v_unused_3088_);
v___x_3074_ = v_head_3071_;
v_isShared_3075_ = v_isSharedCheck_3087_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_after_3072_);
lean_dec(v_head_3071_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3087_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3076_; lean_object* v___x_3078_; 
v___x_3076_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4___closed__0);
if (v_isShared_3075_ == 0)
{
lean_ctor_set_tag(v___x_3074_, 7);
lean_ctor_set(v___x_3074_, 1, v___x_3076_);
lean_ctor_set(v___x_3074_, 0, v_msgData_3062_);
v___x_3078_ = v___x_3074_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_msgData_3062_);
lean_ctor_set(v_reuseFailAlloc_3086_, 1, v___x_3076_);
v___x_3078_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v_msgData_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3079_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__2);
v___x_3080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3078_);
lean_ctor_set(v___x_3080_, 1, v___x_3079_);
v___x_3081_ = l_Lean_MessageData_ofSyntax(v_after_3072_);
v___x_3082_ = l_Lean_indentD(v___x_3081_);
v_msgData_3083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_3083_, 0, v___x_3080_);
lean_ctor_set(v_msgData_3083_, 1, v___x_3082_);
v___x_3084_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__4(v_msgData_3083_, v_macroStack_3063_);
v___x_3085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3084_);
return v___x_3085_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_3089_, lean_object* v_macroStack_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_){
_start:
{
lean_object* v_res_3093_; 
v_res_3093_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg(v_msgData_3089_, v_macroStack_3090_, v___y_3091_);
lean_dec_ref(v___y_3091_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___redArg(lean_object* v_msg_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_){
_start:
{
lean_object* v_ref_3102_; lean_object* v___x_3103_; lean_object* v_a_3104_; lean_object* v_macroStack_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3116_; 
v_ref_3102_ = lean_ctor_get(v___y_3099_, 5);
v___x_3103_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__1_spec__1_spec__2(v_msg_3094_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
lean_inc(v_a_3104_);
lean_dec_ref(v___x_3103_);
v_macroStack_3105_ = lean_ctor_get(v___y_3095_, 1);
v___x_3106_ = l_Lean_Elab_getBetterRef(v_ref_3102_, v_macroStack_3105_);
lean_inc(v_macroStack_3105_);
v___x_3107_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg(v_a_3104_, v_macroStack_3105_, v___y_3099_);
v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3110_ = v___x_3107_;
v_isShared_3111_ = v_isSharedCheck_3116_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3107_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3116_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3112_; lean_object* v___x_3114_; 
v___x_3112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3112_, 0, v___x_3106_);
lean_ctor_set(v___x_3112_, 1, v_a_3108_);
if (v_isShared_3111_ == 0)
{
lean_ctor_set_tag(v___x_3110_, 1);
lean_ctor_set(v___x_3110_, 0, v___x_3112_);
v___x_3114_ = v___x_3110_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3112_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___redArg___boxed(lean_object* v_msg_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_){
_start:
{
lean_object* v_res_3125_; 
v_res_3125_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___redArg(v_msg_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_);
lean_dec(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
return v_res_3125_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__3(void){
_start:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3131_ = lean_box(0);
v___x_3132_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__3___closed__2));
v___x_3133_ = l_Lean_mkConst(v___x_3132_, v___x_3131_);
return v___x_3133_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__5(void){
_start:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3135_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__3___closed__4));
v___x_3136_ = l_Lean_stringToMessageData(v___x_3135_);
return v___x_3136_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__7(void){
_start:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3138_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__3___closed__6));
v___x_3139_ = l_Lean_stringToMessageData(v___x_3138_);
return v___x_3139_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__10(void){
_start:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3143_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__3___closed__9));
v___x_3144_ = l_Lean_MessageData_ofFormat(v___x_3143_);
return v___x_3144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__3(lean_object* v___y_3145_, lean_object* v_monadInfo_3146_, uint8_t v_returnsEarly_3147_, lean_object* v___x_3148_, lean_object* v_a_3149_, uint8_t v___x_3150_, lean_object* v_e_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_){
_start:
{
lean_object* v_defs_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___x_3183_; lean_object* v_returnVar_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3218_; lean_object* v___y_3219_; 
v___x_3183_ = lean_mk_empty_array_with_capacity(v___x_3148_);
if (lean_obj_tag(v_e_3151_) == 0)
{
if (v___x_3150_ == 0)
{
goto v___jp_3232_;
}
else
{
goto v___jp_3193_;
}
}
else
{
goto v___jp_3232_;
}
v___jp_3159_:
{
size_t v_sz_3167_; size_t v___x_3168_; lean_object* v___x_3169_; 
v_sz_3167_ = lean_array_size(v___y_3145_);
v___x_3168_ = ((size_t)0ULL);
v___x_3169_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__0(v_monadInfo_3146_, v___y_3145_, v_sz_3167_, v___x_3168_, v_defs_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_);
if (lean_obj_tag(v___x_3169_) == 0)
{
if (v_returnsEarly_3147_ == 0)
{
return v___x_3169_;
}
else
{
lean_object* v_a_3170_; lean_object* v___x_3171_; uint8_t v___x_3172_; 
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
lean_inc(v_a_3170_);
v___x_3171_ = lean_array_get_size(v___y_3145_);
v___x_3172_ = lean_nat_dec_eq(v___x_3171_, v___x_3148_);
if (v___x_3172_ == 0)
{
lean_dec(v_a_3170_);
return v___x_3169_;
}
else
{
lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3181_; 
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3181_ == 0)
{
lean_object* v_unused_3182_; 
v_unused_3182_ = lean_ctor_get(v___x_3169_, 0);
lean_dec(v_unused_3182_);
v___x_3174_ = v___x_3169_;
v_isShared_3175_ = v_isSharedCheck_3181_;
goto v_resetjp_3173_;
}
else
{
lean_dec(v___x_3169_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3181_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3179_; 
v___x_3176_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__3___closed__3, &l_Lean_Elab_Do_elabDoFor___lam__3___closed__3_once, _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__3);
v___x_3177_ = lean_array_push(v_a_3170_, v___x_3176_);
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 0, v___x_3177_);
v___x_3179_ = v___x_3174_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v___x_3177_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
}
}
}
else
{
return v___x_3169_;
}
}
v___jp_3184_:
{
lean_object* v___x_3192_; 
v___x_3192_ = lean_array_push(v___x_3183_, v_returnVar_3185_);
v_defs_3160_ = v___x_3192_;
v___y_3161_ = v___y_3186_;
v___y_3162_ = v___y_3187_;
v___y_3163_ = v___y_3188_;
v___y_3164_ = v___y_3189_;
v___y_3165_ = v___y_3190_;
v___y_3166_ = v___y_3191_;
goto v___jp_3159_;
}
v___jp_3193_:
{
if (v_returnsEarly_3147_ == 0)
{
lean_dec(v_e_3151_);
lean_dec_ref(v_a_3149_);
v_defs_3160_ = v___x_3183_;
v___y_3161_ = v___y_3152_;
v___y_3162_ = v___y_3153_;
v___y_3163_ = v___y_3154_;
v___y_3164_ = v___y_3155_;
v___y_3165_ = v___y_3156_;
v___y_3166_ = v___y_3157_;
goto v___jp_3159_;
}
else
{
if (lean_obj_tag(v_e_3151_) == 0)
{
lean_object* v_resultType_3194_; lean_object* v___x_3195_; 
v_resultType_3194_ = lean_ctor_get(v_a_3149_, 0);
lean_inc_ref(v_resultType_3194_);
lean_dec_ref(v_a_3149_);
v___x_3195_ = l_Lean_Meta_mkNone(v_resultType_3194_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
if (lean_obj_tag(v___x_3195_) == 0)
{
lean_object* v_a_3196_; 
v_a_3196_ = lean_ctor_get(v___x_3195_, 0);
lean_inc(v_a_3196_);
lean_dec_ref_known(v___x_3195_, 1);
v_returnVar_3185_ = v_a_3196_;
v___y_3186_ = v___y_3152_;
v___y_3187_ = v___y_3153_;
v___y_3188_ = v___y_3154_;
v___y_3189_ = v___y_3155_;
v___y_3190_ = v___y_3156_;
v___y_3191_ = v___y_3157_;
goto v___jp_3184_;
}
else
{
lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3204_; 
lean_dec_ref(v___x_3183_);
lean_dec_ref(v_monadInfo_3146_);
v_a_3197_ = lean_ctor_get(v___x_3195_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3199_ = v___x_3195_;
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_3195_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3202_; 
if (v_isShared_3200_ == 0)
{
v___x_3202_ = v___x_3199_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_a_3197_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
}
else
{
lean_object* v_val_3205_; lean_object* v_resultType_3206_; lean_object* v___x_3207_; 
v_val_3205_ = lean_ctor_get(v_e_3151_, 0);
lean_inc(v_val_3205_);
lean_dec_ref_known(v_e_3151_, 1);
v_resultType_3206_ = lean_ctor_get(v_a_3149_, 0);
lean_inc_ref(v_resultType_3206_);
lean_dec_ref(v_a_3149_);
v___x_3207_ = l_Lean_Meta_mkSome(v_resultType_3206_, v_val_3205_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v_a_3208_; 
v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
lean_inc(v_a_3208_);
lean_dec_ref_known(v___x_3207_, 1);
v_returnVar_3185_ = v_a_3208_;
v___y_3186_ = v___y_3152_;
v___y_3187_ = v___y_3153_;
v___y_3188_ = v___y_3154_;
v___y_3189_ = v___y_3155_;
v___y_3190_ = v___y_3156_;
v___y_3191_ = v___y_3157_;
goto v___jp_3184_;
}
else
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3216_; 
lean_dec_ref(v___x_3183_);
lean_dec_ref(v_monadInfo_3146_);
v_a_3209_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3211_ = v___x_3207_;
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3207_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3214_; 
if (v_isShared_3212_ == 0)
{
v___x_3214_ = v___x_3211_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_a_3209_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
}
}
}
v___jp_3217_:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3231_; 
lean_inc_ref(v___y_3218_);
v___x_3220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3220_, 0, v___y_3218_);
lean_ctor_set(v___x_3220_, 1, v___y_3219_);
v___x_3221_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__3___closed__5, &l_Lean_Elab_Do_elabDoFor___lam__3___closed__5_once, _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__5);
v___x_3222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3220_);
lean_ctor_set(v___x_3222_, 1, v___x_3221_);
v___x_3223_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___redArg(v___x_3222_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
v_a_3224_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3226_ = v___x_3223_;
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v___x_3223_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3229_; 
if (v_isShared_3227_ == 0)
{
v___x_3229_ = v___x_3226_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_a_3224_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
}
v___jp_3232_:
{
if (v_returnsEarly_3147_ == 0)
{
lean_object* v___x_3233_; 
lean_dec_ref(v___x_3183_);
lean_dec_ref(v_a_3149_);
lean_dec_ref(v_monadInfo_3146_);
v___x_3233_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__3___closed__7, &l_Lean_Elab_Do_elabDoFor___lam__3___closed__7_once, _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__7);
if (lean_obj_tag(v_e_3151_) == 0)
{
lean_object* v___x_3234_; 
v___x_3234_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__3___closed__10, &l_Lean_Elab_Do_elabDoFor___lam__3___closed__10_once, _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__10);
v___y_3218_ = v___x_3233_;
v___y_3219_ = v___x_3234_;
goto v___jp_3217_;
}
else
{
lean_object* v_val_3235_; lean_object* v___x_3236_; 
v_val_3235_ = lean_ctor_get(v_e_3151_, 0);
lean_inc(v_val_3235_);
lean_dec_ref_known(v_e_3151_, 1);
v___x_3236_ = l_Lean_MessageData_ofExpr(v_val_3235_);
v___y_3218_ = v___x_3233_;
v___y_3219_ = v___x_3236_;
goto v___jp_3217_;
}
}
else
{
goto v___jp_3193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___boxed(lean_object* v___y_3237_, lean_object* v_monadInfo_3238_, lean_object* v_returnsEarly_3239_, lean_object* v___x_3240_, lean_object* v_a_3241_, lean_object* v___x_3242_, lean_object* v_e_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_){
_start:
{
uint8_t v_returnsEarly_boxed_3251_; uint8_t v___x_74367__boxed_3252_; lean_object* v_res_3253_; 
v_returnsEarly_boxed_3251_ = lean_unbox(v_returnsEarly_3239_);
v___x_74367__boxed_3252_ = lean_unbox(v___x_3242_);
v_res_3253_ = l_Lean_Elab_Do_elabDoFor___lam__3(v___y_3237_, v_monadInfo_3238_, v_returnsEarly_boxed_3251_, v___x_3240_, v_a_3241_, v___x_74367__boxed_3252_, v_e_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___x_3240_);
lean_dec_ref(v___y_3237_);
return v_res_3253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(lean_object* v_name_3254_, lean_object* v_type_3255_, lean_object* v_k_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_){
_start:
{
uint8_t v___x_3265_; uint8_t v___x_3266_; lean_object* v___x_3267_; 
v___x_3265_ = 0;
v___x_3266_ = 0;
v___x_3267_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_name_3254_, v___x_3265_, v_type_3255_, v_k_3256_, v___x_3266_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg___boxed(lean_object* v_name_3268_, lean_object* v_type_3269_, lean_object* v_k_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_){
_start:
{
lean_object* v_res_3279_; 
v_res_3279_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v_name_3268_, v_type_3269_, v_k_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_);
lean_dec(v___y_3277_);
lean_dec_ref(v___y_3276_);
lean_dec(v___y_3275_);
lean_dec_ref(v___y_3274_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec_ref(v___y_3271_);
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__4(uint8_t v_returnsEarly_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_doBlockResultType_3300_, lean_object* v_a_3301_, lean_object* v_v_3302_, lean_object* v_u_3303_, lean_object* v___f_3304_, lean_object* v___y_3305_, lean_object* v___x_3306_, lean_object* v___x_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_){
_start:
{
lean_object* v_ret_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; 
if (v_returnsEarly_3297_ == 0)
{
lean_object* v___x_3371_; 
lean_dec_ref(v___f_3304_);
lean_dec(v_u_3303_);
lean_dec(v_v_3302_);
lean_dec_ref(v_a_3301_);
lean_dec_ref(v_doBlockResultType_3300_);
lean_dec(v_a_3299_);
v___x_3371_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_a_3298_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
return v___x_3371_;
}
else
{
lean_object* v___x_3372_; 
v___x_3372_ = l_Lean_Meta_getFVarFromUserName(v_a_3299_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v_a_3373_; lean_object* v___x_3374_; uint8_t v___x_3375_; 
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
lean_inc(v_a_3373_);
lean_dec_ref_known(v___x_3372_, 1);
v___x_3374_ = lean_array_get_size(v___y_3305_);
v___x_3375_ = lean_nat_dec_eq(v___x_3374_, v___x_3306_);
if (v___x_3375_ == 0)
{
v_ret_3317_ = v_a_3373_;
v___y_3318_ = v___y_3308_;
v___y_3319_ = v___y_3309_;
v___y_3320_ = v___y_3310_;
v___y_3321_ = v___y_3311_;
v___y_3322_ = v___y_3312_;
v___y_3323_ = v___y_3313_;
v___y_3324_ = v___y_3314_;
goto v___jp_3316_;
}
else
{
lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3376_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__4___closed__9));
v___x_3377_ = lean_mk_empty_array_with_capacity(v___x_3307_);
v___x_3378_ = lean_array_push(v___x_3377_, v_a_3373_);
v___x_3379_ = l_Lean_Meta_mkAppM(v___x_3376_, v___x_3378_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
if (lean_obj_tag(v___x_3379_) == 0)
{
lean_object* v_a_3380_; 
v_a_3380_ = lean_ctor_get(v___x_3379_, 0);
lean_inc(v_a_3380_);
lean_dec_ref_known(v___x_3379_, 1);
v_ret_3317_ = v_a_3380_;
v___y_3318_ = v___y_3308_;
v___y_3319_ = v___y_3309_;
v___y_3320_ = v___y_3310_;
v___y_3321_ = v___y_3311_;
v___y_3322_ = v___y_3312_;
v___y_3323_ = v___y_3313_;
v___y_3324_ = v___y_3314_;
goto v___jp_3316_;
}
else
{
lean_dec_ref(v___f_3304_);
lean_dec(v_u_3303_);
lean_dec(v_v_3302_);
lean_dec_ref(v_a_3301_);
lean_dec_ref(v_doBlockResultType_3300_);
lean_dec_ref(v_a_3298_);
return v___x_3379_;
}
}
}
else
{
lean_dec_ref(v___f_3304_);
lean_dec(v_u_3303_);
lean_dec(v_v_3302_);
lean_dec_ref(v_a_3301_);
lean_dec_ref(v_doBlockResultType_3300_);
lean_dec_ref(v_a_3298_);
return v___x_3372_;
}
}
v___jp_3316_:
{
lean_object* v___x_3325_; 
lean_inc(v___y_3324_);
lean_inc_ref(v___y_3323_);
lean_inc(v___y_3322_);
lean_inc_ref(v___y_3321_);
lean_inc_ref(v_ret_3317_);
v___x_3325_ = lean_infer_type(v_ret_3317_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
if (lean_obj_tag(v___x_3325_) == 0)
{
lean_object* v_a_3326_; lean_object* v___x_3327_; 
v_a_3326_ = lean_ctor_get(v___x_3325_, 0);
lean_inc(v_a_3326_);
lean_dec_ref_known(v___x_3325_, 1);
v___x_3327_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_3300_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_object* v_a_3328_; lean_object* v___x_3329_; 
v_a_3328_ = lean_ctor_get(v___x_3327_, 0);
lean_inc(v_a_3328_);
lean_dec_ref_known(v___x_3327_, 1);
v___x_3329_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_a_3298_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_object* v_a_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; 
v_a_3330_ = lean_ctor_get(v___x_3329_, 0);
lean_inc(v_a_3330_);
lean_dec_ref_known(v___x_3329_, 1);
v___x_3331_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__4___closed__1));
v___x_3332_ = l_Lean_Core_mkFreshUserName(v___x_3331_, v___y_3323_, v___y_3324_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v_a_3333_; lean_object* v_resultType_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3361_; 
v_a_3333_ = lean_ctor_get(v___x_3332_, 0);
lean_inc(v_a_3333_);
lean_dec_ref_known(v___x_3332_, 1);
v_resultType_3334_ = lean_ctor_get(v_a_3301_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v_a_3301_);
if (v_isSharedCheck_3361_ == 0)
{
lean_object* v_unused_3362_; 
v_unused_3362_ = lean_ctor_get(v_a_3301_, 1);
lean_dec(v_unused_3362_);
v___x_3336_ = v_a_3301_;
v_isShared_3337_ = v_isSharedCheck_3361_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_resultType_3334_);
lean_dec(v_a_3301_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3361_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3338_; uint8_t v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3345_; 
v___x_3338_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__4___closed__2));
v___x_3339_ = 0;
v___x_3340_ = l_Lean_mkLambda(v___x_3338_, v___x_3339_, v_a_3326_, v_a_3328_);
v___x_3341_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__4___closed__6));
v___x_3342_ = l_Lean_Level_succ___override(v_v_3302_);
v___x_3343_ = lean_box(0);
if (v_isShared_3337_ == 0)
{
lean_ctor_set_tag(v___x_3336_, 1);
lean_ctor_set(v___x_3336_, 1, v___x_3343_);
lean_ctor_set(v___x_3336_, 0, v___x_3342_);
v___x_3345_ = v___x_3336_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3342_);
lean_ctor_set(v_reuseFailAlloc_3360_, 1, v___x_3343_);
v___x_3345_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3346_, 0, v_u_3303_);
lean_ctor_set(v___x_3346_, 1, v___x_3345_);
v___x_3347_ = l_Lean_mkConst(v___x_3341_, v___x_3346_);
lean_inc_ref(v_resultType_3334_);
v___x_3348_ = l_Lean_mkApp3(v___x_3347_, v_resultType_3334_, v___x_3340_, v_ret_3317_);
v___x_3349_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v_a_3333_, v_resultType_3334_, v___f_3304_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3359_; 
v_a_3350_ = lean_ctor_get(v___x_3349_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3352_ = v___x_3349_;
v_isShared_3353_ = v_isSharedCheck_3359_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3349_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3359_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3357_; 
v___x_3354_ = l_Lean_mkSimpleThunk(v_a_3330_);
v___x_3355_ = l_Lean_mkAppB(v___x_3348_, v_a_3350_, v___x_3354_);
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 0, v___x_3355_);
v___x_3357_ = v___x_3352_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v___x_3355_);
v___x_3357_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
return v___x_3357_;
}
}
}
else
{
lean_dec_ref(v___x_3348_);
lean_dec(v_a_3330_);
return v___x_3349_;
}
}
}
}
else
{
lean_object* v_a_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3370_; 
lean_dec(v_a_3330_);
lean_dec(v_a_3328_);
lean_dec(v_a_3326_);
lean_dec_ref(v_ret_3317_);
lean_dec_ref(v___f_3304_);
lean_dec(v_u_3303_);
lean_dec(v_v_3302_);
lean_dec_ref(v_a_3301_);
v_a_3363_ = lean_ctor_get(v___x_3332_, 0);
v_isSharedCheck_3370_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3365_ = v___x_3332_;
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_a_3363_);
lean_dec(v___x_3332_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3368_; 
if (v_isShared_3366_ == 0)
{
v___x_3368_ = v___x_3365_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_a_3363_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
return v___x_3368_;
}
}
}
}
else
{
lean_dec(v_a_3328_);
lean_dec(v_a_3326_);
lean_dec_ref(v_ret_3317_);
lean_dec_ref(v___f_3304_);
lean_dec(v_u_3303_);
lean_dec(v_v_3302_);
lean_dec_ref(v_a_3301_);
return v___x_3329_;
}
}
else
{
lean_dec(v_a_3326_);
lean_dec_ref(v_ret_3317_);
lean_dec_ref(v___f_3304_);
lean_dec(v_u_3303_);
lean_dec(v_v_3302_);
lean_dec_ref(v_a_3301_);
lean_dec_ref(v_a_3298_);
return v___x_3327_;
}
}
else
{
lean_dec_ref(v_ret_3317_);
lean_dec_ref(v___f_3304_);
lean_dec(v_u_3303_);
lean_dec(v_v_3302_);
lean_dec_ref(v_a_3301_);
lean_dec_ref(v_doBlockResultType_3300_);
lean_dec_ref(v_a_3298_);
return v___x_3325_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___boxed(lean_object** _args){
lean_object* v_returnsEarly_3381_ = _args[0];
lean_object* v_a_3382_ = _args[1];
lean_object* v_a_3383_ = _args[2];
lean_object* v_doBlockResultType_3384_ = _args[3];
lean_object* v_a_3385_ = _args[4];
lean_object* v_v_3386_ = _args[5];
lean_object* v_u_3387_ = _args[6];
lean_object* v___f_3388_ = _args[7];
lean_object* v___y_3389_ = _args[8];
lean_object* v___x_3390_ = _args[9];
lean_object* v___x_3391_ = _args[10];
lean_object* v___y_3392_ = _args[11];
lean_object* v___y_3393_ = _args[12];
lean_object* v___y_3394_ = _args[13];
lean_object* v___y_3395_ = _args[14];
lean_object* v___y_3396_ = _args[15];
lean_object* v___y_3397_ = _args[16];
lean_object* v___y_3398_ = _args[17];
lean_object* v___y_3399_ = _args[18];
_start:
{
uint8_t v_returnsEarly_boxed_3400_; lean_object* v_res_3401_; 
v_returnsEarly_boxed_3400_ = lean_unbox(v_returnsEarly_3381_);
v_res_3401_ = l_Lean_Elab_Do_elabDoFor___lam__4(v_returnsEarly_boxed_3400_, v_a_3382_, v_a_3383_, v_doBlockResultType_3384_, v_a_3385_, v_v_3386_, v_u_3387_, v___f_3388_, v___y_3389_, v___x_3390_, v___x_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3397_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3395_);
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec(v___x_3391_);
lean_dec(v___x_3390_);
lean_dec_ref(v___y_3389_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__5(lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___x_3404_, uint8_t v___x_3405_, lean_object* v_postS_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_){
_start:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3415_ = l_Lean_Expr_fvarId_x21(v_postS_3406_);
v___x_3416_ = l_Lean_Elab_Do_bindMutVarsFromTuple(v___y_3402_, v___x_3415_, v___y_3403_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v_a_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; uint8_t v___x_3420_; uint8_t v___x_3421_; lean_object* v___x_3422_; 
v_a_3417_ = lean_ctor_get(v___x_3416_, 0);
lean_inc(v_a_3417_);
lean_dec_ref_known(v___x_3416_, 1);
v___x_3418_ = lean_mk_empty_array_with_capacity(v___x_3404_);
v___x_3419_ = lean_array_push(v___x_3418_, v_postS_3406_);
v___x_3420_ = 0;
v___x_3421_ = 1;
v___x_3422_ = l_Lean_Meta_mkLambdaFVars(v___x_3419_, v_a_3417_, v___x_3420_, v___x_3405_, v___x_3420_, v___x_3405_, v___x_3421_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
lean_dec_ref(v___x_3419_);
return v___x_3422_;
}
else
{
lean_dec_ref(v_postS_3406_);
return v___x_3416_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__5___boxed(lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___x_3425_, lean_object* v___x_3426_, lean_object* v_postS_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_){
_start:
{
uint8_t v___x_74827__boxed_3436_; lean_object* v_res_3437_; 
v___x_74827__boxed_3436_ = lean_unbox(v___x_3426_);
v_res_3437_ = l_Lean_Elab_Do_elabDoFor___lam__5(v___y_3423_, v___y_3424_, v___x_3425_, v___x_74827__boxed_3436_, v_postS_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
lean_dec(v___y_3432_);
lean_dec_ref(v___y_3431_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___x_3425_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__6(lean_object* v___f_3439_, lean_object* v_u_3440_, lean_object* v___x_3441_, lean_object* v___x_3442_, lean_object* v_snd_3443_, lean_object* v___x_3444_, lean_object* v_e_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_){
_start:
{
lean_object* v___x_3454_; lean_object* v___x_3455_; 
v___x_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3454_, 0, v_e_3445_);
lean_inc(v___y_3452_);
lean_inc_ref(v___y_3451_);
lean_inc(v___y_3450_);
lean_inc_ref(v___y_3449_);
lean_inc(v___y_3448_);
lean_inc_ref(v___y_3447_);
v___x_3455_ = lean_apply_8(v___f_3439_, v___x_3454_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, lean_box(0));
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_object* v_a_3456_; lean_object* v___x_3457_; 
v_a_3456_ = lean_ctor_get(v___x_3455_, 0);
lean_inc(v_a_3456_);
lean_dec_ref_known(v___x_3455_, 1);
v___x_3457_ = l_Lean_Meta_mkProdMkN(v_a_3456_, v_u_3440_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_a_3458_; lean_object* v_fst_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; 
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
lean_inc(v_a_3458_);
lean_dec_ref_known(v___x_3457_, 1);
v_fst_3459_ = lean_ctor_get(v_a_3458_, 0);
lean_inc(v_fst_3459_);
lean_dec(v_a_3458_);
v___x_3460_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__6___closed__0));
v___x_3461_ = l_Lean_Name_mkStr2(v___x_3441_, v___x_3460_);
v___x_3462_ = l_Lean_mkConst(v___x_3461_, v___x_3442_);
v___x_3463_ = l_Lean_mkAppB(v___x_3462_, v_snd_3443_, v_fst_3459_);
v___x_3464_ = l_Lean_Elab_Do_mkPureApp(v___x_3444_, v___x_3463_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_);
return v___x_3464_;
}
else
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3472_; 
lean_dec_ref(v___x_3444_);
lean_dec_ref(v_snd_3443_);
lean_dec(v___x_3442_);
lean_dec_ref(v___x_3441_);
v_a_3465_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3467_ = v___x_3457_;
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3457_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3470_; 
if (v_isShared_3468_ == 0)
{
v___x_3470_ = v___x_3467_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_a_3465_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
}
else
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3480_; 
lean_dec_ref(v___x_3444_);
lean_dec_ref(v_snd_3443_);
lean_dec(v___x_3442_);
lean_dec_ref(v___x_3441_);
lean_dec(v_u_3440_);
v_a_3473_ = lean_ctor_get(v___x_3455_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3475_ = v___x_3455_;
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3455_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3478_; 
if (v_isShared_3476_ == 0)
{
v___x_3478_ = v___x_3475_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3473_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__6___boxed(lean_object* v___f_3481_, lean_object* v_u_3482_, lean_object* v___x_3483_, lean_object* v___x_3484_, lean_object* v_snd_3485_, lean_object* v___x_3486_, lean_object* v_e_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_){
_start:
{
lean_object* v_res_3496_; 
v_res_3496_ = l_Lean_Elab_Do_elabDoFor___lam__6(v___f_3481_, v_u_3482_, v___x_3483_, v___x_3484_, v_snd_3485_, v___x_3486_, v_e_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
lean_dec(v___y_3494_);
lean_dec_ref(v___y_3493_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec_ref(v___y_3488_);
return v_res_3496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__7(lean_object* v___f_3498_, lean_object* v___x_3499_, lean_object* v_u_3500_, lean_object* v___x_3501_, lean_object* v___x_3502_, lean_object* v_snd_3503_, lean_object* v___x_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_){
_start:
{
lean_object* v___x_3513_; 
lean_inc(v___y_3511_);
lean_inc_ref(v___y_3510_);
lean_inc(v___y_3509_);
lean_inc_ref(v___y_3508_);
lean_inc(v___y_3507_);
lean_inc_ref(v___y_3506_);
v___x_3513_ = lean_apply_8(v___f_3498_, v___x_3499_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, lean_box(0));
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v___x_3515_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3514_);
lean_dec_ref_known(v___x_3513_, 1);
v___x_3515_ = l_Lean_Meta_mkProdMkN(v_a_3514_, v_u_3500_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v_fst_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_a_3516_);
lean_dec_ref_known(v___x_3515_, 1);
v_fst_3517_ = lean_ctor_get(v_a_3516_, 0);
lean_inc(v_fst_3517_);
lean_dec(v_a_3516_);
v___x_3518_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__7___closed__0));
v___x_3519_ = l_Lean_Name_mkStr2(v___x_3501_, v___x_3518_);
v___x_3520_ = l_Lean_mkConst(v___x_3519_, v___x_3502_);
v___x_3521_ = l_Lean_mkAppB(v___x_3520_, v_snd_3503_, v_fst_3517_);
v___x_3522_ = l_Lean_Elab_Do_mkPureApp(v___x_3504_, v___x_3521_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_);
return v___x_3522_;
}
else
{
lean_object* v_a_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3530_; 
lean_dec_ref(v___x_3504_);
lean_dec_ref(v_snd_3503_);
lean_dec(v___x_3502_);
lean_dec_ref(v___x_3501_);
v_a_3523_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3525_ = v___x_3515_;
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_a_3523_);
lean_dec(v___x_3515_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3528_; 
if (v_isShared_3526_ == 0)
{
v___x_3528_ = v___x_3525_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_a_3523_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
}
else
{
lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3538_; 
lean_dec_ref(v___x_3504_);
lean_dec_ref(v_snd_3503_);
lean_dec(v___x_3502_);
lean_dec_ref(v___x_3501_);
lean_dec(v_u_3500_);
v_a_3531_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3533_ = v___x_3513_;
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_dec(v___x_3513_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3536_; 
if (v_isShared_3534_ == 0)
{
v___x_3536_ = v___x_3533_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_a_3531_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__7___boxed(lean_object* v___f_3539_, lean_object* v___x_3540_, lean_object* v_u_3541_, lean_object* v___x_3542_, lean_object* v___x_3543_, lean_object* v_snd_3544_, lean_object* v___x_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l_Lean_Elab_Do_elabDoFor___lam__7(v___f_3539_, v___x_3540_, v_u_3541_, v___x_3542_, v___x_3543_, v_snd_3544_, v___x_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec(v___y_3548_);
lean_dec_ref(v___y_3547_);
lean_dec_ref(v___y_3546_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__8(lean_object* v___f_3555_, lean_object* v___x_3556_, lean_object* v_u_3557_, lean_object* v___x_3558_, lean_object* v___x_3559_, lean_object* v_snd_3560_, lean_object* v___x_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v___x_3570_; 
lean_inc(v___y_3568_);
lean_inc_ref(v___y_3567_);
lean_inc(v___y_3566_);
lean_inc_ref(v___y_3565_);
lean_inc(v___y_3564_);
lean_inc_ref(v___y_3563_);
v___x_3570_ = lean_apply_8(v___f_3555_, v___x_3556_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, lean_box(0));
if (lean_obj_tag(v___x_3570_) == 0)
{
lean_object* v_a_3571_; lean_object* v___x_3572_; 
v_a_3571_ = lean_ctor_get(v___x_3570_, 0);
lean_inc(v_a_3571_);
lean_dec_ref_known(v___x_3570_, 1);
v___x_3572_ = l_Lean_Meta_mkProdMkN(v_a_3571_, v_u_3557_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_);
if (lean_obj_tag(v___x_3572_) == 0)
{
lean_object* v_a_3573_; lean_object* v_fst_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
v_a_3573_ = lean_ctor_get(v___x_3572_, 0);
lean_inc(v_a_3573_);
lean_dec_ref_known(v___x_3572_, 1);
v_fst_3574_ = lean_ctor_get(v_a_3573_, 0);
lean_inc(v_fst_3574_);
lean_dec(v_a_3573_);
v___x_3575_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__6___closed__0));
v___x_3576_ = l_Lean_Name_mkStr2(v___x_3558_, v___x_3575_);
v___x_3577_ = l_Lean_mkConst(v___x_3576_, v___x_3559_);
v___x_3578_ = l_Lean_mkAppB(v___x_3577_, v_snd_3560_, v_fst_3574_);
v___x_3579_ = l_Lean_Elab_Do_mkPureApp(v___x_3561_, v___x_3578_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_);
return v___x_3579_;
}
else
{
lean_object* v_a_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3587_; 
lean_dec_ref(v___x_3561_);
lean_dec_ref(v_snd_3560_);
lean_dec(v___x_3559_);
lean_dec_ref(v___x_3558_);
v_a_3580_ = lean_ctor_get(v___x_3572_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3582_ = v___x_3572_;
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_a_3580_);
lean_dec(v___x_3572_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3585_; 
if (v_isShared_3583_ == 0)
{
v___x_3585_ = v___x_3582_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_a_3580_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
}
else
{
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3595_; 
lean_dec_ref(v___x_3561_);
lean_dec_ref(v_snd_3560_);
lean_dec(v___x_3559_);
lean_dec_ref(v___x_3558_);
lean_dec(v_u_3557_);
v_a_3588_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3590_ = v___x_3570_;
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3570_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3593_; 
if (v_isShared_3591_ == 0)
{
v___x_3593_ = v___x_3590_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_a_3588_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__8___boxed(lean_object* v___f_3596_, lean_object* v___x_3597_, lean_object* v_u_3598_, lean_object* v___x_3599_, lean_object* v___x_3600_, lean_object* v_snd_3601_, lean_object* v___x_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_){
_start:
{
lean_object* v_res_3611_; 
v_res_3611_ = l_Lean_Elab_Do_elabDoFor___lam__8(v___f_3596_, v___x_3597_, v_u_3598_, v___x_3599_, v___x_3600_, v_snd_3601_, v___x_3602_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_);
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
lean_dec(v___y_3605_);
lean_dec_ref(v___y_3604_);
lean_dec_ref(v___y_3603_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9(lean_object* v___x_3612_, lean_object* v___f_3613_, lean_object* v___f_3614_, lean_object* v___x_3615_, lean_object* v___x_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_){
_start:
{
lean_object* v_monadInfo_3625_; lean_object* v_mutVars_3626_; lean_object* v_mutVarDefs_3627_; lean_object* v_contInfo_3628_; uint8_t v_deadCode_3629_; lean_object* v_ops_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3638_; 
v_monadInfo_3625_ = lean_ctor_get(v___y_3617_, 0);
v_mutVars_3626_ = lean_ctor_get(v___y_3617_, 1);
v_mutVarDefs_3627_ = lean_ctor_get(v___y_3617_, 2);
v_contInfo_3628_ = lean_ctor_get(v___y_3617_, 4);
v_deadCode_3629_ = lean_ctor_get_uint8(v___y_3617_, sizeof(void*)*6);
v_ops_3630_ = lean_ctor_get(v___y_3617_, 5);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___y_3617_);
if (v_isSharedCheck_3638_ == 0)
{
lean_object* v_unused_3639_; 
v_unused_3639_ = lean_ctor_get(v___y_3617_, 3);
lean_dec(v_unused_3639_);
v___x_3632_ = v___y_3617_;
v_isShared_3633_ = v_isSharedCheck_3638_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_ops_3630_);
lean_inc(v_contInfo_3628_);
lean_inc(v_mutVarDefs_3627_);
lean_inc(v_mutVars_3626_);
lean_inc(v_monadInfo_3625_);
lean_dec(v___y_3617_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3638_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v___x_3635_; 
if (v_isShared_3633_ == 0)
{
lean_ctor_set(v___x_3632_, 3, v___x_3612_);
v___x_3635_ = v___x_3632_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_monadInfo_3625_);
lean_ctor_set(v_reuseFailAlloc_3637_, 1, v_mutVars_3626_);
lean_ctor_set(v_reuseFailAlloc_3637_, 2, v_mutVarDefs_3627_);
lean_ctor_set(v_reuseFailAlloc_3637_, 3, v___x_3612_);
lean_ctor_set(v_reuseFailAlloc_3637_, 4, v_contInfo_3628_);
lean_ctor_set(v_reuseFailAlloc_3637_, 5, v_ops_3630_);
lean_ctor_set_uint8(v_reuseFailAlloc_3637_, sizeof(void*)*6, v_deadCode_3629_);
v___x_3635_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
lean_object* v___x_3636_; 
v___x_3636_ = l_Lean_Elab_Do_enterLoopBody___redArg(v___f_3613_, v___f_3614_, v___x_3615_, v___x_3616_, v___x_3635_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_);
lean_dec_ref(v___x_3635_);
return v___x_3636_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9___boxed(lean_object* v___x_3640_, lean_object* v___f_3641_, lean_object* v___f_3642_, lean_object* v___x_3643_, lean_object* v___x_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_){
_start:
{
lean_object* v_res_3653_; 
v_res_3653_ = l_Lean_Elab_Do_elabDoFor___lam__9(v___x_3640_, v___f_3641_, v___f_3642_, v___x_3643_, v___x_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
lean_dec(v___y_3651_);
lean_dec_ref(v___y_3650_);
lean_dec(v___y_3649_);
lean_dec_ref(v___y_3648_);
lean_dec(v___y_3647_);
lean_dec_ref(v___y_3646_);
return v_res_3653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__10(lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_u_3659_, lean_object* v_snd_3660_, lean_object* v___f_3661_, lean_object* v___x_3662_, lean_object* v_body_3663_, uint8_t v___x_3664_, lean_object* v___y_3665_, lean_object* v_xh_3666_, lean_object* v_loopS_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_){
_start:
{
lean_object* v_resultType_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3713_; 
v_resultType_3676_ = lean_ctor_get(v_a_3657_, 0);
v_isSharedCheck_3713_ = !lean_is_exclusive(v_a_3657_);
if (v_isSharedCheck_3713_ == 0)
{
lean_object* v_unused_3714_; 
v_unused_3714_ = lean_ctor_get(v_a_3657_, 1);
lean_dec(v_unused_3714_);
v___x_3678_ = v_a_3657_;
v_isShared_3679_ = v_isSharedCheck_3713_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_resultType_3676_);
lean_dec(v_a_3657_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3713_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v_resultName_3680_; lean_object* v_resultType_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3711_; 
v_resultName_3680_ = lean_ctor_get(v_a_3658_, 0);
v_resultType_3681_ = lean_ctor_get(v_a_3658_, 1);
v_isSharedCheck_3711_ = !lean_is_exclusive(v_a_3658_);
if (v_isSharedCheck_3711_ == 0)
{
lean_object* v_unused_3712_; 
v_unused_3712_ = lean_ctor_get(v_a_3658_, 2);
lean_dec(v_unused_3712_);
v___x_3683_ = v_a_3658_;
v_isShared_3684_ = v_isSharedCheck_3711_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_resultType_3681_);
lean_inc(v_resultName_3680_);
lean_dec(v_a_3658_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3711_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___f_3692_; lean_object* v___f_3693_; lean_object* v___f_3694_; lean_object* v___x_3696_; 
v___x_3685_ = l_Lean_Expr_fvarId_x21(v_loopS_3667_);
v___x_3686_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__10___closed__0));
v___x_3687_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__10___closed__1));
v___x_3688_ = lean_box(0);
lean_inc_n(v_u_3659_, 3);
v___x_3689_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3689_, 0, v_u_3659_);
lean_ctor_set(v___x_3689_, 1, v___x_3688_);
lean_inc_ref_n(v___x_3689_, 3);
v___x_3690_ = l_Lean_mkConst(v___x_3687_, v___x_3689_);
lean_inc_ref_n(v_snd_3660_, 3);
v___x_3691_ = l_Lean_Expr_app___override(v___x_3690_, v_snd_3660_);
lean_inc_ref_n(v___x_3691_, 3);
lean_inc_ref_n(v___f_3661_, 2);
v___f_3692_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__6___boxed), 15, 6);
lean_closure_set(v___f_3692_, 0, v___f_3661_);
lean_closure_set(v___f_3692_, 1, v_u_3659_);
lean_closure_set(v___f_3692_, 2, v___x_3686_);
lean_closure_set(v___f_3692_, 3, v___x_3689_);
lean_closure_set(v___f_3692_, 4, v_snd_3660_);
lean_closure_set(v___f_3692_, 5, v___x_3691_);
lean_inc(v___x_3662_);
v___f_3693_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__7___boxed), 15, 7);
lean_closure_set(v___f_3693_, 0, v___f_3661_);
lean_closure_set(v___f_3693_, 1, v___x_3662_);
lean_closure_set(v___f_3693_, 2, v_u_3659_);
lean_closure_set(v___f_3693_, 3, v___x_3686_);
lean_closure_set(v___f_3693_, 4, v___x_3689_);
lean_closure_set(v___f_3693_, 5, v_snd_3660_);
lean_closure_set(v___f_3693_, 6, v___x_3691_);
v___f_3694_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__8___boxed), 15, 7);
lean_closure_set(v___f_3694_, 0, v___f_3661_);
lean_closure_set(v___f_3694_, 1, v___x_3662_);
lean_closure_set(v___f_3694_, 2, v_u_3659_);
lean_closure_set(v___f_3694_, 3, v___x_3686_);
lean_closure_set(v___f_3694_, 4, v___x_3689_);
lean_closure_set(v___f_3694_, 5, v_snd_3660_);
lean_closure_set(v___f_3694_, 6, v___x_3691_);
if (v_isShared_3679_ == 0)
{
lean_ctor_set(v___x_3678_, 1, v___f_3692_);
v___x_3696_ = v___x_3678_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_resultType_3676_);
lean_ctor_set(v_reuseFailAlloc_3710_, 1, v___f_3692_);
v___x_3696_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
uint8_t v___x_3697_; lean_object* v___x_3699_; 
v___x_3697_ = 1;
lean_inc_ref(v___f_3693_);
if (v_isShared_3684_ == 0)
{
lean_ctor_set(v___x_3683_, 2, v___f_3693_);
v___x_3699_ = v___x_3683_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_resultName_3680_);
lean_ctor_set(v_reuseFailAlloc_3709_, 1, v_resultType_3681_);
lean_ctor_set(v_reuseFailAlloc_3709_, 2, v___f_3693_);
v___x_3699_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___f_3702_; lean_object* v___x_3703_; 
lean_ctor_set_uint8(v___x_3699_, sizeof(void*)*3, v___x_3697_);
v___x_3700_ = lean_box(v___x_3664_);
v___x_3701_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoSeq___boxed), 11, 3);
lean_closure_set(v___x_3701_, 0, v_body_3663_);
lean_closure_set(v___x_3701_, 1, v___x_3699_);
lean_closure_set(v___x_3701_, 2, v___x_3700_);
v___f_3702_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__9___boxed), 13, 5);
lean_closure_set(v___f_3702_, 0, v___x_3691_);
lean_closure_set(v___f_3702_, 1, v___f_3694_);
lean_closure_set(v___f_3702_, 2, v___f_3693_);
lean_closure_set(v___f_3702_, 3, v___x_3696_);
lean_closure_set(v___f_3702_, 4, v___x_3701_);
v___x_3703_ = l_Lean_Elab_Do_bindMutVarsFromTuple(v___y_3665_, v___x_3685_, v___f_3702_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_);
if (lean_obj_tag(v___x_3703_) == 0)
{
lean_object* v_a_3704_; lean_object* v___x_3705_; uint8_t v___x_3706_; uint8_t v___x_3707_; lean_object* v___x_3708_; 
v_a_3704_ = lean_ctor_get(v___x_3703_, 0);
lean_inc(v_a_3704_);
lean_dec_ref_known(v___x_3703_, 1);
v___x_3705_ = lean_array_push(v_xh_3666_, v_loopS_3667_);
v___x_3706_ = 0;
v___x_3707_ = 1;
v___x_3708_ = l_Lean_Meta_mkLambdaFVars(v___x_3705_, v_a_3704_, v___x_3706_, v___x_3664_, v___x_3706_, v___x_3664_, v___x_3707_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_);
lean_dec_ref(v___x_3705_);
return v___x_3708_;
}
else
{
lean_dec_ref(v_loopS_3667_);
lean_dec_ref(v_xh_3666_);
return v___x_3703_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___boxed(lean_object** _args){
lean_object* v_a_3715_ = _args[0];
lean_object* v_a_3716_ = _args[1];
lean_object* v_u_3717_ = _args[2];
lean_object* v_snd_3718_ = _args[3];
lean_object* v___f_3719_ = _args[4];
lean_object* v___x_3720_ = _args[5];
lean_object* v_body_3721_ = _args[6];
lean_object* v___x_3722_ = _args[7];
lean_object* v___y_3723_ = _args[8];
lean_object* v_xh_3724_ = _args[9];
lean_object* v_loopS_3725_ = _args[10];
lean_object* v___y_3726_ = _args[11];
lean_object* v___y_3727_ = _args[12];
lean_object* v___y_3728_ = _args[13];
lean_object* v___y_3729_ = _args[14];
lean_object* v___y_3730_ = _args[15];
lean_object* v___y_3731_ = _args[16];
lean_object* v___y_3732_ = _args[17];
lean_object* v___y_3733_ = _args[18];
_start:
{
uint8_t v___x_75236__boxed_3734_; lean_object* v_res_3735_; 
v___x_75236__boxed_3734_ = lean_unbox(v___x_3722_);
v_res_3735_ = l_Lean_Elab_Do_elabDoFor___lam__10(v_a_3715_, v_a_3716_, v_u_3717_, v_snd_3718_, v___f_3719_, v___x_3720_, v_body_3721_, v___x_75236__boxed_3734_, v___y_3723_, v_xh_3724_, v_loopS_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
lean_dec(v___y_3732_);
lean_dec_ref(v___y_3731_);
lean_dec(v___y_3730_);
lean_dec_ref(v___y_3729_);
lean_dec(v___y_3728_);
lean_dec_ref(v___y_3727_);
lean_dec_ref(v___y_3726_);
return v_res_3735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__11(lean_object* v___x_3736_, lean_object* v___x_3737_, lean_object* v_x_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_, lean_object* v_u_3741_, lean_object* v_snd_3742_, lean_object* v___f_3743_, lean_object* v___x_3744_, lean_object* v_body_3745_, uint8_t v___x_3746_, lean_object* v___y_3747_, lean_object* v_a_3748_, lean_object* v_h_x3f_3749_, lean_object* v___x_3750_, lean_object* v_xh_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_){
_start:
{
lean_object* v___x_3760_; lean_object* v___x_3761_; 
v___x_3760_ = lean_array_get_borrowed(v___x_3736_, v_xh_3751_, v___x_3737_);
lean_inc(v___x_3760_);
v___x_3761_ = l_Lean_Elab_Term_addLocalVarInfo(v_x_3738_, v___x_3760_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
if (lean_obj_tag(v___x_3761_) == 0)
{
lean_object* v___x_3762_; lean_object* v___f_3763_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; 
lean_dec_ref_known(v___x_3761_, 1);
v___x_3762_ = lean_box(v___x_3746_);
lean_inc_ref(v_xh_3751_);
lean_inc_ref(v_snd_3742_);
v___f_3763_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__10___boxed), 19, 10);
lean_closure_set(v___f_3763_, 0, v_a_3739_);
lean_closure_set(v___f_3763_, 1, v_a_3740_);
lean_closure_set(v___f_3763_, 2, v_u_3741_);
lean_closure_set(v___f_3763_, 3, v_snd_3742_);
lean_closure_set(v___f_3763_, 4, v___f_3743_);
lean_closure_set(v___f_3763_, 5, v___x_3744_);
lean_closure_set(v___f_3763_, 6, v_body_3745_);
lean_closure_set(v___f_3763_, 7, v___x_3762_);
lean_closure_set(v___f_3763_, 8, v___y_3747_);
lean_closure_set(v___f_3763_, 9, v_xh_3751_);
if (lean_obj_tag(v_h_x3f_3749_) == 1)
{
lean_object* v_val_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; 
v_val_3775_ = lean_ctor_get(v_h_x3f_3749_, 0);
lean_inc(v_val_3775_);
lean_dec_ref_known(v_h_x3f_3749_, 1);
v___x_3776_ = lean_array_get(v___x_3736_, v_xh_3751_, v___x_3750_);
lean_dec_ref(v_xh_3751_);
v___x_3777_ = l_Lean_Elab_Term_addLocalVarInfo(v_val_3775_, v___x_3776_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
if (lean_obj_tag(v___x_3777_) == 0)
{
lean_dec_ref_known(v___x_3777_, 1);
v___y_3765_ = v___y_3752_;
v___y_3766_ = v___y_3753_;
v___y_3767_ = v___y_3754_;
v___y_3768_ = v___y_3755_;
v___y_3769_ = v___y_3756_;
v___y_3770_ = v___y_3757_;
v___y_3771_ = v___y_3758_;
goto v___jp_3764_;
}
else
{
lean_object* v_a_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3785_; 
lean_dec_ref(v___f_3763_);
lean_dec(v_a_3748_);
lean_dec_ref(v_snd_3742_);
v_a_3778_ = lean_ctor_get(v___x_3777_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v___x_3777_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3780_ = v___x_3777_;
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_a_3778_);
lean_dec(v___x_3777_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3783_; 
if (v_isShared_3781_ == 0)
{
v___x_3783_ = v___x_3780_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v_a_3778_);
v___x_3783_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
return v___x_3783_;
}
}
}
}
else
{
lean_dec_ref(v_xh_3751_);
lean_dec(v_h_x3f_3749_);
v___y_3765_ = v___y_3752_;
v___y_3766_ = v___y_3753_;
v___y_3767_ = v___y_3754_;
v___y_3768_ = v___y_3755_;
v___y_3769_ = v___y_3756_;
v___y_3770_ = v___y_3757_;
v___y_3771_ = v___y_3758_;
goto v___jp_3764_;
}
v___jp_3764_:
{
uint8_t v___x_3772_; uint8_t v___x_3773_; lean_object* v___x_3774_; 
v___x_3772_ = 0;
v___x_3773_ = 1;
v___x_3774_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_a_3748_, v___x_3772_, v_snd_3742_, v___f_3763_, v___x_3773_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_);
return v___x_3774_;
}
}
else
{
lean_object* v_a_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3793_; 
lean_dec_ref(v_xh_3751_);
lean_dec(v_h_x3f_3749_);
lean_dec(v_a_3748_);
lean_dec(v___y_3747_);
lean_dec(v_body_3745_);
lean_dec(v___x_3744_);
lean_dec_ref(v___f_3743_);
lean_dec_ref(v_snd_3742_);
lean_dec(v_u_3741_);
lean_dec_ref(v_a_3740_);
lean_dec_ref(v_a_3739_);
v_a_3786_ = lean_ctor_get(v___x_3761_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3761_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3788_ = v___x_3761_;
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_a_3786_);
lean_dec(v___x_3761_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3791_; 
if (v_isShared_3789_ == 0)
{
v___x_3791_ = v___x_3788_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_a_3786_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__11___boxed(lean_object** _args){
lean_object* v___x_3794_ = _args[0];
lean_object* v___x_3795_ = _args[1];
lean_object* v_x_3796_ = _args[2];
lean_object* v_a_3797_ = _args[3];
lean_object* v_a_3798_ = _args[4];
lean_object* v_u_3799_ = _args[5];
lean_object* v_snd_3800_ = _args[6];
lean_object* v___f_3801_ = _args[7];
lean_object* v___x_3802_ = _args[8];
lean_object* v_body_3803_ = _args[9];
lean_object* v___x_3804_ = _args[10];
lean_object* v___y_3805_ = _args[11];
lean_object* v_a_3806_ = _args[12];
lean_object* v_h_x3f_3807_ = _args[13];
lean_object* v___x_3808_ = _args[14];
lean_object* v_xh_3809_ = _args[15];
lean_object* v___y_3810_ = _args[16];
lean_object* v___y_3811_ = _args[17];
lean_object* v___y_3812_ = _args[18];
lean_object* v___y_3813_ = _args[19];
lean_object* v___y_3814_ = _args[20];
lean_object* v___y_3815_ = _args[21];
lean_object* v___y_3816_ = _args[22];
lean_object* v___y_3817_ = _args[23];
_start:
{
uint8_t v___x_75359__boxed_3818_; lean_object* v_res_3819_; 
v___x_75359__boxed_3818_ = lean_unbox(v___x_3804_);
v_res_3819_ = l_Lean_Elab_Do_elabDoFor___lam__11(v___x_3794_, v___x_3795_, v_x_3796_, v_a_3797_, v_a_3798_, v_u_3799_, v_snd_3800_, v___f_3801_, v___x_3802_, v_body_3803_, v___x_75359__boxed_3818_, v___y_3805_, v_a_3806_, v_h_x3f_3807_, v___x_3808_, v_xh_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
lean_dec(v___y_3816_);
lean_dec_ref(v___y_3815_);
lean_dec(v___y_3814_);
lean_dec_ref(v___y_3813_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec_ref(v___y_3810_);
lean_dec(v___x_3808_);
lean_dec(v___x_3795_);
lean_dec_ref(v___x_3794_);
return v_res_3819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__12(lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v___x_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_, lean_object* v_val_3830_, lean_object* v_a_3831_, lean_object* v_x_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_){
_start:
{
lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
v___x_3841_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__12___closed__2));
v___x_3842_ = lean_box(0);
v___x_3843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3843_, 0, v_a_3825_);
lean_ctor_set(v___x_3843_, 1, v___x_3842_);
v___x_3844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3844_, 0, v_a_3826_);
lean_ctor_set(v___x_3844_, 1, v___x_3843_);
v___x_3845_ = l_Lean_mkConst(v___x_3841_, v___x_3844_);
v___x_3846_ = l_Lean_instInhabitedExpr;
v___x_3847_ = lean_array_get_borrowed(v___x_3846_, v_x_3832_, v___x_3827_);
lean_inc(v___x_3847_);
v___x_3848_ = l_Lean_mkApp5(v___x_3845_, v_a_3828_, v_a_3829_, v_val_3830_, v_a_3831_, v___x_3847_);
v___x_3849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3849_, 0, v___x_3848_);
return v___x_3849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__12___boxed(lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v___x_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_val_3855_, lean_object* v_a_3856_, lean_object* v_x_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_){
_start:
{
lean_object* v_res_3866_; 
v_res_3866_ = l_Lean_Elab_Do_elabDoFor___lam__12(v_a_3850_, v_a_3851_, v___x_3852_, v_a_3853_, v_a_3854_, v_val_3855_, v_a_3856_, v_x_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
lean_dec_ref(v___y_3858_);
lean_dec_ref(v_x_3857_);
lean_dec(v___x_3852_);
return v_res_3866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__5(size_t v_sz_3867_, size_t v_i_3868_, lean_object* v_bs_3869_){
_start:
{
uint8_t v___x_3870_; 
v___x_3870_ = lean_usize_dec_lt(v_i_3868_, v_sz_3867_);
if (v___x_3870_ == 0)
{
return v_bs_3869_;
}
else
{
lean_object* v_v_3871_; lean_object* v___x_3872_; lean_object* v_bs_x27_3873_; lean_object* v___x_3874_; size_t v___x_3875_; size_t v___x_3876_; lean_object* v___x_3877_; 
v_v_3871_ = lean_array_uget(v_bs_3869_, v_i_3868_);
v___x_3872_ = lean_unsigned_to_nat(0u);
v_bs_x27_3873_ = lean_array_uset(v_bs_3869_, v_i_3868_, v___x_3872_);
v___x_3874_ = l_Lean_Elab_Do_MutVar_getId(v_v_3871_);
lean_dec(v_v_3871_);
v___x_3875_ = ((size_t)1ULL);
v___x_3876_ = lean_usize_add(v_i_3868_, v___x_3875_);
v___x_3877_ = lean_array_uset(v_bs_x27_3873_, v_i_3868_, v___x_3874_);
v_i_3868_ = v___x_3876_;
v_bs_3869_ = v___x_3877_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__5___boxed(lean_object* v_sz_3879_, lean_object* v_i_3880_, lean_object* v_bs_3881_){
_start:
{
size_t v_sz_boxed_3882_; size_t v_i_boxed_3883_; lean_object* v_res_3884_; 
v_sz_boxed_3882_ = lean_unbox_usize(v_sz_3879_);
lean_dec(v_sz_3879_);
v_i_boxed_3883_ = lean_unbox_usize(v_i_3880_);
lean_dec(v_i_3880_);
v_res_3884_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__5(v_sz_boxed_3882_, v_i_boxed_3883_, v_bs_3881_);
return v_res_3884_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__6(lean_object* v_a_3885_, lean_object* v_as_3886_, size_t v_i_3887_, size_t v_stop_3888_, lean_object* v_b_3889_){
_start:
{
lean_object* v___y_3891_; uint8_t v___x_3895_; 
v___x_3895_ = lean_usize_dec_eq(v_i_3887_, v_stop_3888_);
if (v___x_3895_ == 0)
{
lean_object* v_reassigns_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; uint8_t v___x_3899_; 
v_reassigns_3896_ = lean_ctor_get(v_a_3885_, 1);
v___x_3897_ = lean_array_uget_borrowed(v_as_3886_, v_i_3887_);
v___x_3898_ = l_Lean_Elab_Do_MutVar_getId(v___x_3897_);
v___x_3899_ = l_Lean_NameSet_contains(v_reassigns_3896_, v___x_3898_);
lean_dec(v___x_3898_);
if (v___x_3899_ == 0)
{
v___y_3891_ = v_b_3889_;
goto v___jp_3890_;
}
else
{
lean_object* v___x_3900_; 
lean_inc(v___x_3897_);
v___x_3900_ = lean_array_push(v_b_3889_, v___x_3897_);
v___y_3891_ = v___x_3900_;
goto v___jp_3890_;
}
}
else
{
return v_b_3889_;
}
v___jp_3890_:
{
size_t v___x_3892_; size_t v___x_3893_; 
v___x_3892_ = ((size_t)1ULL);
v___x_3893_ = lean_usize_add(v_i_3887_, v___x_3892_);
v_i_3887_ = v___x_3893_;
v_b_3889_ = v___y_3891_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__6___boxed(lean_object* v_a_3901_, lean_object* v_as_3902_, lean_object* v_i_3903_, lean_object* v_stop_3904_, lean_object* v_b_3905_){
_start:
{
size_t v_i_boxed_3906_; size_t v_stop_boxed_3907_; lean_object* v_res_3908_; 
v_i_boxed_3906_ = lean_unbox_usize(v_i_3903_);
lean_dec(v_i_3903_);
v_stop_boxed_3907_ = lean_unbox_usize(v_stop_3904_);
lean_dec(v_stop_3904_);
v_res_3908_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__6(v_a_3901_, v_as_3902_, v_i_boxed_3906_, v_stop_boxed_3907_, v_b_3905_);
lean_dec_ref(v_as_3902_);
lean_dec_ref(v_a_3901_);
return v_res_3908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__0(lean_object* v___x_3909_, lean_object* v_a_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_){
_start:
{
lean_object* v___x_3919_; lean_object* v___x_73799__overap_3920_; lean_object* v___x_3921_; 
v___x_3919_ = l_Lean_instInhabitedExpr;
v___x_73799__overap_3920_ = l_instInhabitedOfMonad___redArg(v___x_3909_, v___x_3919_);
lean_inc(v___y_3917_);
lean_inc_ref(v___y_3916_);
lean_inc(v___y_3915_);
lean_inc_ref(v___y_3914_);
lean_inc(v___y_3913_);
lean_inc_ref(v___y_3912_);
lean_inc_ref(v___y_3911_);
v___x_3921_ = lean_apply_8(v___x_73799__overap_3920_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_, lean_box(0));
return v___x_3921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__0___boxed(lean_object* v___x_3922_, lean_object* v_a_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_){
_start:
{
lean_object* v_res_3932_; 
v_res_3932_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__0(v___x_3922_, v_a_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_);
lean_dec(v___y_3930_);
lean_dec_ref(v___y_3929_);
lean_dec(v___y_3928_);
lean_dec_ref(v___y_3927_);
lean_dec(v___y_3926_);
lean_dec_ref(v___y_3925_);
lean_dec_ref(v___y_3924_);
lean_dec_ref(v_a_3923_);
return v_res_3932_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__0(void){
_start:
{
lean_object* v___x_3933_; 
v___x_3933_ = l_instMonadEIO(lean_box(0));
return v___x_3933_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__1(void){
_start:
{
lean_object* v___x_3934_; lean_object* v___x_3935_; 
v___x_3934_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__0);
v___x_3935_ = l_StateRefT_x27_instMonad___redArg(v___x_3934_);
return v___x_3935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__1___boxed(lean_object* v_acc_3942_, lean_object* v_declInfos_3943_, lean_object* v_k_3944_, lean_object* v_kind_3945_, lean_object* v_x_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_){
_start:
{
uint8_t v_kind_boxed_3955_; lean_object* v_res_3956_; 
v_kind_boxed_3955_ = lean_unbox(v_kind_3945_);
v_res_3956_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__1(v_acc_3942_, v_declInfos_3943_, v_k_3944_, v_kind_boxed_3955_, v_x_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec_ref(v___y_3947_);
return v_res_3956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9(lean_object* v_declInfos_3957_, lean_object* v_k_3958_, uint8_t v_kind_3959_, lean_object* v_acc_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_){
_start:
{
lean_object* v___x_3969_; lean_object* v_toApplicative_3970_; lean_object* v_toFunctor_3971_; lean_object* v_toSeq_3972_; lean_object* v_toSeqLeft_3973_; lean_object* v_toSeqRight_3974_; lean_object* v___f_3975_; lean_object* v___f_3976_; lean_object* v___f_3977_; lean_object* v___f_3978_; lean_object* v___x_3979_; lean_object* v___f_3980_; lean_object* v___f_3981_; lean_object* v___f_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v_toApplicative_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_4066_; 
v___x_3969_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__1);
v_toApplicative_3970_ = lean_ctor_get(v___x_3969_, 0);
v_toFunctor_3971_ = lean_ctor_get(v_toApplicative_3970_, 0);
v_toSeq_3972_ = lean_ctor_get(v_toApplicative_3970_, 2);
v_toSeqLeft_3973_ = lean_ctor_get(v_toApplicative_3970_, 3);
v_toSeqRight_3974_ = lean_ctor_get(v_toApplicative_3970_, 4);
v___f_3975_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__2));
v___f_3976_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__3));
lean_inc_ref_n(v_toFunctor_3971_, 2);
v___f_3977_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3977_, 0, v_toFunctor_3971_);
v___f_3978_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3978_, 0, v_toFunctor_3971_);
v___x_3979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3979_, 0, v___f_3977_);
lean_ctor_set(v___x_3979_, 1, v___f_3978_);
lean_inc(v_toSeqRight_3974_);
v___f_3980_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3980_, 0, v_toSeqRight_3974_);
lean_inc(v_toSeqLeft_3973_);
v___f_3981_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3981_, 0, v_toSeqLeft_3973_);
lean_inc(v_toSeq_3972_);
v___f_3982_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3982_, 0, v_toSeq_3972_);
v___x_3983_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3983_, 0, v___x_3979_);
lean_ctor_set(v___x_3983_, 1, v___f_3975_);
lean_ctor_set(v___x_3983_, 2, v___f_3982_);
lean_ctor_set(v___x_3983_, 3, v___f_3981_);
lean_ctor_set(v___x_3983_, 4, v___f_3980_);
v___x_3984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3984_, 0, v___x_3983_);
lean_ctor_set(v___x_3984_, 1, v___f_3976_);
v___x_3985_ = l_StateRefT_x27_instMonad___redArg(v___x_3984_);
v_toApplicative_3986_ = lean_ctor_get(v___x_3985_, 0);
v_isSharedCheck_4066_ = !lean_is_exclusive(v___x_3985_);
if (v_isSharedCheck_4066_ == 0)
{
lean_object* v_unused_4067_; 
v_unused_4067_ = lean_ctor_get(v___x_3985_, 1);
lean_dec(v_unused_4067_);
v___x_3988_ = v___x_3985_;
v_isShared_3989_ = v_isSharedCheck_4066_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_toApplicative_3986_);
lean_dec(v___x_3985_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_4066_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v_toFunctor_3990_; lean_object* v_toSeq_3991_; lean_object* v_toSeqLeft_3992_; lean_object* v_toSeqRight_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4064_; 
v_toFunctor_3990_ = lean_ctor_get(v_toApplicative_3986_, 0);
v_toSeq_3991_ = lean_ctor_get(v_toApplicative_3986_, 2);
v_toSeqLeft_3992_ = lean_ctor_get(v_toApplicative_3986_, 3);
v_toSeqRight_3993_ = lean_ctor_get(v_toApplicative_3986_, 4);
v_isSharedCheck_4064_ = !lean_is_exclusive(v_toApplicative_3986_);
if (v_isSharedCheck_4064_ == 0)
{
lean_object* v_unused_4065_; 
v_unused_4065_ = lean_ctor_get(v_toApplicative_3986_, 1);
lean_dec(v_unused_4065_);
v___x_3995_ = v_toApplicative_3986_;
v_isShared_3996_ = v_isSharedCheck_4064_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_toSeqRight_3993_);
lean_inc(v_toSeqLeft_3992_);
lean_inc(v_toSeq_3991_);
lean_inc(v_toFunctor_3990_);
lean_dec(v_toApplicative_3986_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4064_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___f_3997_; lean_object* v___f_3998_; lean_object* v___f_3999_; lean_object* v___f_4000_; lean_object* v___x_4001_; lean_object* v___f_4002_; lean_object* v___f_4003_; lean_object* v___f_4004_; lean_object* v___x_4006_; 
v___f_3997_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__4));
v___f_3998_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__5));
lean_inc_ref(v_toFunctor_3990_);
v___f_3999_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3999_, 0, v_toFunctor_3990_);
v___f_4000_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4000_, 0, v_toFunctor_3990_);
v___x_4001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4001_, 0, v___f_3999_);
lean_ctor_set(v___x_4001_, 1, v___f_4000_);
v___f_4002_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4002_, 0, v_toSeqRight_3993_);
v___f_4003_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4003_, 0, v_toSeqLeft_3992_);
v___f_4004_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4004_, 0, v_toSeq_3991_);
if (v_isShared_3996_ == 0)
{
lean_ctor_set(v___x_3995_, 4, v___f_4002_);
lean_ctor_set(v___x_3995_, 3, v___f_4003_);
lean_ctor_set(v___x_3995_, 2, v___f_4004_);
lean_ctor_set(v___x_3995_, 1, v___f_3997_);
lean_ctor_set(v___x_3995_, 0, v___x_4001_);
v___x_4006_ = v___x_3995_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v___x_4001_);
lean_ctor_set(v_reuseFailAlloc_4063_, 1, v___f_3997_);
lean_ctor_set(v_reuseFailAlloc_4063_, 2, v___f_4004_);
lean_ctor_set(v_reuseFailAlloc_4063_, 3, v___f_4003_);
lean_ctor_set(v_reuseFailAlloc_4063_, 4, v___f_4002_);
v___x_4006_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
lean_object* v___x_4008_; 
if (v_isShared_3989_ == 0)
{
lean_ctor_set(v___x_3988_, 1, v___f_3998_);
lean_ctor_set(v___x_3988_, 0, v___x_4006_);
v___x_4008_ = v___x_3988_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v___x_4006_);
lean_ctor_set(v_reuseFailAlloc_4062_, 1, v___f_3998_);
v___x_4008_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
lean_object* v___x_4009_; lean_object* v_toApplicative_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4060_; 
v___x_4009_ = l_StateRefT_x27_instMonad___redArg(v___x_4008_);
v_toApplicative_4010_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4060_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4060_ == 0)
{
lean_object* v_unused_4061_; 
v_unused_4061_ = lean_ctor_get(v___x_4009_, 1);
lean_dec(v_unused_4061_);
v___x_4012_ = v___x_4009_;
v_isShared_4013_ = v_isSharedCheck_4060_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_toApplicative_4010_);
lean_dec(v___x_4009_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4060_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v_toFunctor_4014_; lean_object* v_toSeq_4015_; lean_object* v_toSeqLeft_4016_; lean_object* v_toSeqRight_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4058_; 
v_toFunctor_4014_ = lean_ctor_get(v_toApplicative_4010_, 0);
v_toSeq_4015_ = lean_ctor_get(v_toApplicative_4010_, 2);
v_toSeqLeft_4016_ = lean_ctor_get(v_toApplicative_4010_, 3);
v_toSeqRight_4017_ = lean_ctor_get(v_toApplicative_4010_, 4);
v_isSharedCheck_4058_ = !lean_is_exclusive(v_toApplicative_4010_);
if (v_isSharedCheck_4058_ == 0)
{
lean_object* v_unused_4059_; 
v_unused_4059_ = lean_ctor_get(v_toApplicative_4010_, 1);
lean_dec(v_unused_4059_);
v___x_4019_ = v_toApplicative_4010_;
v_isShared_4020_ = v_isSharedCheck_4058_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_toSeqRight_4017_);
lean_inc(v_toSeqLeft_4016_);
lean_inc(v_toSeq_4015_);
lean_inc(v_toFunctor_4014_);
lean_dec(v_toApplicative_4010_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4058_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___f_4021_; lean_object* v___f_4022_; lean_object* v___f_4023_; lean_object* v___f_4024_; lean_object* v___x_4025_; lean_object* v___f_4026_; lean_object* v___f_4027_; lean_object* v___f_4028_; lean_object* v___x_4030_; 
v___f_4021_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__6));
v___f_4022_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___closed__7));
lean_inc_ref(v_toFunctor_4014_);
v___f_4023_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4023_, 0, v_toFunctor_4014_);
v___f_4024_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4024_, 0, v_toFunctor_4014_);
v___x_4025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4025_, 0, v___f_4023_);
lean_ctor_set(v___x_4025_, 1, v___f_4024_);
v___f_4026_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4026_, 0, v_toSeqRight_4017_);
v___f_4027_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4027_, 0, v_toSeqLeft_4016_);
v___f_4028_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4028_, 0, v_toSeq_4015_);
if (v_isShared_4020_ == 0)
{
lean_ctor_set(v___x_4019_, 4, v___f_4026_);
lean_ctor_set(v___x_4019_, 3, v___f_4027_);
lean_ctor_set(v___x_4019_, 2, v___f_4028_);
lean_ctor_set(v___x_4019_, 1, v___f_4021_);
lean_ctor_set(v___x_4019_, 0, v___x_4025_);
v___x_4030_ = v___x_4019_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v___x_4025_);
lean_ctor_set(v_reuseFailAlloc_4057_, 1, v___f_4021_);
lean_ctor_set(v_reuseFailAlloc_4057_, 2, v___f_4028_);
lean_ctor_set(v_reuseFailAlloc_4057_, 3, v___f_4027_);
lean_ctor_set(v_reuseFailAlloc_4057_, 4, v___f_4026_);
v___x_4030_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
lean_object* v___x_4032_; 
if (v_isShared_4013_ == 0)
{
lean_ctor_set(v___x_4012_, 1, v___f_4022_);
lean_ctor_set(v___x_4012_, 0, v___x_4030_);
v___x_4032_ = v___x_4012_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v___x_4030_);
lean_ctor_set(v_reuseFailAlloc_4056_, 1, v___f_4022_);
v___x_4032_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; uint8_t v___x_4036_; 
v___x_4033_ = l_ReaderT_instMonad___redArg(v___x_4032_);
v___x_4034_ = lean_array_get_size(v_acc_3960_);
v___x_4035_ = lean_array_get_size(v_declInfos_3957_);
v___x_4036_ = lean_nat_dec_lt(v___x_4034_, v___x_4035_);
if (v___x_4036_ == 0)
{
lean_object* v___x_4037_; 
lean_dec_ref(v___x_4033_);
lean_dec_ref(v_declInfos_3957_);
lean_inc(v___y_3967_);
lean_inc_ref(v___y_3966_);
lean_inc(v___y_3965_);
lean_inc_ref(v___y_3964_);
lean_inc(v___y_3963_);
lean_inc_ref(v___y_3962_);
lean_inc_ref(v___y_3961_);
v___x_4037_ = lean_apply_9(v_k_3958_, v_acc_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, lean_box(0));
return v___x_4037_;
}
else
{
lean_object* v___f_4038_; lean_object* v___x_4039_; uint8_t v___x_4040_; lean_object* v___f_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v_snd_4046_; lean_object* v_fst_4047_; lean_object* v_fst_4048_; lean_object* v_snd_4049_; lean_object* v___x_4050_; 
v___f_4038_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__0___boxed), 10, 1);
lean_closure_set(v___f_4038_, 0, v___x_4033_);
v___x_4039_ = lean_box(0);
v___x_4040_ = 0;
v___f_4041_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_4041_, 0, v___f_4038_);
v___x_4042_ = lean_box(v___x_4040_);
v___x_4043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4043_, 0, v___x_4042_);
lean_ctor_set(v___x_4043_, 1, v___f_4041_);
v___x_4044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4044_, 0, v___x_4039_);
lean_ctor_set(v___x_4044_, 1, v___x_4043_);
v___x_4045_ = lean_array_get(v___x_4044_, v_declInfos_3957_, v___x_4034_);
lean_dec_ref_known(v___x_4044_, 2);
v_snd_4046_ = lean_ctor_get(v___x_4045_, 1);
lean_inc(v_snd_4046_);
v_fst_4047_ = lean_ctor_get(v___x_4045_, 0);
lean_inc(v_fst_4047_);
lean_dec(v___x_4045_);
v_fst_4048_ = lean_ctor_get(v_snd_4046_, 0);
lean_inc(v_fst_4048_);
v_snd_4049_ = lean_ctor_get(v_snd_4046_, 1);
lean_inc(v_snd_4049_);
lean_dec(v_snd_4046_);
lean_inc(v___y_3967_);
lean_inc_ref(v___y_3966_);
lean_inc(v___y_3965_);
lean_inc_ref(v___y_3964_);
lean_inc(v___y_3963_);
lean_inc_ref(v___y_3962_);
lean_inc_ref(v___y_3961_);
lean_inc_ref(v_acc_3960_);
v___x_4050_ = lean_apply_9(v_snd_4049_, v_acc_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, lean_box(0));
if (lean_obj_tag(v___x_4050_) == 0)
{
lean_object* v_a_4051_; lean_object* v___x_4052_; lean_object* v___f_4053_; uint8_t v___x_4054_; lean_object* v___x_4055_; 
v_a_4051_ = lean_ctor_get(v___x_4050_, 0);
lean_inc(v_a_4051_);
lean_dec_ref_known(v___x_4050_, 1);
v___x_4052_ = lean_box(v_kind_3959_);
v___f_4053_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__1___boxed), 13, 4);
lean_closure_set(v___f_4053_, 0, v_acc_3960_);
lean_closure_set(v___f_4053_, 1, v_declInfos_3957_);
lean_closure_set(v___f_4053_, 2, v_k_3958_);
lean_closure_set(v___f_4053_, 3, v___x_4052_);
v___x_4054_ = lean_unbox(v_fst_4048_);
lean_dec(v_fst_4048_);
v___x_4055_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_fst_4047_, v___x_4054_, v_a_4051_, v___f_4053_, v_kind_3959_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_);
return v___x_4055_;
}
else
{
lean_dec(v_fst_4048_);
lean_dec(v_fst_4047_);
lean_dec_ref(v_acc_3960_);
lean_dec_ref(v_k_3958_);
lean_dec_ref(v_declInfos_3957_);
return v___x_4050_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___lam__1(lean_object* v_acc_4068_, lean_object* v_declInfos_4069_, lean_object* v_k_4070_, uint8_t v_kind_4071_, lean_object* v_x_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_){
_start:
{
lean_object* v___x_4081_; lean_object* v___x_4082_; 
v___x_4081_ = lean_array_push(v_acc_4068_, v_x_4072_);
v___x_4082_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9(v_declInfos_4069_, v_k_4070_, v_kind_4071_, v___x_4081_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_);
return v___x_4082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9___boxed(lean_object* v_declInfos_4083_, lean_object* v_k_4084_, lean_object* v_kind_4085_, lean_object* v_acc_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_){
_start:
{
uint8_t v_kind_boxed_4095_; lean_object* v_res_4096_; 
v_kind_boxed_4095_ = lean_unbox(v_kind_4085_);
v_res_4096_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9(v_declInfos_4083_, v_k_4084_, v_kind_boxed_4095_, v_acc_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_);
lean_dec(v___y_4093_);
lean_dec_ref(v___y_4092_);
lean_dec(v___y_4091_);
lean_dec_ref(v___y_4090_);
lean_dec(v___y_4089_);
lean_dec_ref(v___y_4088_);
lean_dec_ref(v___y_4087_);
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(lean_object* v_declInfos_4099_, lean_object* v_k_4100_, uint8_t v_kind_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_){
_start:
{
lean_object* v___x_4110_; lean_object* v___x_4111_; 
v___x_4110_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6___closed__0));
v___x_4111_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__9(v_declInfos_4099_, v_k_4100_, v_kind_4101_, v___x_4110_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
return v___x_4111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6___boxed(lean_object* v_declInfos_4112_, lean_object* v_k_4113_, lean_object* v_kind_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_){
_start:
{
uint8_t v_kind_boxed_4123_; lean_object* v_res_4124_; 
v_kind_boxed_4123_ = lean_unbox(v_kind_4114_);
v_res_4124_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(v_declInfos_4112_, v_k_4113_, v_kind_boxed_4123_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_);
lean_dec(v___y_4121_);
lean_dec_ref(v___y_4120_);
lean_dec(v___y_4119_);
lean_dec_ref(v___y_4118_);
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4116_);
lean_dec_ref(v___y_4115_);
return v_res_4124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__5(size_t v_sz_4125_, size_t v_i_4126_, lean_object* v_bs_4127_){
_start:
{
uint8_t v___x_4128_; 
v___x_4128_ = lean_usize_dec_lt(v_i_4126_, v_sz_4125_);
if (v___x_4128_ == 0)
{
return v_bs_4127_;
}
else
{
lean_object* v_v_4129_; lean_object* v_fst_4130_; lean_object* v_snd_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4147_; 
v_v_4129_ = lean_array_uget(v_bs_4127_, v_i_4126_);
v_fst_4130_ = lean_ctor_get(v_v_4129_, 0);
v_snd_4131_ = lean_ctor_get(v_v_4129_, 1);
v_isSharedCheck_4147_ = !lean_is_exclusive(v_v_4129_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4133_ = v_v_4129_;
v_isShared_4134_ = v_isSharedCheck_4147_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_snd_4131_);
lean_inc(v_fst_4130_);
lean_dec(v_v_4129_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4147_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v___x_4135_; lean_object* v_bs_x27_4136_; uint8_t v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4140_; 
v___x_4135_ = lean_unsigned_to_nat(0u);
v_bs_x27_4136_ = lean_array_uset(v_bs_4127_, v_i_4126_, v___x_4135_);
v___x_4137_ = 0;
v___x_4138_ = lean_box(v___x_4137_);
if (v_isShared_4134_ == 0)
{
lean_ctor_set(v___x_4133_, 0, v___x_4138_);
v___x_4140_ = v___x_4133_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v___x_4138_);
lean_ctor_set(v_reuseFailAlloc_4146_, 1, v_snd_4131_);
v___x_4140_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
lean_object* v___x_4141_; size_t v___x_4142_; size_t v___x_4143_; lean_object* v___x_4144_; 
v___x_4141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4141_, 0, v_fst_4130_);
lean_ctor_set(v___x_4141_, 1, v___x_4140_);
v___x_4142_ = ((size_t)1ULL);
v___x_4143_ = lean_usize_add(v_i_4126_, v___x_4142_);
v___x_4144_ = lean_array_uset(v_bs_x27_4136_, v_i_4126_, v___x_4141_);
v_i_4126_ = v___x_4143_;
v_bs_4127_ = v___x_4144_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__5___boxed(lean_object* v_sz_4148_, lean_object* v_i_4149_, lean_object* v_bs_4150_){
_start:
{
size_t v_sz_boxed_4151_; size_t v_i_boxed_4152_; lean_object* v_res_4153_; 
v_sz_boxed_4151_ = lean_unbox_usize(v_sz_4148_);
lean_dec(v_sz_4148_);
v_i_boxed_4152_ = lean_unbox_usize(v_i_4149_);
lean_dec(v_i_4149_);
v_res_4153_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__5(v_sz_boxed_4151_, v_i_boxed_4152_, v_bs_4150_);
return v_res_4153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(lean_object* v_declInfos_4154_, lean_object* v_k_4155_, uint8_t v_kind_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_){
_start:
{
size_t v_sz_4165_; size_t v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; 
v_sz_4165_ = lean_array_size(v_declInfos_4154_);
v___x_4166_ = ((size_t)0ULL);
v___x_4167_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__5(v_sz_4165_, v___x_4166_, v_declInfos_4154_);
v___x_4168_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(v___x_4167_, v_k_4155_, v_kind_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_);
return v___x_4168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4___boxed(lean_object* v_declInfos_4169_, lean_object* v_k_4170_, lean_object* v_kind_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_){
_start:
{
uint8_t v_kind_boxed_4180_; lean_object* v_res_4181_; 
v_kind_boxed_4180_ = lean_unbox(v_kind_4171_);
v_res_4181_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(v_declInfos_4169_, v_k_4170_, v_kind_boxed_4180_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_);
lean_dec(v___y_4178_);
lean_dec_ref(v___y_4177_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
lean_dec_ref(v___y_4172_);
return v_res_4181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor(lean_object* v_stx_4210_, lean_object* v_dec_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_){
_start:
{
lean_object* v___x_4220_; uint8_t v___x_4221_; 
v___x_4220_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
lean_inc(v_stx_4210_);
v___x_4221_ = l_Lean_Syntax_isOfKind(v_stx_4210_, v___x_4220_);
if (v___x_4221_ == 0)
{
lean_object* v___x_4222_; 
lean_dec_ref(v_dec_4211_);
lean_dec(v_stx_4210_);
v___x_4222_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v___x_4222_;
}
else
{
lean_object* v___x_4223_; lean_object* v___x_4224_; uint8_t v___x_4225_; 
v___x_4223_ = lean_unsigned_to_nat(1u);
v___x_4224_ = l_Lean_Syntax_getArg(v_stx_4210_, v___x_4223_);
lean_inc(v___x_4224_);
v___x_4225_ = l_Lean_Syntax_matchesNull(v___x_4224_, v___x_4223_);
if (v___x_4225_ == 0)
{
lean_object* v___x_4226_; 
lean_dec(v___x_4224_);
lean_dec_ref(v_dec_4211_);
lean_dec(v_stx_4210_);
v___x_4226_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v___x_4226_;
}
else
{
lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; uint8_t v___x_4230_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v___y_4234_; lean_object* v___y_4235_; uint8_t v___y_4236_; lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v_forIn_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; uint8_t v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; uint8_t v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4293_; uint8_t v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v___y_4305_; lean_object* v___y_4306_; lean_object* v___y_4307_; lean_object* v___y_4308_; lean_object* v___y_4309_; lean_object* v___y_4310_; lean_object* v___y_4311_; lean_object* v___y_4312_; lean_object* v___y_4313_; lean_object* v___y_4314_; lean_object* v___y_4315_; uint8_t v___y_4316_; lean_object* v___y_4317_; lean_object* v___y_4318_; lean_object* v___y_4319_; lean_object* v___y_4320_; lean_object* v___y_4321_; lean_object* v___y_4322_; lean_object* v___y_4323_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; uint8_t v___y_4350_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4354_; lean_object* v___y_4355_; lean_object* v___y_4356_; lean_object* v___y_4357_; lean_object* v___y_4358_; lean_object* v___y_4359_; lean_object* v___y_4360_; lean_object* v___y_4361_; lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v___y_4364_; lean_object* v___y_4365_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4369_; lean_object* v___y_4370_; uint8_t v___y_4371_; lean_object* v___y_4372_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v_fst_4377_; lean_object* v_snd_4378_; lean_object* v___y_4379_; lean_object* v___y_4380_; lean_object* v___y_4381_; lean_object* v___y_4382_; lean_object* v___y_4383_; lean_object* v___y_4384_; lean_object* v___y_4385_; lean_object* v___y_4412_; lean_object* v___y_4413_; lean_object* v___y_4414_; lean_object* v___y_4415_; lean_object* v___y_4416_; uint8_t v___y_4417_; lean_object* v___y_4418_; lean_object* v___y_4419_; lean_object* v___y_4420_; lean_object* v___y_4421_; lean_object* v___y_4422_; lean_object* v___y_4423_; lean_object* v___y_4424_; lean_object* v___y_4425_; lean_object* v___y_4426_; lean_object* v___y_4427_; lean_object* v___y_4428_; lean_object* v___y_4429_; lean_object* v___y_4430_; lean_object* v___y_4431_; lean_object* v___y_4432_; lean_object* v___y_4433_; lean_object* v___y_4434_; lean_object* v___y_4435_; lean_object* v___y_4436_; lean_object* v___y_4437_; lean_object* v___y_4438_; lean_object* v___y_4439_; lean_object* v___y_4440_; lean_object* v___y_4441_; lean_object* v___y_4442_; lean_object* v___y_4443_; uint8_t v___y_4444_; lean_object* v___y_4445_; lean_object* v___y_4446_; lean_object* v___y_4447_; lean_object* v___y_4448_; lean_object* v___y_4532_; uint8_t v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4535_; lean_object* v___y_4536_; lean_object* v___y_4537_; lean_object* v___y_4538_; lean_object* v___y_4539_; lean_object* v___y_4540_; lean_object* v___y_4541_; lean_object* v___y_4542_; lean_object* v___y_4543_; lean_object* v___y_4544_; lean_object* v___y_4545_; lean_object* v___y_4546_; lean_object* v___y_4547_; lean_object* v___y_4548_; lean_object* v___y_4549_; lean_object* v___y_4550_; lean_object* v___y_4551_; lean_object* v___y_4552_; lean_object* v___y_4553_; lean_object* v___y_4554_; lean_object* v___y_4555_; lean_object* v___y_4556_; lean_object* v___y_4557_; lean_object* v___y_4558_; lean_object* v___y_4559_; lean_object* v___y_4560_; lean_object* v___y_4561_; lean_object* v___y_4562_; uint8_t v___y_4563_; lean_object* v___y_4564_; lean_object* v___y_4565_; lean_object* v___y_4566_; lean_object* v___y_4567_; 
v___x_4227_ = lean_unsigned_to_nat(0u);
v___x_4228_ = l_Lean_Syntax_getArg(v___x_4224_, v___x_4227_);
lean_dec(v___x_4224_);
v___x_4229_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
lean_inc(v___x_4228_);
v___x_4230_ = l_Lean_Syntax_isOfKind(v___x_4228_, v___x_4229_);
if (v___x_4230_ == 0)
{
lean_object* v___x_4581_; 
lean_dec(v___x_4228_);
lean_dec_ref(v_dec_4211_);
lean_dec(v_stx_4210_);
v___x_4581_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v___x_4581_;
}
else
{
lean_object* v_tk_4582_; uint8_t v___y_4584_; lean_object* v___y_4585_; lean_object* v___y_4586_; lean_object* v___y_4587_; lean_object* v___y_4588_; lean_object* v___y_4589_; lean_object* v___y_4590_; lean_object* v_inv_x3f_4591_; lean_object* v___y_4592_; lean_object* v___y_4593_; lean_object* v___y_4594_; lean_object* v___y_4595_; lean_object* v___y_4596_; lean_object* v___y_4597_; lean_object* v___y_4598_; lean_object* v_h_x3f_4719_; lean_object* v___y_4720_; lean_object* v___y_4721_; lean_object* v___y_4722_; lean_object* v___y_4723_; lean_object* v___y_4724_; lean_object* v___y_4725_; lean_object* v___y_4726_; lean_object* v___x_4744_; uint8_t v___x_4745_; 
v_tk_4582_ = l_Lean_Syntax_getArg(v_stx_4210_, v___x_4227_);
v___x_4744_ = l_Lean_Syntax_getArg(v___x_4228_, v___x_4227_);
v___x_4745_ = l_Lean_Syntax_isNone(v___x_4744_);
if (v___x_4745_ == 0)
{
lean_object* v___x_4746_; uint8_t v___x_4747_; 
v___x_4746_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_4744_);
v___x_4747_ = l_Lean_Syntax_matchesNull(v___x_4744_, v___x_4746_);
if (v___x_4747_ == 0)
{
lean_object* v___x_4748_; 
lean_dec(v___x_4744_);
lean_dec(v_tk_4582_);
lean_dec(v___x_4228_);
lean_dec_ref(v_dec_4211_);
lean_dec(v_stx_4210_);
v___x_4748_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v___x_4748_;
}
else
{
lean_object* v_h_x3f_4749_; lean_object* v___x_4750_; 
v_h_x3f_4749_ = l_Lean_Syntax_getArg(v___x_4744_, v___x_4227_);
lean_dec(v___x_4744_);
v___x_4750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4750_, 0, v_h_x3f_4749_);
v_h_x3f_4719_ = v___x_4750_;
v___y_4720_ = v_a_4212_;
v___y_4721_ = v_a_4213_;
v___y_4722_ = v_a_4214_;
v___y_4723_ = v_a_4215_;
v___y_4724_ = v_a_4216_;
v___y_4725_ = v_a_4217_;
v___y_4726_ = v_a_4218_;
goto v___jp_4718_;
}
}
else
{
lean_object* v___x_4751_; 
lean_dec(v___x_4744_);
v___x_4751_ = lean_box(0);
v_h_x3f_4719_ = v___x_4751_;
v___y_4720_ = v_a_4212_;
v___y_4721_ = v_a_4213_;
v___y_4722_ = v_a_4214_;
v___y_4723_ = v_a_4215_;
v___y_4724_ = v_a_4216_;
v___y_4725_ = v_a_4217_;
v___y_4726_ = v_a_4218_;
goto v___jp_4718_;
}
v___jp_4583_:
{
lean_object* v___x_4599_; 
v___x_4599_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_4211_, v_tk_4582_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_);
lean_dec(v_tk_4582_);
if (lean_obj_tag(v___x_4599_) == 0)
{
lean_object* v_a_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; 
v_a_4600_ = lean_ctor_get(v___x_4599_, 0);
lean_inc(v_a_4600_);
lean_dec_ref_known(v___x_4599_, 1);
v___x_4601_ = lean_mk_empty_array_with_capacity(v___x_4223_);
lean_inc(v___y_4590_);
v___x_4602_ = lean_array_push(v___x_4601_, v___y_4590_);
v___x_4603_ = l_Lean_Elab_Do_checkMutVarsForShadowing(v___x_4602_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_);
lean_dec_ref(v___x_4602_);
if (lean_obj_tag(v___x_4603_) == 0)
{
lean_object* v___x_4604_; 
lean_dec_ref_known(v___x_4603_, 1);
v___x_4604_ = l_Lean_Meta_mkFreshLevelMVar(v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_);
if (lean_obj_tag(v___x_4604_) == 0)
{
lean_object* v_a_4605_; lean_object* v___x_4606_; 
v_a_4605_ = lean_ctor_get(v___x_4604_, 0);
lean_inc(v_a_4605_);
lean_dec_ref_known(v___x_4604_, 1);
v___x_4606_ = l_Lean_Meta_mkFreshLevelMVar(v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_);
if (lean_obj_tag(v___x_4606_) == 0)
{
lean_object* v_a_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; uint8_t v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; 
v_a_4607_ = lean_ctor_get(v___x_4606_, 0);
lean_inc(v_a_4607_);
lean_dec_ref_known(v___x_4606_, 1);
lean_inc(v_a_4605_);
v___x_4608_ = l_Lean_Level_succ___override(v_a_4605_);
v___x_4609_ = l_Lean_mkSort(v___x_4608_);
v___x_4610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4610_, 0, v___x_4609_);
v___x_4611_ = 0;
v___x_4612_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__10));
v___x_4613_ = l_Lean_Meta_mkFreshExprMVar(v___x_4610_, v___x_4611_, v___x_4612_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_);
if (lean_obj_tag(v___x_4613_) == 0)
{
lean_object* v_a_4614_; lean_object* v___x_4616_; uint8_t v_isShared_4617_; uint8_t v_isSharedCheck_4685_; 
v_a_4614_ = lean_ctor_get(v___x_4613_, 0);
v_isSharedCheck_4685_ = !lean_is_exclusive(v___x_4613_);
if (v_isSharedCheck_4685_ == 0)
{
v___x_4616_ = v___x_4613_;
v_isShared_4617_ = v_isSharedCheck_4685_;
goto v_resetjp_4615_;
}
else
{
lean_inc(v_a_4614_);
lean_dec(v___x_4613_);
v___x_4616_ = lean_box(0);
v_isShared_4617_ = v_isSharedCheck_4685_;
goto v_resetjp_4615_;
}
v_resetjp_4615_:
{
lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4621_; 
lean_inc(v_a_4607_);
v___x_4618_ = l_Lean_Level_succ___override(v_a_4607_);
v___x_4619_ = l_Lean_mkSort(v___x_4618_);
if (v_isShared_4617_ == 0)
{
lean_ctor_set_tag(v___x_4616_, 1);
lean_ctor_set(v___x_4616_, 0, v___x_4619_);
v___x_4621_ = v___x_4616_;
goto v_reusejp_4620_;
}
else
{
lean_object* v_reuseFailAlloc_4684_; 
v_reuseFailAlloc_4684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4684_, 0, v___x_4619_);
v___x_4621_ = v_reuseFailAlloc_4684_;
goto v_reusejp_4620_;
}
v_reusejp_4620_:
{
lean_object* v___x_4622_; lean_object* v___x_4623_; 
v___x_4622_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__12));
v___x_4623_ = l_Lean_Meta_mkFreshExprMVar(v___x_4621_, v___x_4611_, v___x_4622_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_);
if (lean_obj_tag(v___x_4623_) == 0)
{
lean_object* v_a_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4683_; 
v_a_4624_ = lean_ctor_get(v___x_4623_, 0);
v_isSharedCheck_4683_ = !lean_is_exclusive(v___x_4623_);
if (v_isSharedCheck_4683_ == 0)
{
v___x_4626_ = v___x_4623_;
v_isShared_4627_ = v_isSharedCheck_4683_;
goto v_resetjp_4625_;
}
else
{
lean_inc(v_a_4624_);
lean_dec(v___x_4623_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4683_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v___x_4629_; 
lean_inc(v_a_4624_);
if (v_isShared_4627_ == 0)
{
lean_ctor_set_tag(v___x_4626_, 1);
v___x_4629_ = v___x_4626_;
goto v_reusejp_4628_;
}
else
{
lean_object* v_reuseFailAlloc_4682_; 
v_reuseFailAlloc_4682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4682_, 0, v_a_4624_);
v___x_4629_ = v_reuseFailAlloc_4682_;
goto v_reusejp_4628_;
}
v_reusejp_4628_:
{
lean_object* v___x_4630_; lean_object* v___x_4631_; 
v___x_4630_ = lean_box(0);
v___x_4631_ = l_Lean_Elab_Term_elabTermEnsuringType(v___y_4589_, v___x_4629_, v___x_4230_, v___x_4230_, v___x_4630_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_);
if (lean_obj_tag(v___x_4631_) == 0)
{
lean_object* v_a_4632_; lean_object* v___x_4633_; lean_object* v_body_4634_; lean_object* v___x_4635_; 
v_a_4632_ = lean_ctor_get(v___x_4631_, 0);
lean_inc(v_a_4632_);
lean_dec_ref_known(v___x_4631_, 1);
v___x_4633_ = lean_unsigned_to_nat(4u);
v_body_4634_ = l_Lean_Syntax_getArg(v_stx_4210_, v___x_4633_);
lean_dec(v_stx_4210_);
lean_inc(v_body_4634_);
v___x_4635_ = l_Lean_Elab_Do_inferControlInfoSeq(v_body_4634_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_);
if (lean_obj_tag(v___x_4635_) == 0)
{
lean_object* v_a_4636_; lean_object* v___x_4637_; 
v_a_4636_ = lean_ctor_get(v___x_4635_, 0);
lean_inc(v_a_4636_);
lean_dec_ref_known(v___x_4635_, 1);
v___x_4637_ = l_Lean_Elab_Do_getReturnCont___redArg(v___y_4592_);
if (lean_obj_tag(v___x_4637_) == 0)
{
lean_object* v_a_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; 
v_a_4638_ = lean_ctor_get(v___x_4637_, 0);
lean_inc(v_a_4638_);
lean_dec_ref_known(v___x_4637_, 1);
v___x_4639_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__14));
v___x_4640_ = l_Lean_Core_mkFreshUserName(v___x_4639_, v___y_4597_, v___y_4598_);
if (lean_obj_tag(v___x_4640_) == 0)
{
lean_object* v_a_4641_; lean_object* v_monadInfo_4642_; lean_object* v_mutVars_4643_; lean_object* v___f_4644_; lean_object* v___f_4645_; lean_object* v___x_4646_; lean_object* v___f_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; uint8_t v___x_4650_; 
v_a_4641_ = lean_ctor_get(v___x_4640_, 0);
lean_inc(v_a_4641_);
lean_dec_ref_known(v___x_4640_, 1);
v_monadInfo_4642_ = lean_ctor_get(v___y_4592_, 0);
v_mutVars_4643_ = lean_ctor_get(v___y_4592_, 1);
lean_inc(v_a_4614_);
v___f_4644_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__0___boxed), 10, 1);
lean_closure_set(v___f_4644_, 0, v_a_4614_);
lean_inc_ref(v___f_4644_);
lean_inc(v___y_4586_);
v___f_4645_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__2___boxed), 5, 3);
lean_closure_set(v___f_4645_, 0, v___y_4586_);
lean_closure_set(v___f_4645_, 1, v___f_4644_);
lean_closure_set(v___f_4645_, 2, v___x_4223_);
v___x_4646_ = lean_box(v___x_4230_);
lean_inc(v_a_4638_);
v___f_4647_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__1___boxed), 12, 3);
lean_closure_set(v___f_4647_, 0, v_a_4638_);
lean_closure_set(v___f_4647_, 1, v___x_4223_);
lean_closure_set(v___f_4647_, 2, v___x_4646_);
v___x_4648_ = lean_array_get_size(v_mutVars_4643_);
v___x_4649_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__15));
v___x_4650_ = lean_nat_dec_lt(v___x_4227_, v___x_4648_);
if (v___x_4650_ == 0)
{
lean_inc(v_a_4605_);
lean_inc(v_a_4607_);
lean_inc(v_a_4632_);
lean_inc(v_a_4641_);
lean_inc(v_a_4614_);
lean_inc(v_a_4624_);
v___y_4532_ = v_a_4624_;
v___y_4533_ = v___y_4584_;
v___y_4534_ = v_monadInfo_4642_;
v___y_4535_ = v___y_4585_;
v___y_4536_ = v___f_4645_;
v___y_4537_ = v_a_4614_;
v___y_4538_ = v___y_4586_;
v___y_4539_ = v_a_4641_;
v___y_4540_ = v_a_4632_;
v___y_4541_ = v_a_4607_;
v___y_4542_ = v_body_4634_;
v___y_4543_ = v___f_4647_;
v___y_4544_ = v_a_4605_;
v___y_4545_ = v___f_4644_;
v___y_4546_ = v_a_4600_;
v___y_4547_ = v_a_4638_;
v___y_4548_ = v_a_4624_;
v___y_4549_ = v___y_4592_;
v___y_4550_ = v___y_4594_;
v___y_4551_ = v___y_4596_;
v___y_4552_ = v___y_4598_;
v___y_4553_ = v___y_4597_;
v___y_4554_ = v___y_4587_;
v___y_4555_ = v_a_4614_;
v___y_4556_ = v___y_4590_;
v___y_4557_ = v_a_4641_;
v___y_4558_ = v_a_4632_;
v___y_4559_ = v_a_4607_;
v___y_4560_ = v___y_4595_;
v___y_4561_ = v___y_4593_;
v___y_4562_ = v_a_4605_;
v___y_4563_ = v___x_4611_;
v___y_4564_ = v_a_4636_;
v___y_4565_ = v_inv_x3f_4591_;
v___y_4566_ = v___y_4588_;
v___y_4567_ = v___x_4649_;
goto v___jp_4531_;
}
else
{
uint8_t v___x_4651_; 
v___x_4651_ = lean_nat_dec_le(v___x_4648_, v___x_4648_);
if (v___x_4651_ == 0)
{
if (v___x_4650_ == 0)
{
lean_inc(v_a_4605_);
lean_inc(v_a_4607_);
lean_inc(v_a_4632_);
lean_inc(v_a_4641_);
lean_inc(v_a_4614_);
lean_inc(v_a_4624_);
v___y_4532_ = v_a_4624_;
v___y_4533_ = v___y_4584_;
v___y_4534_ = v_monadInfo_4642_;
v___y_4535_ = v___y_4585_;
v___y_4536_ = v___f_4645_;
v___y_4537_ = v_a_4614_;
v___y_4538_ = v___y_4586_;
v___y_4539_ = v_a_4641_;
v___y_4540_ = v_a_4632_;
v___y_4541_ = v_a_4607_;
v___y_4542_ = v_body_4634_;
v___y_4543_ = v___f_4647_;
v___y_4544_ = v_a_4605_;
v___y_4545_ = v___f_4644_;
v___y_4546_ = v_a_4600_;
v___y_4547_ = v_a_4638_;
v___y_4548_ = v_a_4624_;
v___y_4549_ = v___y_4592_;
v___y_4550_ = v___y_4594_;
v___y_4551_ = v___y_4596_;
v___y_4552_ = v___y_4598_;
v___y_4553_ = v___y_4597_;
v___y_4554_ = v___y_4587_;
v___y_4555_ = v_a_4614_;
v___y_4556_ = v___y_4590_;
v___y_4557_ = v_a_4641_;
v___y_4558_ = v_a_4632_;
v___y_4559_ = v_a_4607_;
v___y_4560_ = v___y_4595_;
v___y_4561_ = v___y_4593_;
v___y_4562_ = v_a_4605_;
v___y_4563_ = v___x_4611_;
v___y_4564_ = v_a_4636_;
v___y_4565_ = v_inv_x3f_4591_;
v___y_4566_ = v___y_4588_;
v___y_4567_ = v___x_4649_;
goto v___jp_4531_;
}
else
{
size_t v___x_4652_; size_t v___x_4653_; lean_object* v___x_4654_; 
v___x_4652_ = ((size_t)0ULL);
v___x_4653_ = lean_usize_of_nat(v___x_4648_);
v___x_4654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__6(v_a_4636_, v_mutVars_4643_, v___x_4652_, v___x_4653_, v___x_4649_);
lean_inc(v_a_4605_);
lean_inc(v_a_4607_);
lean_inc(v_a_4632_);
lean_inc(v_a_4641_);
lean_inc(v_a_4614_);
lean_inc(v_a_4624_);
v___y_4532_ = v_a_4624_;
v___y_4533_ = v___y_4584_;
v___y_4534_ = v_monadInfo_4642_;
v___y_4535_ = v___y_4585_;
v___y_4536_ = v___f_4645_;
v___y_4537_ = v_a_4614_;
v___y_4538_ = v___y_4586_;
v___y_4539_ = v_a_4641_;
v___y_4540_ = v_a_4632_;
v___y_4541_ = v_a_4607_;
v___y_4542_ = v_body_4634_;
v___y_4543_ = v___f_4647_;
v___y_4544_ = v_a_4605_;
v___y_4545_ = v___f_4644_;
v___y_4546_ = v_a_4600_;
v___y_4547_ = v_a_4638_;
v___y_4548_ = v_a_4624_;
v___y_4549_ = v___y_4592_;
v___y_4550_ = v___y_4594_;
v___y_4551_ = v___y_4596_;
v___y_4552_ = v___y_4598_;
v___y_4553_ = v___y_4597_;
v___y_4554_ = v___y_4587_;
v___y_4555_ = v_a_4614_;
v___y_4556_ = v___y_4590_;
v___y_4557_ = v_a_4641_;
v___y_4558_ = v_a_4632_;
v___y_4559_ = v_a_4607_;
v___y_4560_ = v___y_4595_;
v___y_4561_ = v___y_4593_;
v___y_4562_ = v_a_4605_;
v___y_4563_ = v___x_4611_;
v___y_4564_ = v_a_4636_;
v___y_4565_ = v_inv_x3f_4591_;
v___y_4566_ = v___y_4588_;
v___y_4567_ = v___x_4654_;
goto v___jp_4531_;
}
}
else
{
size_t v___x_4655_; size_t v___x_4656_; lean_object* v___x_4657_; 
v___x_4655_ = ((size_t)0ULL);
v___x_4656_ = lean_usize_of_nat(v___x_4648_);
v___x_4657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__6(v_a_4636_, v_mutVars_4643_, v___x_4655_, v___x_4656_, v___x_4649_);
lean_inc(v_a_4605_);
lean_inc(v_a_4607_);
lean_inc(v_a_4632_);
lean_inc(v_a_4641_);
lean_inc(v_a_4614_);
lean_inc(v_a_4624_);
v___y_4532_ = v_a_4624_;
v___y_4533_ = v___y_4584_;
v___y_4534_ = v_monadInfo_4642_;
v___y_4535_ = v___y_4585_;
v___y_4536_ = v___f_4645_;
v___y_4537_ = v_a_4614_;
v___y_4538_ = v___y_4586_;
v___y_4539_ = v_a_4641_;
v___y_4540_ = v_a_4632_;
v___y_4541_ = v_a_4607_;
v___y_4542_ = v_body_4634_;
v___y_4543_ = v___f_4647_;
v___y_4544_ = v_a_4605_;
v___y_4545_ = v___f_4644_;
v___y_4546_ = v_a_4600_;
v___y_4547_ = v_a_4638_;
v___y_4548_ = v_a_4624_;
v___y_4549_ = v___y_4592_;
v___y_4550_ = v___y_4594_;
v___y_4551_ = v___y_4596_;
v___y_4552_ = v___y_4598_;
v___y_4553_ = v___y_4597_;
v___y_4554_ = v___y_4587_;
v___y_4555_ = v_a_4614_;
v___y_4556_ = v___y_4590_;
v___y_4557_ = v_a_4641_;
v___y_4558_ = v_a_4632_;
v___y_4559_ = v_a_4607_;
v___y_4560_ = v___y_4595_;
v___y_4561_ = v___y_4593_;
v___y_4562_ = v_a_4605_;
v___y_4563_ = v___x_4611_;
v___y_4564_ = v_a_4636_;
v___y_4565_ = v_inv_x3f_4591_;
v___y_4566_ = v___y_4588_;
v___y_4567_ = v___x_4657_;
goto v___jp_4531_;
}
}
}
else
{
lean_object* v_a_4658_; lean_object* v___x_4660_; uint8_t v_isShared_4661_; uint8_t v_isSharedCheck_4665_; 
lean_dec(v_a_4638_);
lean_dec(v_a_4636_);
lean_dec(v_body_4634_);
lean_dec(v_a_4632_);
lean_dec(v_a_4624_);
lean_dec(v_a_4614_);
lean_dec(v_a_4607_);
lean_dec(v_a_4605_);
lean_dec(v_a_4600_);
lean_dec(v_inv_x3f_4591_);
lean_dec(v___y_4590_);
lean_dec(v___y_4587_);
lean_dec(v___y_4586_);
lean_dec(v___y_4585_);
v_a_4658_ = lean_ctor_get(v___x_4640_, 0);
v_isSharedCheck_4665_ = !lean_is_exclusive(v___x_4640_);
if (v_isSharedCheck_4665_ == 0)
{
v___x_4660_ = v___x_4640_;
v_isShared_4661_ = v_isSharedCheck_4665_;
goto v_resetjp_4659_;
}
else
{
lean_inc(v_a_4658_);
lean_dec(v___x_4640_);
v___x_4660_ = lean_box(0);
v_isShared_4661_ = v_isSharedCheck_4665_;
goto v_resetjp_4659_;
}
v_resetjp_4659_:
{
lean_object* v___x_4663_; 
if (v_isShared_4661_ == 0)
{
v___x_4663_ = v___x_4660_;
goto v_reusejp_4662_;
}
else
{
lean_object* v_reuseFailAlloc_4664_; 
v_reuseFailAlloc_4664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4664_, 0, v_a_4658_);
v___x_4663_ = v_reuseFailAlloc_4664_;
goto v_reusejp_4662_;
}
v_reusejp_4662_:
{
return v___x_4663_;
}
}
}
}
else
{
lean_object* v_a_4666_; lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4673_; 
lean_dec(v_a_4636_);
lean_dec(v_body_4634_);
lean_dec(v_a_4632_);
lean_dec(v_a_4624_);
lean_dec(v_a_4614_);
lean_dec(v_a_4607_);
lean_dec(v_a_4605_);
lean_dec(v_a_4600_);
lean_dec(v_inv_x3f_4591_);
lean_dec(v___y_4590_);
lean_dec(v___y_4587_);
lean_dec(v___y_4586_);
lean_dec(v___y_4585_);
v_a_4666_ = lean_ctor_get(v___x_4637_, 0);
v_isSharedCheck_4673_ = !lean_is_exclusive(v___x_4637_);
if (v_isSharedCheck_4673_ == 0)
{
v___x_4668_ = v___x_4637_;
v_isShared_4669_ = v_isSharedCheck_4673_;
goto v_resetjp_4667_;
}
else
{
lean_inc(v_a_4666_);
lean_dec(v___x_4637_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4673_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
lean_object* v___x_4671_; 
if (v_isShared_4669_ == 0)
{
v___x_4671_ = v___x_4668_;
goto v_reusejp_4670_;
}
else
{
lean_object* v_reuseFailAlloc_4672_; 
v_reuseFailAlloc_4672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4672_, 0, v_a_4666_);
v___x_4671_ = v_reuseFailAlloc_4672_;
goto v_reusejp_4670_;
}
v_reusejp_4670_:
{
return v___x_4671_;
}
}
}
}
else
{
lean_object* v_a_4674_; lean_object* v___x_4676_; uint8_t v_isShared_4677_; uint8_t v_isSharedCheck_4681_; 
lean_dec(v_body_4634_);
lean_dec(v_a_4632_);
lean_dec(v_a_4624_);
lean_dec(v_a_4614_);
lean_dec(v_a_4607_);
lean_dec(v_a_4605_);
lean_dec(v_a_4600_);
lean_dec(v_inv_x3f_4591_);
lean_dec(v___y_4590_);
lean_dec(v___y_4587_);
lean_dec(v___y_4586_);
lean_dec(v___y_4585_);
v_a_4674_ = lean_ctor_get(v___x_4635_, 0);
v_isSharedCheck_4681_ = !lean_is_exclusive(v___x_4635_);
if (v_isSharedCheck_4681_ == 0)
{
v___x_4676_ = v___x_4635_;
v_isShared_4677_ = v_isSharedCheck_4681_;
goto v_resetjp_4675_;
}
else
{
lean_inc(v_a_4674_);
lean_dec(v___x_4635_);
v___x_4676_ = lean_box(0);
v_isShared_4677_ = v_isSharedCheck_4681_;
goto v_resetjp_4675_;
}
v_resetjp_4675_:
{
lean_object* v___x_4679_; 
if (v_isShared_4677_ == 0)
{
v___x_4679_ = v___x_4676_;
goto v_reusejp_4678_;
}
else
{
lean_object* v_reuseFailAlloc_4680_; 
v_reuseFailAlloc_4680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4680_, 0, v_a_4674_);
v___x_4679_ = v_reuseFailAlloc_4680_;
goto v_reusejp_4678_;
}
v_reusejp_4678_:
{
return v___x_4679_;
}
}
}
}
else
{
lean_dec(v_a_4624_);
lean_dec(v_a_4614_);
lean_dec(v_a_4607_);
lean_dec(v_a_4605_);
lean_dec(v_a_4600_);
lean_dec(v_inv_x3f_4591_);
lean_dec(v___y_4590_);
lean_dec(v___y_4587_);
lean_dec(v___y_4586_);
lean_dec(v___y_4585_);
lean_dec(v_stx_4210_);
return v___x_4631_;
}
}
}
}
else
{
lean_dec(v_a_4614_);
lean_dec(v_a_4607_);
lean_dec(v_a_4605_);
lean_dec(v_a_4600_);
lean_dec(v_inv_x3f_4591_);
lean_dec(v___y_4590_);
lean_dec(v___y_4589_);
lean_dec(v___y_4587_);
lean_dec(v___y_4586_);
lean_dec(v___y_4585_);
lean_dec(v_stx_4210_);
return v___x_4623_;
}
}
}
}
else
{
lean_dec(v_a_4607_);
lean_dec(v_a_4605_);
lean_dec(v_a_4600_);
lean_dec(v_inv_x3f_4591_);
lean_dec(v___y_4590_);
lean_dec(v___y_4589_);
lean_dec(v___y_4587_);
lean_dec(v___y_4586_);
lean_dec(v___y_4585_);
lean_dec(v_stx_4210_);
return v___x_4613_;
}
}
else
{
lean_object* v_a_4686_; lean_object* v___x_4688_; uint8_t v_isShared_4689_; uint8_t v_isSharedCheck_4693_; 
lean_dec(v_a_4605_);
lean_dec(v_a_4600_);
lean_dec(v_inv_x3f_4591_);
lean_dec(v___y_4590_);
lean_dec(v___y_4589_);
lean_dec(v___y_4587_);
lean_dec(v___y_4586_);
lean_dec(v___y_4585_);
lean_dec(v_stx_4210_);
v_a_4686_ = lean_ctor_get(v___x_4606_, 0);
v_isSharedCheck_4693_ = !lean_is_exclusive(v___x_4606_);
if (v_isSharedCheck_4693_ == 0)
{
v___x_4688_ = v___x_4606_;
v_isShared_4689_ = v_isSharedCheck_4693_;
goto v_resetjp_4687_;
}
else
{
lean_inc(v_a_4686_);
lean_dec(v___x_4606_);
v___x_4688_ = lean_box(0);
v_isShared_4689_ = v_isSharedCheck_4693_;
goto v_resetjp_4687_;
}
v_resetjp_4687_:
{
lean_object* v___x_4691_; 
if (v_isShared_4689_ == 0)
{
v___x_4691_ = v___x_4688_;
goto v_reusejp_4690_;
}
else
{
lean_object* v_reuseFailAlloc_4692_; 
v_reuseFailAlloc_4692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4692_, 0, v_a_4686_);
v___x_4691_ = v_reuseFailAlloc_4692_;
goto v_reusejp_4690_;
}
v_reusejp_4690_:
{
return v___x_4691_;
}
}
}
}
else
{
lean_object* v_a_4694_; lean_object* v___x_4696_; uint8_t v_isShared_4697_; uint8_t v_isSharedCheck_4701_; 
lean_dec(v_a_4600_);
lean_dec(v_inv_x3f_4591_);
lean_dec(v___y_4590_);
lean_dec(v___y_4589_);
lean_dec(v___y_4587_);
lean_dec(v___y_4586_);
lean_dec(v___y_4585_);
lean_dec(v_stx_4210_);
v_a_4694_ = lean_ctor_get(v___x_4604_, 0);
v_isSharedCheck_4701_ = !lean_is_exclusive(v___x_4604_);
if (v_isSharedCheck_4701_ == 0)
{
v___x_4696_ = v___x_4604_;
v_isShared_4697_ = v_isSharedCheck_4701_;
goto v_resetjp_4695_;
}
else
{
lean_inc(v_a_4694_);
lean_dec(v___x_4604_);
v___x_4696_ = lean_box(0);
v_isShared_4697_ = v_isSharedCheck_4701_;
goto v_resetjp_4695_;
}
v_resetjp_4695_:
{
lean_object* v___x_4699_; 
if (v_isShared_4697_ == 0)
{
v___x_4699_ = v___x_4696_;
goto v_reusejp_4698_;
}
else
{
lean_object* v_reuseFailAlloc_4700_; 
v_reuseFailAlloc_4700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4700_, 0, v_a_4694_);
v___x_4699_ = v_reuseFailAlloc_4700_;
goto v_reusejp_4698_;
}
v_reusejp_4698_:
{
return v___x_4699_;
}
}
}
}
else
{
lean_object* v_a_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4709_; 
lean_dec(v_a_4600_);
lean_dec(v_inv_x3f_4591_);
lean_dec(v___y_4590_);
lean_dec(v___y_4589_);
lean_dec(v___y_4587_);
lean_dec(v___y_4586_);
lean_dec(v___y_4585_);
lean_dec(v_stx_4210_);
v_a_4702_ = lean_ctor_get(v___x_4603_, 0);
v_isSharedCheck_4709_ = !lean_is_exclusive(v___x_4603_);
if (v_isSharedCheck_4709_ == 0)
{
v___x_4704_ = v___x_4603_;
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_a_4702_);
lean_dec(v___x_4603_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v___x_4707_; 
if (v_isShared_4705_ == 0)
{
v___x_4707_ = v___x_4704_;
goto v_reusejp_4706_;
}
else
{
lean_object* v_reuseFailAlloc_4708_; 
v_reuseFailAlloc_4708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4708_, 0, v_a_4702_);
v___x_4707_ = v_reuseFailAlloc_4708_;
goto v_reusejp_4706_;
}
v_reusejp_4706_:
{
return v___x_4707_;
}
}
}
}
else
{
lean_object* v_a_4710_; lean_object* v___x_4712_; uint8_t v_isShared_4713_; uint8_t v_isSharedCheck_4717_; 
lean_dec(v_inv_x3f_4591_);
lean_dec(v___y_4590_);
lean_dec(v___y_4589_);
lean_dec(v___y_4587_);
lean_dec(v___y_4586_);
lean_dec(v___y_4585_);
lean_dec(v_stx_4210_);
v_a_4710_ = lean_ctor_get(v___x_4599_, 0);
v_isSharedCheck_4717_ = !lean_is_exclusive(v___x_4599_);
if (v_isSharedCheck_4717_ == 0)
{
v___x_4712_ = v___x_4599_;
v_isShared_4713_ = v_isSharedCheck_4717_;
goto v_resetjp_4711_;
}
else
{
lean_inc(v_a_4710_);
lean_dec(v___x_4599_);
v___x_4712_ = lean_box(0);
v_isShared_4713_ = v_isSharedCheck_4717_;
goto v_resetjp_4711_;
}
v_resetjp_4711_:
{
lean_object* v___x_4715_; 
if (v_isShared_4713_ == 0)
{
v___x_4715_ = v___x_4712_;
goto v_reusejp_4714_;
}
else
{
lean_object* v_reuseFailAlloc_4716_; 
v_reuseFailAlloc_4716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4716_, 0, v_a_4710_);
v___x_4715_ = v_reuseFailAlloc_4716_;
goto v_reusejp_4714_;
}
v_reusejp_4714_:
{
return v___x_4715_;
}
}
}
}
v___jp_4718_:
{
lean_object* v_x_4727_; lean_object* v___x_4728_; uint8_t v___x_4729_; 
v_x_4727_ = l_Lean_Syntax_getArg(v___x_4228_, v___x_4223_);
v___x_4728_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__19));
lean_inc(v_x_4727_);
v___x_4729_ = l_Lean_Syntax_isOfKind(v_x_4727_, v___x_4728_);
if (v___x_4729_ == 0)
{
lean_object* v___x_4730_; 
lean_dec(v_x_4727_);
lean_dec(v_h_x3f_4719_);
lean_dec(v_tk_4582_);
lean_dec(v___x_4228_);
lean_dec_ref(v_dec_4211_);
lean_dec(v_stx_4210_);
v___x_4730_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v___x_4730_;
}
else
{
lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; uint8_t v___x_4735_; 
v___x_4731_ = lean_unsigned_to_nat(2u);
v___x_4732_ = lean_unsigned_to_nat(3u);
v___x_4733_ = l_Lean_Syntax_getArg(v___x_4228_, v___x_4732_);
lean_dec(v___x_4228_);
v___x_4734_ = l_Lean_Syntax_getArg(v_stx_4210_, v___x_4731_);
v___x_4735_ = l_Lean_Syntax_isNone(v___x_4734_);
if (v___x_4735_ == 0)
{
uint8_t v___x_4736_; 
lean_inc(v___x_4734_);
v___x_4736_ = l_Lean_Syntax_matchesNull(v___x_4734_, v___x_4223_);
if (v___x_4736_ == 0)
{
lean_object* v___x_4737_; 
lean_dec(v___x_4734_);
lean_dec(v___x_4733_);
lean_dec(v_x_4727_);
lean_dec(v_h_x3f_4719_);
lean_dec(v_tk_4582_);
lean_dec_ref(v_dec_4211_);
lean_dec(v_stx_4210_);
v___x_4737_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v___x_4737_;
}
else
{
lean_object* v_inv_x3f_4738_; lean_object* v___x_4739_; uint8_t v___x_4740_; 
v_inv_x3f_4738_ = l_Lean_Syntax_getArg(v___x_4734_, v___x_4227_);
lean_dec(v___x_4734_);
v___x_4739_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v_inv_x3f_4738_);
v___x_4740_ = l_Lean_Syntax_isOfKind(v_inv_x3f_4738_, v___x_4739_);
if (v___x_4740_ == 0)
{
lean_object* v___x_4741_; 
lean_dec(v_inv_x3f_4738_);
lean_dec(v___x_4733_);
lean_dec(v_x_4727_);
lean_dec(v_h_x3f_4719_);
lean_dec(v_tk_4582_);
lean_dec_ref(v_dec_4211_);
lean_dec(v_stx_4210_);
v___x_4741_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant_spec__0___redArg();
return v___x_4741_;
}
else
{
lean_object* v___x_4742_; 
v___x_4742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4742_, 0, v_inv_x3f_4738_);
lean_inc(v_x_4727_);
lean_inc(v_h_x3f_4719_);
v___y_4584_ = v___x_4729_;
v___y_4585_ = v_h_x3f_4719_;
v___y_4586_ = v_x_4727_;
v___y_4587_ = v_h_x3f_4719_;
v___y_4588_ = v___x_4731_;
v___y_4589_ = v___x_4733_;
v___y_4590_ = v_x_4727_;
v_inv_x3f_4591_ = v___x_4742_;
v___y_4592_ = v___y_4720_;
v___y_4593_ = v___y_4721_;
v___y_4594_ = v___y_4722_;
v___y_4595_ = v___y_4723_;
v___y_4596_ = v___y_4724_;
v___y_4597_ = v___y_4725_;
v___y_4598_ = v___y_4726_;
goto v___jp_4583_;
}
}
}
else
{
lean_object* v___x_4743_; 
lean_dec(v___x_4734_);
v___x_4743_ = lean_box(0);
lean_inc(v_x_4727_);
lean_inc(v_h_x3f_4719_);
v___y_4584_ = v___x_4729_;
v___y_4585_ = v_h_x3f_4719_;
v___y_4586_ = v_x_4727_;
v___y_4587_ = v_h_x3f_4719_;
v___y_4588_ = v___x_4731_;
v___y_4589_ = v___x_4733_;
v___y_4590_ = v_x_4727_;
v_inv_x3f_4591_ = v___x_4743_;
v___y_4592_ = v___y_4720_;
v___y_4593_ = v___y_4721_;
v___y_4594_ = v___y_4722_;
v___y_4595_ = v___y_4723_;
v___y_4596_ = v___y_4724_;
v___y_4597_ = v___y_4725_;
v___y_4598_ = v___y_4726_;
goto v___jp_4583_;
}
}
}
}
v___jp_4231_:
{
lean_object* v_doBlockResultType_4251_; lean_object* v___x_4252_; lean_object* v___y_4253_; lean_object* v___x_4254_; lean_object* v___f_4255_; lean_object* v___x_4256_; 
v_doBlockResultType_4251_ = lean_ctor_get(v___y_4244_, 3);
v___x_4252_ = lean_box(v___y_4236_);
lean_inc(v___y_4237_);
lean_inc_ref(v_doBlockResultType_4251_);
v___y_4253_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__4___boxed), 19, 11);
lean_closure_set(v___y_4253_, 0, v___x_4252_);
lean_closure_set(v___y_4253_, 1, v___y_4239_);
lean_closure_set(v___y_4253_, 2, v___y_4238_);
lean_closure_set(v___y_4253_, 3, v_doBlockResultType_4251_);
lean_closure_set(v___y_4253_, 4, v___y_4240_);
lean_closure_set(v___y_4253_, 5, v___y_4237_);
lean_closure_set(v___y_4253_, 6, v___y_4235_);
lean_closure_set(v___y_4253_, 7, v___y_4233_);
lean_closure_set(v___y_4253_, 8, v___y_4232_);
lean_closure_set(v___y_4253_, 9, v___x_4227_);
lean_closure_set(v___y_4253_, 10, v___x_4223_);
v___x_4254_ = lean_box(v___x_4230_);
v___f_4255_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__5___boxed), 13, 4);
lean_closure_set(v___f_4255_, 0, v___y_4234_);
lean_closure_set(v___f_4255_, 1, v___y_4253_);
lean_closure_set(v___f_4255_, 2, v___x_4223_);
lean_closure_set(v___f_4255_, 3, v___x_4254_);
lean_inc_ref(v___y_4242_);
v___x_4256_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v___y_4241_, v___y_4242_, v___f_4255_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_);
if (lean_obj_tag(v___x_4256_) == 0)
{
lean_object* v_a_4257_; lean_object* v___x_4258_; 
v_a_4257_ = lean_ctor_get(v___x_4256_, 0);
lean_inc(v_a_4257_);
lean_dec_ref_known(v___x_4256_, 1);
lean_inc_ref(v_doBlockResultType_4251_);
v___x_4258_ = l_Lean_Elab_Do_mkBindApp(v___y_4242_, v_doBlockResultType_4251_, v_forIn_4243_, v_a_4257_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_);
return v___x_4258_;
}
else
{
lean_dec_ref(v_forIn_4243_);
lean_dec_ref(v___y_4242_);
return v___x_4256_;
}
}
v___jp_4259_:
{
lean_object* v___x_4287_; 
lean_inc_ref(v___y_4275_);
lean_inc_ref(v___y_4274_);
v___x_4287_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInWithInvariant(v___y_4276_, v___y_4286_, v___y_4280_, v___y_4277_, v___y_4282_, v___y_4284_, v___y_4274_, v___y_4273_, v___y_4279_, v___y_4275_, v___y_4283_, v___y_4281_, v___y_4270_, v___y_4285_, v___y_4278_, v___y_4269_, v___y_4272_);
lean_dec_ref(v___y_4273_);
lean_dec(v___y_4286_);
if (lean_obj_tag(v___x_4287_) == 0)
{
lean_object* v_a_4288_; 
v_a_4288_ = lean_ctor_get(v___x_4287_, 0);
lean_inc(v_a_4288_);
lean_dec_ref_known(v___x_4287_, 1);
v___y_4232_ = v___y_4261_;
v___y_4233_ = v___y_4260_;
v___y_4234_ = v___y_4263_;
v___y_4235_ = v___y_4262_;
v___y_4236_ = v___y_4264_;
v___y_4237_ = v___y_4266_;
v___y_4238_ = v___y_4265_;
v___y_4239_ = v___y_4267_;
v___y_4240_ = v___y_4268_;
v___y_4241_ = v___y_4271_;
v___y_4242_ = v___y_4274_;
v_forIn_4243_ = v_a_4288_;
v___y_4244_ = v___y_4283_;
v___y_4245_ = v___y_4281_;
v___y_4246_ = v___y_4270_;
v___y_4247_ = v___y_4285_;
v___y_4248_ = v___y_4278_;
v___y_4249_ = v___y_4269_;
v___y_4250_ = v___y_4272_;
goto v___jp_4231_;
}
else
{
lean_dec_ref(v___y_4274_);
lean_dec(v___y_4271_);
lean_dec_ref(v___y_4268_);
lean_dec_ref(v___y_4267_);
lean_dec(v___y_4265_);
lean_dec(v___y_4263_);
lean_dec(v___y_4262_);
lean_dec_ref(v___y_4261_);
lean_dec_ref(v___y_4260_);
return v___x_4287_;
}
}
v___jp_4289_:
{
lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___f_4326_; uint8_t v___x_4327_; lean_object* v___x_4328_; 
v___x_4324_ = l_Lean_instInhabitedExpr;
v___x_4325_ = lean_box(v___x_4230_);
lean_inc(v___y_4290_);
lean_inc(v___y_4303_);
lean_inc(v___y_4302_);
lean_inc_ref(v___y_4304_);
lean_inc_ref(v___y_4305_);
v___f_4326_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__11___boxed), 24, 15);
lean_closure_set(v___f_4326_, 0, v___x_4324_);
lean_closure_set(v___f_4326_, 1, v___x_4227_);
lean_closure_set(v___f_4326_, 2, v___y_4295_);
lean_closure_set(v___f_4326_, 3, v___y_4305_);
lean_closure_set(v___f_4326_, 4, v___y_4304_);
lean_closure_set(v___f_4326_, 5, v___y_4302_);
lean_closure_set(v___f_4326_, 6, v___y_4292_);
lean_closure_set(v___f_4326_, 7, v___y_4296_);
lean_closure_set(v___f_4326_, 8, v___y_4301_);
lean_closure_set(v___f_4326_, 9, v___y_4300_);
lean_closure_set(v___f_4326_, 10, v___x_4325_);
lean_closure_set(v___f_4326_, 11, v___y_4303_);
lean_closure_set(v___f_4326_, 12, v___y_4290_);
lean_closure_set(v___f_4326_, 13, v___y_4293_);
lean_closure_set(v___f_4326_, 14, v___x_4223_);
v___x_4327_ = 0;
v___x_4328_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(v___y_4323_, v___f_4326_, v___x_4327_, v___y_4320_, v___y_4318_, v___y_4307_, v___y_4321_, v___y_4315_, v___y_4308_, v___y_4309_);
if (lean_obj_tag(v___x_4328_) == 0)
{
if (lean_obj_tag(v___y_4322_) == 0)
{
lean_object* v_a_4329_; lean_object* v___x_4330_; 
lean_dec_ref(v___y_4319_);
lean_dec_ref(v___y_4317_);
lean_dec_ref(v___y_4314_);
lean_dec(v___y_4313_);
lean_dec_ref(v___y_4310_);
v_a_4329_ = lean_ctor_get(v___x_4328_, 0);
lean_inc(v_a_4329_);
lean_dec_ref_known(v___x_4328_, 1);
v___x_4330_ = l_Lean_Expr_app___override(v___y_4306_, v_a_4329_);
v___y_4232_ = v___y_4291_;
v___y_4233_ = v___y_4299_;
v___y_4234_ = v___y_4303_;
v___y_4235_ = v___y_4302_;
v___y_4236_ = v___y_4294_;
v___y_4237_ = v___y_4298_;
v___y_4238_ = v___y_4297_;
v___y_4239_ = v___y_4304_;
v___y_4240_ = v___y_4305_;
v___y_4241_ = v___y_4290_;
v___y_4242_ = v___y_4312_;
v_forIn_4243_ = v___x_4330_;
v___y_4244_ = v___y_4320_;
v___y_4245_ = v___y_4318_;
v___y_4246_ = v___y_4307_;
v___y_4247_ = v___y_4321_;
v___y_4248_ = v___y_4315_;
v___y_4249_ = v___y_4308_;
v___y_4250_ = v___y_4309_;
goto v___jp_4231_;
}
else
{
lean_dec_ref(v___y_4306_);
if (lean_obj_tag(v___y_4313_) == 0)
{
lean_object* v_a_4331_; lean_object* v_val_4332_; lean_object* v___x_4333_; 
v_a_4331_ = lean_ctor_get(v___x_4328_, 0);
lean_inc(v_a_4331_);
lean_dec_ref_known(v___x_4328_, 1);
v_val_4332_ = lean_ctor_get(v___y_4322_, 0);
lean_inc(v_val_4332_);
lean_dec_ref_known(v___y_4322_, 1);
v___x_4333_ = lean_box(0);
v___y_4260_ = v___y_4299_;
v___y_4261_ = v___y_4291_;
v___y_4262_ = v___y_4302_;
v___y_4263_ = v___y_4303_;
v___y_4264_ = v___y_4294_;
v___y_4265_ = v___y_4297_;
v___y_4266_ = v___y_4298_;
v___y_4267_ = v___y_4304_;
v___y_4268_ = v___y_4305_;
v___y_4269_ = v___y_4308_;
v___y_4270_ = v___y_4307_;
v___y_4271_ = v___y_4290_;
v___y_4272_ = v___y_4309_;
v___y_4273_ = v___y_4310_;
v___y_4274_ = v___y_4312_;
v___y_4275_ = v___y_4311_;
v___y_4276_ = v_val_4332_;
v___y_4277_ = v___y_4314_;
v___y_4278_ = v___y_4315_;
v___y_4279_ = v___y_4316_;
v___y_4280_ = v___y_4317_;
v___y_4281_ = v___y_4318_;
v___y_4282_ = v___y_4319_;
v___y_4283_ = v___y_4320_;
v___y_4284_ = v_a_4331_;
v___y_4285_ = v___y_4321_;
v___y_4286_ = v___x_4333_;
goto v___jp_4259_;
}
else
{
lean_object* v_a_4334_; lean_object* v_val_4335_; lean_object* v_val_4336_; lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4343_; 
v_a_4334_ = lean_ctor_get(v___x_4328_, 0);
lean_inc(v_a_4334_);
lean_dec_ref_known(v___x_4328_, 1);
v_val_4335_ = lean_ctor_get(v___y_4322_, 0);
lean_inc(v_val_4335_);
lean_dec_ref_known(v___y_4322_, 1);
v_val_4336_ = lean_ctor_get(v___y_4313_, 0);
v_isSharedCheck_4343_ = !lean_is_exclusive(v___y_4313_);
if (v_isSharedCheck_4343_ == 0)
{
v___x_4338_ = v___y_4313_;
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
else
{
lean_inc(v_val_4336_);
lean_dec(v___y_4313_);
v___x_4338_ = lean_box(0);
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
v_resetjp_4337_:
{
lean_object* v___x_4341_; 
if (v_isShared_4339_ == 0)
{
v___x_4341_ = v___x_4338_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v_val_4336_);
v___x_4341_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
v___y_4260_ = v___y_4299_;
v___y_4261_ = v___y_4291_;
v___y_4262_ = v___y_4302_;
v___y_4263_ = v___y_4303_;
v___y_4264_ = v___y_4294_;
v___y_4265_ = v___y_4297_;
v___y_4266_ = v___y_4298_;
v___y_4267_ = v___y_4304_;
v___y_4268_ = v___y_4305_;
v___y_4269_ = v___y_4308_;
v___y_4270_ = v___y_4307_;
v___y_4271_ = v___y_4290_;
v___y_4272_ = v___y_4309_;
v___y_4273_ = v___y_4310_;
v___y_4274_ = v___y_4312_;
v___y_4275_ = v___y_4311_;
v___y_4276_ = v_val_4335_;
v___y_4277_ = v___y_4314_;
v___y_4278_ = v___y_4315_;
v___y_4279_ = v___y_4316_;
v___y_4280_ = v___y_4317_;
v___y_4281_ = v___y_4318_;
v___y_4282_ = v___y_4319_;
v___y_4283_ = v___y_4320_;
v___y_4284_ = v_a_4334_;
v___y_4285_ = v___y_4321_;
v___y_4286_ = v___x_4341_;
goto v___jp_4259_;
}
}
}
}
}
else
{
lean_dec(v___y_4322_);
lean_dec_ref(v___y_4319_);
lean_dec_ref(v___y_4317_);
lean_dec_ref(v___y_4314_);
lean_dec(v___y_4313_);
lean_dec_ref(v___y_4312_);
lean_dec_ref(v___y_4310_);
lean_dec_ref(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec_ref(v___y_4304_);
lean_dec(v___y_4303_);
lean_dec(v___y_4302_);
lean_dec_ref(v___y_4299_);
lean_dec(v___y_4297_);
lean_dec_ref(v___y_4291_);
lean_dec(v___y_4290_);
return v___x_4328_;
}
}
v___jp_4344_:
{
lean_object* v___x_4386_; lean_object* v___x_4387_; 
v___x_4386_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17));
v___x_4387_ = l_Lean_Core_mkFreshUserName(v___x_4386_, v___y_4384_, v___y_4385_);
if (lean_obj_tag(v___x_4387_) == 0)
{
if (lean_obj_tag(v___y_4368_) == 1)
{
if (lean_obj_tag(v_snd_4378_) == 1)
{
lean_object* v_a_4388_; lean_object* v_val_4389_; lean_object* v_val_4390_; lean_object* v___f_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; 
lean_dec_ref(v___y_4370_);
v_a_4388_ = lean_ctor_get(v___x_4387_, 0);
lean_inc(v_a_4388_);
lean_dec_ref_known(v___x_4387_, 1);
v_val_4389_ = lean_ctor_get(v___y_4368_, 0);
v_val_4390_ = lean_ctor_get(v_snd_4378_, 0);
lean_inc(v_val_4390_);
lean_dec_ref_known(v_snd_4378_, 1);
v___f_4391_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__12___boxed), 16, 7);
lean_closure_set(v___f_4391_, 0, v___y_4356_);
lean_closure_set(v___f_4391_, 1, v___y_4360_);
lean_closure_set(v___f_4391_, 2, v___x_4227_);
lean_closure_set(v___f_4391_, 3, v___y_4349_);
lean_closure_set(v___f_4391_, 4, v___y_4345_);
lean_closure_set(v___f_4391_, 5, v_val_4390_);
lean_closure_set(v___f_4391_, 6, v___y_4353_);
v___x_4392_ = l_Lean_TSyntax_getId(v___y_4372_);
lean_dec(v___y_4372_);
v___x_4393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4393_, 0, v___x_4392_);
lean_ctor_set(v___x_4393_, 1, v___y_4376_);
v___x_4394_ = l_Lean_TSyntax_getId(v_val_4389_);
v___x_4395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4395_, 0, v___x_4394_);
lean_ctor_set(v___x_4395_, 1, v___f_4391_);
v___x_4396_ = lean_mk_empty_array_with_capacity(v___y_4375_);
v___x_4397_ = lean_array_push(v___x_4396_, v___x_4393_);
v___x_4398_ = lean_array_push(v___x_4397_, v___x_4395_);
lean_inc_ref(v___y_4347_);
v___y_4290_ = v_a_4388_;
v___y_4291_ = v___y_4346_;
v___y_4292_ = v___y_4347_;
v___y_4293_ = v___y_4348_;
v___y_4294_ = v___y_4350_;
v___y_4295_ = v___y_4351_;
v___y_4296_ = v___y_4352_;
v___y_4297_ = v___y_4354_;
v___y_4298_ = v___y_4355_;
v___y_4299_ = v___y_4358_;
v___y_4300_ = v___y_4359_;
v___y_4301_ = v___y_4361_;
v___y_4302_ = v___y_4362_;
v___y_4303_ = v___y_4363_;
v___y_4304_ = v___y_4364_;
v___y_4305_ = v___y_4365_;
v___y_4306_ = v_fst_4377_;
v___y_4307_ = v___y_4381_;
v___y_4308_ = v___y_4384_;
v___y_4309_ = v___y_4385_;
v___y_4310_ = v___y_4366_;
v___y_4311_ = v___y_4367_;
v___y_4312_ = v___y_4347_;
v___y_4313_ = v___y_4368_;
v___y_4314_ = v___y_4369_;
v___y_4315_ = v___y_4383_;
v___y_4316_ = v___y_4371_;
v___y_4317_ = v___y_4373_;
v___y_4318_ = v___y_4380_;
v___y_4319_ = v___y_4357_;
v___y_4320_ = v___y_4379_;
v___y_4321_ = v___y_4382_;
v___y_4322_ = v___y_4374_;
v___y_4323_ = v___x_4398_;
goto v___jp_4289_;
}
else
{
lean_object* v_a_4399_; lean_object* v___x_4400_; 
lean_dec_ref(v___y_4376_);
lean_dec(v___y_4372_);
lean_dec(v___y_4360_);
lean_dec(v___y_4356_);
lean_dec_ref(v___y_4353_);
lean_dec_ref(v___y_4349_);
lean_dec_ref(v___y_4345_);
v_a_4399_ = lean_ctor_get(v___x_4387_, 0);
lean_inc(v_a_4399_);
lean_dec_ref_known(v___x_4387_, 1);
lean_inc_ref(v___y_4368_);
v___x_4400_ = lean_apply_2(v___y_4370_, v___y_4368_, v_snd_4378_);
lean_inc_ref(v___y_4347_);
v___y_4290_ = v_a_4399_;
v___y_4291_ = v___y_4346_;
v___y_4292_ = v___y_4347_;
v___y_4293_ = v___y_4348_;
v___y_4294_ = v___y_4350_;
v___y_4295_ = v___y_4351_;
v___y_4296_ = v___y_4352_;
v___y_4297_ = v___y_4354_;
v___y_4298_ = v___y_4355_;
v___y_4299_ = v___y_4358_;
v___y_4300_ = v___y_4359_;
v___y_4301_ = v___y_4361_;
v___y_4302_ = v___y_4362_;
v___y_4303_ = v___y_4363_;
v___y_4304_ = v___y_4364_;
v___y_4305_ = v___y_4365_;
v___y_4306_ = v_fst_4377_;
v___y_4307_ = v___y_4381_;
v___y_4308_ = v___y_4384_;
v___y_4309_ = v___y_4385_;
v___y_4310_ = v___y_4366_;
v___y_4311_ = v___y_4367_;
v___y_4312_ = v___y_4347_;
v___y_4313_ = v___y_4368_;
v___y_4314_ = v___y_4369_;
v___y_4315_ = v___y_4383_;
v___y_4316_ = v___y_4371_;
v___y_4317_ = v___y_4373_;
v___y_4318_ = v___y_4380_;
v___y_4319_ = v___y_4357_;
v___y_4320_ = v___y_4379_;
v___y_4321_ = v___y_4382_;
v___y_4322_ = v___y_4374_;
v___y_4323_ = v___x_4400_;
goto v___jp_4289_;
}
}
else
{
lean_object* v_a_4401_; lean_object* v___x_4402_; 
lean_dec_ref(v___y_4376_);
lean_dec(v___y_4372_);
lean_dec(v___y_4360_);
lean_dec(v___y_4356_);
lean_dec_ref(v___y_4353_);
lean_dec_ref(v___y_4349_);
lean_dec_ref(v___y_4345_);
v_a_4401_ = lean_ctor_get(v___x_4387_, 0);
lean_inc(v_a_4401_);
lean_dec_ref_known(v___x_4387_, 1);
lean_inc(v___y_4368_);
v___x_4402_ = lean_apply_2(v___y_4370_, v___y_4368_, v_snd_4378_);
lean_inc_ref(v___y_4347_);
v___y_4290_ = v_a_4401_;
v___y_4291_ = v___y_4346_;
v___y_4292_ = v___y_4347_;
v___y_4293_ = v___y_4348_;
v___y_4294_ = v___y_4350_;
v___y_4295_ = v___y_4351_;
v___y_4296_ = v___y_4352_;
v___y_4297_ = v___y_4354_;
v___y_4298_ = v___y_4355_;
v___y_4299_ = v___y_4358_;
v___y_4300_ = v___y_4359_;
v___y_4301_ = v___y_4361_;
v___y_4302_ = v___y_4362_;
v___y_4303_ = v___y_4363_;
v___y_4304_ = v___y_4364_;
v___y_4305_ = v___y_4365_;
v___y_4306_ = v_fst_4377_;
v___y_4307_ = v___y_4381_;
v___y_4308_ = v___y_4384_;
v___y_4309_ = v___y_4385_;
v___y_4310_ = v___y_4366_;
v___y_4311_ = v___y_4367_;
v___y_4312_ = v___y_4347_;
v___y_4313_ = v___y_4368_;
v___y_4314_ = v___y_4369_;
v___y_4315_ = v___y_4383_;
v___y_4316_ = v___y_4371_;
v___y_4317_ = v___y_4373_;
v___y_4318_ = v___y_4380_;
v___y_4319_ = v___y_4357_;
v___y_4320_ = v___y_4379_;
v___y_4321_ = v___y_4382_;
v___y_4322_ = v___y_4374_;
v___y_4323_ = v___x_4402_;
goto v___jp_4289_;
}
}
else
{
lean_object* v_a_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4410_; 
lean_dec(v_snd_4378_);
lean_dec_ref(v_fst_4377_);
lean_dec_ref(v___y_4376_);
lean_dec(v___y_4374_);
lean_dec_ref(v___y_4373_);
lean_dec(v___y_4372_);
lean_dec_ref(v___y_4370_);
lean_dec_ref(v___y_4369_);
lean_dec(v___y_4368_);
lean_dec_ref(v___y_4366_);
lean_dec_ref(v___y_4365_);
lean_dec_ref(v___y_4364_);
lean_dec(v___y_4363_);
lean_dec(v___y_4362_);
lean_dec(v___y_4361_);
lean_dec(v___y_4360_);
lean_dec(v___y_4359_);
lean_dec_ref(v___y_4358_);
lean_dec_ref(v___y_4357_);
lean_dec(v___y_4356_);
lean_dec(v___y_4354_);
lean_dec_ref(v___y_4353_);
lean_dec_ref(v___y_4352_);
lean_dec(v___y_4351_);
lean_dec_ref(v___y_4349_);
lean_dec(v___y_4348_);
lean_dec_ref(v___y_4347_);
lean_dec_ref(v___y_4346_);
lean_dec_ref(v___y_4345_);
v_a_4403_ = lean_ctor_get(v___x_4387_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4387_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4405_ = v___x_4387_;
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
else
{
lean_inc(v_a_4403_);
lean_dec(v___x_4387_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
lean_object* v___x_4408_; 
if (v_isShared_4406_ == 0)
{
v___x_4408_ = v___x_4405_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v_a_4403_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
}
}
}
}
v___jp_4411_:
{
lean_object* v___x_4449_; lean_object* v___x_4450_; 
v___x_4449_ = lean_box(0);
lean_inc_ref(v___y_4416_);
lean_inc(v___y_4432_);
lean_inc_ref(v___y_4434_);
lean_inc(v___y_4431_);
lean_inc_ref(v___y_4441_);
lean_inc(v___y_4430_);
lean_inc_ref(v___y_4443_);
v___x_4450_ = lean_apply_8(v___y_4416_, v___x_4449_, v___y_4443_, v___y_4430_, v___y_4441_, v___y_4431_, v___y_4434_, v___y_4432_, lean_box(0));
if (lean_obj_tag(v___x_4450_) == 0)
{
lean_object* v_a_4451_; lean_object* v_m_4452_; lean_object* v_u_4453_; lean_object* v_v_4454_; lean_object* v___x_4455_; 
v_a_4451_ = lean_ctor_get(v___x_4450_, 0);
lean_inc(v_a_4451_);
lean_dec_ref_known(v___x_4450_, 1);
v_m_4452_ = lean_ctor_get(v___y_4433_, 0);
v_u_4453_ = lean_ctor_get(v___y_4433_, 1);
v_v_4454_ = lean_ctor_get(v___y_4433_, 2);
lean_inc(v_u_4453_);
v___x_4455_ = l_Lean_Meta_mkProdMkN(v_a_4451_, v_u_4453_, v___y_4441_, v___y_4431_, v___y_4434_, v___y_4432_);
if (lean_obj_tag(v___x_4455_) == 0)
{
lean_object* v_a_4456_; 
v_a_4456_ = lean_ctor_get(v___x_4455_, 0);
lean_inc(v_a_4456_);
lean_dec_ref_known(v___x_4455_, 1);
if (lean_obj_tag(v___y_4435_) == 0)
{
lean_object* v_fst_4457_; lean_object* v_snd_4458_; lean_object* v___x_4460_; uint8_t v_isShared_4461_; uint8_t v_isSharedCheck_4477_; 
v_fst_4457_ = lean_ctor_get(v_a_4456_, 0);
v_snd_4458_ = lean_ctor_get(v_a_4456_, 1);
v_isSharedCheck_4477_ = !lean_is_exclusive(v_a_4456_);
if (v_isSharedCheck_4477_ == 0)
{
v___x_4460_ = v_a_4456_;
v_isShared_4461_ = v_isSharedCheck_4477_;
goto v_resetjp_4459_;
}
else
{
lean_inc(v_snd_4458_);
lean_inc(v_fst_4457_);
lean_dec(v_a_4456_);
v___x_4460_ = lean_box(0);
v_isShared_4461_ = v_isSharedCheck_4477_;
goto v_resetjp_4459_;
}
v_resetjp_4459_:
{
lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4465_; 
v___x_4462_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__0));
v___x_4463_ = lean_box(0);
lean_inc(v_v_4454_);
if (v_isShared_4461_ == 0)
{
lean_ctor_set_tag(v___x_4460_, 1);
lean_ctor_set(v___x_4460_, 1, v___x_4463_);
lean_ctor_set(v___x_4460_, 0, v_v_4454_);
v___x_4465_ = v___x_4460_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v_v_4454_);
lean_ctor_set(v_reuseFailAlloc_4476_, 1, v___x_4463_);
v___x_4465_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; 
lean_inc(v_u_4453_);
v___x_4466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4466_, 0, v_u_4453_);
lean_ctor_set(v___x_4466_, 1, v___x_4465_);
v___x_4467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4467_, 0, v___y_4442_);
lean_ctor_set(v___x_4467_, 1, v___x_4466_);
v___x_4468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4468_, 0, v___y_4440_);
lean_ctor_set(v___x_4468_, 1, v___x_4467_);
lean_inc_ref(v___x_4468_);
v___x_4469_ = l_Lean_mkConst(v___x_4462_, v___x_4468_);
lean_inc_ref(v___y_4436_);
lean_inc_ref(v___y_4427_);
lean_inc_ref(v_m_4452_);
v___x_4470_ = l_Lean_mkApp3(v___x_4469_, v_m_4452_, v___y_4427_, v___y_4436_);
v___x_4471_ = l_Lean_Elab_Term_mkInstMVar(v___x_4470_, v___x_4449_, v___y_4443_, v___y_4430_, v___y_4441_, v___y_4431_, v___y_4434_, v___y_4432_);
if (lean_obj_tag(v___x_4471_) == 0)
{
lean_object* v_a_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; 
v_a_4472_ = lean_ctor_get(v___x_4471_, 0);
lean_inc(v_a_4472_);
lean_dec_ref_known(v___x_4471_, 1);
v___x_4473_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__2));
v___x_4474_ = l_Lean_mkConst(v___x_4473_, v___x_4468_);
lean_inc(v_fst_4457_);
lean_inc_ref(v___y_4439_);
lean_inc(v_snd_4458_);
lean_inc_ref(v___y_4436_);
lean_inc_ref(v_m_4452_);
v___x_4475_ = l_Lean_mkApp7(v___x_4474_, v_m_4452_, v___y_4427_, v___y_4436_, v_a_4472_, v_snd_4458_, v___y_4439_, v_fst_4457_);
lean_inc(v_u_4453_);
v___y_4345_ = v___y_4412_;
v___y_4346_ = v___y_4413_;
v___y_4347_ = v_snd_4458_;
v___y_4348_ = v___y_4414_;
v___y_4349_ = v___y_4415_;
v___y_4350_ = v___y_4417_;
v___y_4351_ = v___y_4418_;
v___y_4352_ = v___y_4416_;
v___y_4353_ = v___y_4420_;
v___y_4354_ = v___y_4419_;
v___y_4355_ = v_v_4454_;
v___y_4356_ = v___y_4421_;
v___y_4357_ = v_fst_4457_;
v___y_4358_ = v___y_4423_;
v___y_4359_ = v___y_4422_;
v___y_4360_ = v___y_4424_;
v___y_4361_ = v___x_4449_;
v___y_4362_ = v_u_4453_;
v___y_4363_ = v___y_4448_;
v___y_4364_ = v___y_4425_;
v___y_4365_ = v___y_4426_;
v___y_4366_ = v___y_4429_;
v___y_4367_ = v___y_4433_;
v___y_4368_ = v___y_4435_;
v___y_4369_ = v___y_4436_;
v___y_4370_ = v___y_4437_;
v___y_4371_ = v___y_4417_;
v___y_4372_ = v___y_4438_;
v___y_4373_ = v___y_4439_;
v___y_4374_ = v___y_4445_;
v___y_4375_ = v___y_4446_;
v___y_4376_ = v___y_4447_;
v_fst_4377_ = v___x_4475_;
v_snd_4378_ = v___x_4449_;
v___y_4379_ = v___y_4428_;
v___y_4380_ = v___y_4443_;
v___y_4381_ = v___y_4430_;
v___y_4382_ = v___y_4441_;
v___y_4383_ = v___y_4431_;
v___y_4384_ = v___y_4434_;
v___y_4385_ = v___y_4432_;
goto v___jp_4344_;
}
else
{
lean_dec_ref_known(v___x_4468_, 2);
lean_dec(v_snd_4458_);
lean_dec(v_fst_4457_);
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
lean_dec(v___y_4445_);
lean_dec_ref(v___y_4439_);
lean_dec(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec_ref(v___y_4436_);
lean_dec_ref(v___y_4429_);
lean_dec_ref(v___y_4427_);
lean_dec_ref(v___y_4426_);
lean_dec_ref(v___y_4425_);
lean_dec(v___y_4424_);
lean_dec_ref(v___y_4423_);
lean_dec(v___y_4422_);
lean_dec(v___y_4421_);
lean_dec_ref(v___y_4420_);
lean_dec(v___y_4419_);
lean_dec(v___y_4418_);
lean_dec_ref(v___y_4416_);
lean_dec_ref(v___y_4415_);
lean_dec(v___y_4414_);
lean_dec_ref(v___y_4413_);
lean_dec_ref(v___y_4412_);
return v___x_4471_;
}
}
}
}
else
{
lean_object* v_fst_4478_; lean_object* v_snd_4479_; lean_object* v___x_4481_; uint8_t v_isShared_4482_; uint8_t v_isSharedCheck_4514_; 
v_fst_4478_ = lean_ctor_get(v_a_4456_, 0);
v_snd_4479_ = lean_ctor_get(v_a_4456_, 1);
v_isSharedCheck_4514_ = !lean_is_exclusive(v_a_4456_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4481_ = v_a_4456_;
v_isShared_4482_ = v_isSharedCheck_4514_;
goto v_resetjp_4480_;
}
else
{
lean_inc(v_snd_4479_);
lean_inc(v_fst_4478_);
lean_dec(v_a_4456_);
v___x_4481_ = lean_box(0);
v_isShared_4482_ = v_isSharedCheck_4514_;
goto v_resetjp_4480_;
}
v_resetjp_4480_:
{
lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4486_; 
v___x_4483_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__3));
v___x_4484_ = lean_box(0);
lean_inc(v___y_4440_);
if (v_isShared_4482_ == 0)
{
lean_ctor_set_tag(v___x_4481_, 1);
lean_ctor_set(v___x_4481_, 1, v___x_4484_);
lean_ctor_set(v___x_4481_, 0, v___y_4440_);
v___x_4486_ = v___x_4481_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v___y_4440_);
lean_ctor_set(v_reuseFailAlloc_4513_, 1, v___x_4484_);
v___x_4486_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; 
lean_inc(v___y_4442_);
v___x_4487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4487_, 0, v___y_4442_);
lean_ctor_set(v___x_4487_, 1, v___x_4486_);
v___x_4488_ = l_Lean_mkConst(v___x_4483_, v___x_4487_);
lean_inc_ref(v___y_4427_);
lean_inc_ref(v___y_4436_);
v___x_4489_ = l_Lean_mkAppB(v___x_4488_, v___y_4436_, v___y_4427_);
v___x_4490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4490_, 0, v___x_4489_);
v___x_4491_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__5));
v___x_4492_ = l_Lean_Meta_mkFreshExprMVar(v___x_4490_, v___y_4444_, v___x_4491_, v___y_4441_, v___y_4431_, v___y_4434_, v___y_4432_);
if (lean_obj_tag(v___x_4492_) == 0)
{
lean_object* v_a_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; 
v_a_4493_ = lean_ctor_get(v___x_4492_, 0);
lean_inc_n(v_a_4493_, 2);
lean_dec_ref_known(v___x_4492_, 1);
v___x_4494_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__6));
lean_inc(v_v_4454_);
v___x_4495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4495_, 0, v_v_4454_);
lean_ctor_set(v___x_4495_, 1, v___x_4484_);
lean_inc(v_u_4453_);
v___x_4496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4496_, 0, v_u_4453_);
lean_ctor_set(v___x_4496_, 1, v___x_4495_);
v___x_4497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4497_, 0, v___y_4442_);
lean_ctor_set(v___x_4497_, 1, v___x_4496_);
v___x_4498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4498_, 0, v___y_4440_);
lean_ctor_set(v___x_4498_, 1, v___x_4497_);
lean_inc_ref(v___x_4498_);
v___x_4499_ = l_Lean_mkConst(v___x_4494_, v___x_4498_);
lean_inc_ref(v___y_4436_);
lean_inc_ref(v___y_4427_);
lean_inc_ref(v_m_4452_);
v___x_4500_ = l_Lean_mkApp4(v___x_4499_, v_m_4452_, v___y_4427_, v___y_4436_, v_a_4493_);
v___x_4501_ = l_Lean_Elab_Term_mkInstMVar(v___x_4500_, v___x_4449_, v___y_4443_, v___y_4430_, v___y_4441_, v___y_4431_, v___y_4434_, v___y_4432_);
if (lean_obj_tag(v___x_4501_) == 0)
{
lean_object* v_a_4502_; lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4512_; 
v_a_4502_ = lean_ctor_get(v___x_4501_, 0);
v_isSharedCheck_4512_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4512_ == 0)
{
v___x_4504_ = v___x_4501_;
v_isShared_4505_ = v_isSharedCheck_4512_;
goto v_resetjp_4503_;
}
else
{
lean_inc(v_a_4502_);
lean_dec(v___x_4501_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4512_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4510_; 
v___x_4506_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__8));
v___x_4507_ = l_Lean_mkConst(v___x_4506_, v___x_4498_);
lean_inc(v_fst_4478_);
lean_inc_ref(v___y_4439_);
lean_inc(v_snd_4479_);
lean_inc(v_a_4493_);
lean_inc_ref(v___y_4436_);
lean_inc_ref(v_m_4452_);
v___x_4508_ = l_Lean_mkApp8(v___x_4507_, v_m_4452_, v___y_4427_, v___y_4436_, v_a_4493_, v_a_4502_, v_snd_4479_, v___y_4439_, v_fst_4478_);
if (v_isShared_4505_ == 0)
{
lean_ctor_set_tag(v___x_4504_, 1);
lean_ctor_set(v___x_4504_, 0, v_a_4493_);
v___x_4510_ = v___x_4504_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v_a_4493_);
v___x_4510_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
lean_inc(v_u_4453_);
v___y_4345_ = v___y_4412_;
v___y_4346_ = v___y_4413_;
v___y_4347_ = v_snd_4479_;
v___y_4348_ = v___y_4414_;
v___y_4349_ = v___y_4415_;
v___y_4350_ = v___y_4417_;
v___y_4351_ = v___y_4418_;
v___y_4352_ = v___y_4416_;
v___y_4353_ = v___y_4420_;
v___y_4354_ = v___y_4419_;
v___y_4355_ = v_v_4454_;
v___y_4356_ = v___y_4421_;
v___y_4357_ = v_fst_4478_;
v___y_4358_ = v___y_4423_;
v___y_4359_ = v___y_4422_;
v___y_4360_ = v___y_4424_;
v___y_4361_ = v___x_4449_;
v___y_4362_ = v_u_4453_;
v___y_4363_ = v___y_4448_;
v___y_4364_ = v___y_4425_;
v___y_4365_ = v___y_4426_;
v___y_4366_ = v___y_4429_;
v___y_4367_ = v___y_4433_;
v___y_4368_ = v___y_4435_;
v___y_4369_ = v___y_4436_;
v___y_4370_ = v___y_4437_;
v___y_4371_ = v___y_4417_;
v___y_4372_ = v___y_4438_;
v___y_4373_ = v___y_4439_;
v___y_4374_ = v___y_4445_;
v___y_4375_ = v___y_4446_;
v___y_4376_ = v___y_4447_;
v_fst_4377_ = v___x_4508_;
v_snd_4378_ = v___x_4510_;
v___y_4379_ = v___y_4428_;
v___y_4380_ = v___y_4443_;
v___y_4381_ = v___y_4430_;
v___y_4382_ = v___y_4441_;
v___y_4383_ = v___y_4431_;
v___y_4384_ = v___y_4434_;
v___y_4385_ = v___y_4432_;
goto v___jp_4344_;
}
}
}
else
{
lean_dec_ref_known(v___x_4498_, 2);
lean_dec(v_a_4493_);
lean_dec(v_snd_4479_);
lean_dec(v_fst_4478_);
lean_dec_ref_known(v___y_4435_, 1);
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
lean_dec(v___y_4445_);
lean_dec_ref(v___y_4439_);
lean_dec(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec_ref(v___y_4436_);
lean_dec_ref(v___y_4429_);
lean_dec_ref(v___y_4427_);
lean_dec_ref(v___y_4426_);
lean_dec_ref(v___y_4425_);
lean_dec(v___y_4424_);
lean_dec_ref(v___y_4423_);
lean_dec(v___y_4422_);
lean_dec(v___y_4421_);
lean_dec_ref(v___y_4420_);
lean_dec(v___y_4419_);
lean_dec(v___y_4418_);
lean_dec_ref(v___y_4416_);
lean_dec_ref(v___y_4415_);
lean_dec(v___y_4414_);
lean_dec_ref(v___y_4413_);
lean_dec_ref(v___y_4412_);
return v___x_4501_;
}
}
else
{
lean_dec(v_snd_4479_);
lean_dec(v_fst_4478_);
lean_dec_ref_known(v___y_4435_, 1);
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
lean_dec(v___y_4445_);
lean_dec(v___y_4442_);
lean_dec(v___y_4440_);
lean_dec_ref(v___y_4439_);
lean_dec(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec_ref(v___y_4436_);
lean_dec_ref(v___y_4429_);
lean_dec_ref(v___y_4427_);
lean_dec_ref(v___y_4426_);
lean_dec_ref(v___y_4425_);
lean_dec(v___y_4424_);
lean_dec_ref(v___y_4423_);
lean_dec(v___y_4422_);
lean_dec(v___y_4421_);
lean_dec_ref(v___y_4420_);
lean_dec(v___y_4419_);
lean_dec(v___y_4418_);
lean_dec_ref(v___y_4416_);
lean_dec_ref(v___y_4415_);
lean_dec(v___y_4414_);
lean_dec_ref(v___y_4413_);
lean_dec_ref(v___y_4412_);
return v___x_4492_;
}
}
}
}
}
else
{
lean_object* v_a_4515_; lean_object* v___x_4517_; uint8_t v_isShared_4518_; uint8_t v_isSharedCheck_4522_; 
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
lean_dec(v___y_4445_);
lean_dec(v___y_4442_);
lean_dec(v___y_4440_);
lean_dec_ref(v___y_4439_);
lean_dec(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec_ref(v___y_4436_);
lean_dec(v___y_4435_);
lean_dec_ref(v___y_4429_);
lean_dec_ref(v___y_4427_);
lean_dec_ref(v___y_4426_);
lean_dec_ref(v___y_4425_);
lean_dec(v___y_4424_);
lean_dec_ref(v___y_4423_);
lean_dec(v___y_4422_);
lean_dec(v___y_4421_);
lean_dec_ref(v___y_4420_);
lean_dec(v___y_4419_);
lean_dec(v___y_4418_);
lean_dec_ref(v___y_4416_);
lean_dec_ref(v___y_4415_);
lean_dec(v___y_4414_);
lean_dec_ref(v___y_4413_);
lean_dec_ref(v___y_4412_);
v_a_4515_ = lean_ctor_get(v___x_4455_, 0);
v_isSharedCheck_4522_ = !lean_is_exclusive(v___x_4455_);
if (v_isSharedCheck_4522_ == 0)
{
v___x_4517_ = v___x_4455_;
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
else
{
lean_inc(v_a_4515_);
lean_dec(v___x_4455_);
v___x_4517_ = lean_box(0);
v_isShared_4518_ = v_isSharedCheck_4522_;
goto v_resetjp_4516_;
}
v_resetjp_4516_:
{
lean_object* v___x_4520_; 
if (v_isShared_4518_ == 0)
{
v___x_4520_ = v___x_4517_;
goto v_reusejp_4519_;
}
else
{
lean_object* v_reuseFailAlloc_4521_; 
v_reuseFailAlloc_4521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4521_, 0, v_a_4515_);
v___x_4520_ = v_reuseFailAlloc_4521_;
goto v_reusejp_4519_;
}
v_reusejp_4519_:
{
return v___x_4520_;
}
}
}
}
else
{
lean_object* v_a_4523_; lean_object* v___x_4525_; uint8_t v_isShared_4526_; uint8_t v_isSharedCheck_4530_; 
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
lean_dec(v___y_4445_);
lean_dec(v___y_4442_);
lean_dec(v___y_4440_);
lean_dec_ref(v___y_4439_);
lean_dec(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec_ref(v___y_4436_);
lean_dec(v___y_4435_);
lean_dec_ref(v___y_4429_);
lean_dec_ref(v___y_4427_);
lean_dec_ref(v___y_4426_);
lean_dec_ref(v___y_4425_);
lean_dec(v___y_4424_);
lean_dec_ref(v___y_4423_);
lean_dec(v___y_4422_);
lean_dec(v___y_4421_);
lean_dec_ref(v___y_4420_);
lean_dec(v___y_4419_);
lean_dec(v___y_4418_);
lean_dec_ref(v___y_4416_);
lean_dec_ref(v___y_4415_);
lean_dec(v___y_4414_);
lean_dec_ref(v___y_4413_);
lean_dec_ref(v___y_4412_);
v_a_4523_ = lean_ctor_get(v___x_4450_, 0);
v_isSharedCheck_4530_ = !lean_is_exclusive(v___x_4450_);
if (v_isSharedCheck_4530_ == 0)
{
v___x_4525_ = v___x_4450_;
v_isShared_4526_ = v_isSharedCheck_4530_;
goto v_resetjp_4524_;
}
else
{
lean_inc(v_a_4523_);
lean_dec(v___x_4450_);
v___x_4525_ = lean_box(0);
v_isShared_4526_ = v_isSharedCheck_4530_;
goto v_resetjp_4524_;
}
v_resetjp_4524_:
{
lean_object* v___x_4528_; 
if (v_isShared_4526_ == 0)
{
v___x_4528_ = v___x_4525_;
goto v_reusejp_4527_;
}
else
{
lean_object* v_reuseFailAlloc_4529_; 
v_reuseFailAlloc_4529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4529_, 0, v_a_4523_);
v___x_4528_ = v_reuseFailAlloc_4529_;
goto v_reusejp_4527_;
}
v_reusejp_4527_:
{
return v___x_4528_;
}
}
}
}
v___jp_4531_:
{
uint8_t v_returnsEarly_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___f_4571_; 
v_returnsEarly_4568_ = lean_ctor_get_uint8(v___y_4564_, sizeof(void*)*2 + 2);
lean_dec_ref(v___y_4564_);
v___x_4569_ = lean_box(v_returnsEarly_4568_);
v___x_4570_ = lean_box(v___y_4533_);
lean_inc_ref(v___y_4547_);
lean_inc_ref(v___y_4534_);
lean_inc_ref(v___y_4567_);
v___f_4571_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__3___boxed), 14, 6);
lean_closure_set(v___f_4571_, 0, v___y_4567_);
lean_closure_set(v___f_4571_, 1, v___y_4534_);
lean_closure_set(v___f_4571_, 2, v___x_4569_);
lean_closure_set(v___f_4571_, 3, v___x_4227_);
lean_closure_set(v___f_4571_, 4, v___y_4547_);
lean_closure_set(v___f_4571_, 5, v___x_4570_);
if (v_returnsEarly_4568_ == 0)
{
size_t v_sz_4572_; size_t v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; 
lean_dec(v___y_4557_);
v_sz_4572_ = lean_array_size(v___y_4567_);
v___x_4573_ = ((size_t)0ULL);
lean_inc_ref_n(v___y_4567_, 2);
v___x_4574_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__5(v_sz_4572_, v___x_4573_, v___y_4567_);
v___x_4575_ = lean_array_to_list(v___x_4574_);
v___y_4412_ = v___y_4532_;
v___y_4413_ = v___y_4567_;
v___y_4414_ = v___y_4535_;
v___y_4415_ = v___y_4537_;
v___y_4416_ = v___f_4571_;
v___y_4417_ = v_returnsEarly_4568_;
v___y_4418_ = v___y_4538_;
v___y_4419_ = v___y_4539_;
v___y_4420_ = v___y_4540_;
v___y_4421_ = v___y_4541_;
v___y_4422_ = v___y_4542_;
v___y_4423_ = v___y_4543_;
v___y_4424_ = v___y_4544_;
v___y_4425_ = v___y_4546_;
v___y_4426_ = v___y_4547_;
v___y_4427_ = v___y_4548_;
v___y_4428_ = v___y_4549_;
v___y_4429_ = v___y_4567_;
v___y_4430_ = v___y_4550_;
v___y_4431_ = v___y_4551_;
v___y_4432_ = v___y_4552_;
v___y_4433_ = v___y_4534_;
v___y_4434_ = v___y_4553_;
v___y_4435_ = v___y_4554_;
v___y_4436_ = v___y_4555_;
v___y_4437_ = v___y_4536_;
v___y_4438_ = v___y_4556_;
v___y_4439_ = v___y_4558_;
v___y_4440_ = v___y_4559_;
v___y_4441_ = v___y_4560_;
v___y_4442_ = v___y_4562_;
v___y_4443_ = v___y_4561_;
v___y_4444_ = v___y_4563_;
v___y_4445_ = v___y_4565_;
v___y_4446_ = v___y_4566_;
v___y_4447_ = v___y_4545_;
v___y_4448_ = v___x_4575_;
goto v___jp_4411_;
}
else
{
size_t v_sz_4576_; size_t v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; 
v_sz_4576_ = lean_array_size(v___y_4567_);
v___x_4577_ = ((size_t)0ULL);
lean_inc_ref_n(v___y_4567_, 2);
v___x_4578_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__5(v_sz_4576_, v___x_4577_, v___y_4567_);
v___x_4579_ = lean_array_to_list(v___x_4578_);
v___x_4580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4580_, 0, v___y_4557_);
lean_ctor_set(v___x_4580_, 1, v___x_4579_);
v___y_4412_ = v___y_4532_;
v___y_4413_ = v___y_4567_;
v___y_4414_ = v___y_4535_;
v___y_4415_ = v___y_4537_;
v___y_4416_ = v___f_4571_;
v___y_4417_ = v_returnsEarly_4568_;
v___y_4418_ = v___y_4538_;
v___y_4419_ = v___y_4539_;
v___y_4420_ = v___y_4540_;
v___y_4421_ = v___y_4541_;
v___y_4422_ = v___y_4542_;
v___y_4423_ = v___y_4543_;
v___y_4424_ = v___y_4544_;
v___y_4425_ = v___y_4546_;
v___y_4426_ = v___y_4547_;
v___y_4427_ = v___y_4548_;
v___y_4428_ = v___y_4549_;
v___y_4429_ = v___y_4567_;
v___y_4430_ = v___y_4550_;
v___y_4431_ = v___y_4551_;
v___y_4432_ = v___y_4552_;
v___y_4433_ = v___y_4534_;
v___y_4434_ = v___y_4553_;
v___y_4435_ = v___y_4554_;
v___y_4436_ = v___y_4555_;
v___y_4437_ = v___y_4536_;
v___y_4438_ = v___y_4556_;
v___y_4439_ = v___y_4558_;
v___y_4440_ = v___y_4559_;
v___y_4441_ = v___y_4560_;
v___y_4442_ = v___y_4562_;
v___y_4443_ = v___y_4561_;
v___y_4444_ = v___y_4563_;
v___y_4445_ = v___y_4565_;
v___y_4446_ = v___y_4566_;
v___y_4447_ = v___y_4545_;
v___y_4448_ = v___x_4580_;
goto v___jp_4411_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___boxed(lean_object* v_stx_4752_, lean_object* v_dec_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_, lean_object* v_a_4761_){
_start:
{
lean_object* v_res_4762_; 
v_res_4762_ = l_Lean_Elab_Do_elabDoFor(v_stx_4752_, v_dec_4753_, v_a_4754_, v_a_4755_, v_a_4756_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_);
lean_dec(v_a_4760_);
lean_dec_ref(v_a_4759_);
lean_dec(v_a_4758_);
lean_dec_ref(v_a_4757_);
lean_dec(v_a_4756_);
lean_dec_ref(v_a_4755_);
lean_dec_ref(v_a_4754_);
return v_res_4762_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1(lean_object* v_00_u03b1_4763_, lean_object* v_msg_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_){
_start:
{
lean_object* v___x_4772_; 
v___x_4772_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___redArg(v_msg_4764_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_, v___y_4770_);
return v___x_4772_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___boxed(lean_object* v_00_u03b1_4773_, lean_object* v_msg_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_){
_start:
{
lean_object* v_res_4782_; 
v_res_4782_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1(v_00_u03b1_4773_, v_msg_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_, v___y_4780_);
lean_dec(v___y_4780_);
lean_dec_ref(v___y_4779_);
lean_dec(v___y_4778_);
lean_dec_ref(v___y_4777_);
lean_dec(v___y_4776_);
lean_dec_ref(v___y_4775_);
return v_res_4782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2(lean_object* v_00_u03b1_4783_, lean_object* v_name_4784_, lean_object* v_type_4785_, lean_object* v_k_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_){
_start:
{
lean_object* v___x_4795_; 
v___x_4795_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v_name_4784_, v_type_4785_, v_k_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_, v___y_4793_);
return v___x_4795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___boxed(lean_object* v_00_u03b1_4796_, lean_object* v_name_4797_, lean_object* v_type_4798_, lean_object* v_k_4799_, lean_object* v___y_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_){
_start:
{
lean_object* v_res_4808_; 
v_res_4808_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2(v_00_u03b1_4796_, v_name_4797_, v_type_4798_, v_k_4799_, v___y_4800_, v___y_4801_, v___y_4802_, v___y_4803_, v___y_4804_, v___y_4805_, v___y_4806_);
lean_dec(v___y_4806_);
lean_dec_ref(v___y_4805_);
lean_dec(v___y_4804_);
lean_dec_ref(v___y_4803_);
lean_dec(v___y_4802_);
lean_dec_ref(v___y_4801_);
lean_dec_ref(v___y_4800_);
return v_res_4808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1(lean_object* v_msgData_4809_, lean_object* v_macroStack_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_, lean_object* v___y_4816_){
_start:
{
lean_object* v___x_4818_; 
v___x_4818_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg(v_msgData_4809_, v_macroStack_4810_, v___y_4815_);
return v___x_4818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___boxed(lean_object* v_msgData_4819_, lean_object* v_macroStack_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_){
_start:
{
lean_object* v_res_4828_; 
v_res_4828_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1(v_msgData_4819_, v_macroStack_4820_, v___y_4821_, v___y_4822_, v___y_4823_, v___y_4824_, v___y_4825_, v___y_4826_);
lean_dec(v___y_4826_);
lean_dec_ref(v___y_4825_);
lean_dec(v___y_4824_);
lean_dec_ref(v___y_4823_);
lean_dec(v___y_4822_);
lean_dec_ref(v___y_4821_);
return v_res_4828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1(){
_start:
{
lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; 
v___x_4836_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_4837_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
v___x_4838_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1));
v___x_4839_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___boxed), 10, 0);
v___x_4840_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4836_, v___x_4837_, v___x_4838_, v___x_4839_);
return v___x_4840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___boxed(lean_object* v_a_4841_){
_start:
{
lean_object* v_res_4842_; 
v_res_4842_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1();
return v_res_4842_;
}
}
lean_object* runtime_initialize_Lean_Elab_BuiltinDo_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Do(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_ProdN(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_BuiltinDo_For(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_BuiltinDo_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
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
lean_object* initialize_Init_While(uint8_t builtin);
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
res = initialize_Init_While(builtin);
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
