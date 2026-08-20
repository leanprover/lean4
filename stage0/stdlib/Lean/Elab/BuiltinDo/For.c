// Lean compiler output
// Module: Lean.Elab.BuiltinDo.For
// Imports: public import Lean.Elab.BuiltinDo.Basic meta import Lean.Parser.Do meta import Std.WP.Gadget.ForIn import Init.Control.Do import Init.While import Lean.Meta.ProdN
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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Term_exprToSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray2___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_Do_MutVar_getId(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Array_mkArray3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getForallArity(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_mkMonadApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_continueWithUnit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSimpleThunk(lean_object*);
lean_object* l_Lean_Meta_getFVarFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDeclFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Elab_Term_addTermInfo_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLevelDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_mkBindApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkInstMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSome(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_ensureUnitAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_checkMutVarsForShadowing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_getReturnCont___redArg(lean_object*);
extern lean_object* l_Lean_Elab_Do_experimental_intrinsic;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l_Lean_Elab_Do_expandDoFor___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__4 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__4_value;
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "in"};
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
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "doLoopDecreasing"};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__16 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__17_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__17_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__17_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__16_value),LEAN_SCALAR_PTR_LITERAL(0, 112, 64, 8, 91, 183, 41, 148)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__17 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__17_value;
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "doLoopInvariant"};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__18 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__19_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__19_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__19_value_aux_2),((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__18_value),LEAN_SCALAR_PTR_LITERAL(207, 155, 107, 150, 202, 64, 185, 181)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__19 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__19_value;
static const lean_string_object l_Lean_Elab_Do_expandDoFor___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__20 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Do_expandDoFor___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__20_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Do_expandDoFor___closed__21 = (const lean_object*)&l_Lean_Elab_Do_expandDoFor___closed__21_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "WP"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "WPMonad"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(202, 83, 143, 139, 231, 107, 0, 192)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "The "};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__1;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = " of a loop in this monad takes "};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__3;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = ", and this clause has "};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__5;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = ". The loop's mutable variables are named without binding them."};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__6 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__7;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " binders"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__8 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__9;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "one binder"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__10 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__11;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " arguments"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__12 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__12_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__13;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "one argument"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__14 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__14_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__15;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "arrow"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__1___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__1___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__1___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__1___redArg___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__1___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__1___redArg___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__1___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(182, 146, 143, 73, 122, 115, 5, 207)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__1___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "→"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__3_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__3_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__2_value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__3_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__5_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__5_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__4_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__5 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__6_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__6_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__6_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__60_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__6 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__7_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__7_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__7 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__7_value)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__8 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__9_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__68_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__9 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__9_value)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__10 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__11_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__11_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__11 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__11_value)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__12 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__13 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__10_value),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__13_value)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__14 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__8_value),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__14_value)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__15 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__15_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "anonymousCtor"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 53, 154, 97, 179, 232, 94, 186)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__2_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkStateFun___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkStateFun___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkStateFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkStateFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "open"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__0_value),LEAN_SCALAR_PTR_LITERAL(77, 46, 79, 112, 232, 100, 17, 35)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__2_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "openScoped"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__4_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__3_value),LEAN_SCALAR_PTR_LITERAL(55, 166, 237, 23, 37, 47, 5, 133)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__4_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scoped"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__5 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__5_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Std.WP"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__6 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__7;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__8 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__8_value)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__9 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__10 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__10_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Lean.Order"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__11 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__11_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__12;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__13 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__13_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__14 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__14_value)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__15 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__16 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__16_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 81, .m_capacity = 81, .m_length = 80, .m_data = "a loop annotation elaborates to a `vcgen` gadget; add `import Std.WP` to use it."};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__17 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__17_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__18;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__0_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 164, .m_capacity = 164, .m_length = 162, .m_data = "The `invariant` clause takes no type ascription covering all its binders; ascribe the type on an individual binder, as in `invariant (pref : List α) suff => ...`."};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "invariant"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__0_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Gadget"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "forInPureWithInvariant"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(193, 119, 194, 233, 172, 109, 107, 25)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__2_value),LEAN_SCALAR_PTR_LITERAL(183, 165, 133, 99, 223, 97, 236, 183)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__3_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "forInPureWithInvariant'"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(193, 119, 194, 233, 172, 109, 107, 25)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__4_value),LEAN_SCALAR_PTR_LITERAL(107, 130, 88, 65, 130, 23, 203, 175)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__5 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__5_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 108, .m_capacity = 108, .m_length = 107, .m_data = "The `invariant` clause takes at least two binders: the elements consumed so far and the elements remaining."};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__6 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "measure"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "WhileInvariant"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 42, 207, 185, 94, 183, 123, 103)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(249, 129, 117, 90, 117, 252, 244, 94)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "forInLoopWithVariant"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(193, 119, 194, 233, 172, 109, 107, 25)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(31, 161, 208, 243, 4, 56, 187, 242)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "forInLoopWithInvariant"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(193, 119, 194, 233, 172, 109, 107, 25)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__2_value),LEAN_SCALAR_PTR_LITERAL(86, 62, 119, 157, 208, 178, 34, 119)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__3_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "forInLoopWithInvariantAndVariant"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__1_value),LEAN_SCALAR_PTR_LITERAL(193, 119, 194, 233, 172, 109, 107, 25)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__4_value),LEAN_SCALAR_PTR_LITERAL(100, 75, 86, 181, 82, 124, 122, 58)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__5 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__5_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "__exit"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__6 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__6_value),LEAN_SCALAR_PTR_LITERAL(225, 46, 225, 83, 109, 75, 189, 208)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__7 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__8_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__8_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__8_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(9, 208, 235, 82, 91, 230, 203, 159)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__8 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__10___boxed(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unit"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__1___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(87, 186, 243, 194, 96, 12, 218, 7)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoFor___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoFor___lam__1___closed__3;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = " but the info said there is no early return"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__1___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoFor___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoFor___lam__1___closed__5;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Early returning "};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__1___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoFor___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoFor___lam__1___closed__7;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "<not-available>"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__1___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__1___closed__8_value)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__1___closed__9 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__1___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoFor___lam__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoFor___lam__1___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "r"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(201, 206, 29, 183, 206, 15, 98, 41)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(168, 60, 211, 188, 58, 220, 100, 184)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__2_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Break"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___closed__3 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "runK"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__4_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "match_1"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___closed__5 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__3___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(25, 204, 143, 3, 84, 67, 92, 151)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__3___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 178, 64, 100, 79, 118, 122, 28)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__5_value),LEAN_SCALAR_PTR_LITERAL(199, 194, 234, 57, 172, 104, 157, 179)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__6_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prod"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___closed__7 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__7_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fst"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___closed__8 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__3___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__7_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__8_value),LEAN_SCALAR_PTR_LITERAL(170, 44, 236, 58, 247, 164, 254, 114)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___closed__9 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__3___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "done"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__5___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__5___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "yield"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__6___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__6___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ForInStep"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__9___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__9___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(153, 23, 255, 201, 194, 179, 65, 111)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__9___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__9___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Membership"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__11___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__11___closed__0_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___lam__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mem"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__11___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__11___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__11___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__11___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 217, 109, 94, 255, 55, 82, 109)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___lam__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__11___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__11___closed__1_value),LEAN_SCALAR_PTR_LITERAL(224, 90, 126, 237, 128, 148, 153, 69)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___lam__11___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__11___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 165, .m_capacity = 165, .m_length = 164, .m_data = " is part of the experimental intrinsic verification syntax; `set_option experimental.intrinsic true` acknowledges its experimental status and silences this warning."};
static const lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7___closed__0 = (const lean_object*)&l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__1;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__2 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__3 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__4 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__5 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__5_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__6 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__6_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__7 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6___closed__0 = (const lean_object*)&l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Loop"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 180, 170, 243, 159, 48, 205, 98)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__1 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 132, .m_capacity = 132, .m_length = 131, .m_data = "A `for` loop terminates with the collection it iterates; `decreasing` states the termination measure of a `repeat` or `while` loop."};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__2 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoFor___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoFor___closed__3;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ForIn"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__4 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 152, 230, 155, 97, 233, 45, 158)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__5 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__5_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "forIn"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__6 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 152, 230, 155, 97, 233, 45, 158)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__6_value),LEAN_SCALAR_PTR_LITERAL(9, 12, 142, 239, 44, 138, 10, 93)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__7 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___lam__11___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 217, 109, 94, 255, 55, 82, 109)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__8 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__8_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "d"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__9 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__9_value),LEAN_SCALAR_PTR_LITERAL(48, 234, 148, 175, 115, 149, 2, 231)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__10 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__10_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ForIn'"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__11 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__11_value),LEAN_SCALAR_PTR_LITERAL(75, 251, 229, 162, 252, 35, 196, 120)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__12 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__12_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "forIn'"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__13 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__11_value),LEAN_SCALAR_PTR_LITERAL(75, 251, 229, 162, 252, 35, 196, 120)}};
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__13_value),LEAN_SCALAR_PTR_LITERAL(10, 254, 232, 131, 195, 189, 138, 93)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__14 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__14_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "α"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__15 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__15_value),LEAN_SCALAR_PTR_LITERAL(102, 24, 27, 80, 217, 159, 184, 13)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__16 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__16_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "ρ"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__17 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__17_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__17_value),LEAN_SCALAR_PTR_LITERAL(148, 87, 172, 24, 54, 35, 28, 246)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__18 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__18_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "__r"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__19 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__19_value;
static const lean_ctor_object l_Lean_Elab_Do_elabDoFor___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__19_value),LEAN_SCALAR_PTR_LITERAL(38, 26, 183, 93, 43, 136, 227, 87)}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__20 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__20_value;
static const lean_array_object l_Lean_Elab_Do_elabDoFor___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__21 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__21_value;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "`decreasing` clause"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__22 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__22_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoFor___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoFor___closed__23;
static const lean_string_object l_Lean_Elab_Do_elabDoFor___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "`invariant` clause"};
static const lean_object* l_Lean_Elab_Do_elabDoFor___closed__24 = (const lean_object*)&l_Lean_Elab_Do_elabDoFor___closed__24_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoFor___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoFor___closed__25;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_202988__boxed_428_; lean_object* v_res_429_; 
v___x_202988__boxed_428_ = lean_unbox(v___x_416_);
v_res_429_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(v___x_413_, v___x_414_, v___x_415_, v___x_202988__boxed_428_, v___x_417_, v___x_418_, v___x_419_, v___f_420_, v_fst_421_, v___x_422_, v_snd_423_, v_x_424_, v_h_x3f_425_, v___y_426_, v___y_427_);
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
uint8_t v___x_203594__boxed_440_; lean_object* v_res_441_; 
v___x_203594__boxed_440_ = lean_unbox(v___x_436_);
v_res_441_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0(v___x_203594__boxed_440_, v_____do__lift_437_, v___y_438_, v___y_439_);
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
uint8_t v___x_203630__boxed_559_; lean_object* v_res_560_; 
v___x_203630__boxed_559_ = lean_unbox(v___x_554_);
v_res_560_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_203630__boxed_559_, v_a_555_, v_b_556_, v___y_557_, v___y_558_);
lean_dec_ref(v___y_557_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___lam__1(lean_object* v___x_561_, lean_object* v___x_562_, lean_object* v___x_563_, lean_object* v___x_564_, lean_object* v___x_565_, lean_object* v___x_566_, lean_object* v___f_567_, lean_object* v_fst_568_, lean_object* v___x_569_, lean_object* v_snd_570_, lean_object* v_x_571_, lean_object* v_h_x3f_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___y_578_; 
v___x_575_ = l_Lean_Syntax_getArg(v___x_561_, v___x_562_);
v___x_576_ = l_Lean_Syntax_getArg(v___x_561_, v___x_563_);
if (lean_obj_tag(v_h_x3f_572_) == 1)
{
lean_object* v_val_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v_val_797_ = lean_ctor_get(v_h_x3f_572_, 0);
v___x_798_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__77));
v___x_799_ = l_Lean_Macro_throwErrorAt___redArg(v_val_797_, v___x_798_, v___y_573_, v___y_574_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; 
v_a_800_ = lean_ctor_get(v___x_799_, 1);
lean_inc(v_a_800_);
lean_dec_ref_known(v___x_799_, 2);
v___y_578_ = v_a_800_;
goto v___jp_577_;
}
else
{
lean_object* v_a_801_; lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
lean_dec(v___x_576_);
lean_dec(v___x_575_);
lean_dec(v_snd_570_);
lean_dec_ref(v___x_569_);
lean_dec(v_fst_568_);
lean_dec_ref(v___f_567_);
lean_dec_ref(v___x_566_);
lean_dec_ref(v___x_565_);
lean_dec_ref(v___x_564_);
v_a_801_ = lean_ctor_get(v___x_799_, 0);
v_a_802_ = lean_ctor_get(v___x_799_, 1);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_799_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_inc(v_a_801_);
lean_dec(v___x_799_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_801_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_a_802_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
else
{
v___y_578_ = v___y_574_;
goto v___jp_577_;
}
v___jp_577_:
{
lean_object* v_quotContext_579_; lean_object* v_currMacroScope_580_; lean_object* v_ref_581_; lean_object* v_ref_582_; uint8_t v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v_macroScope_605_; lean_object* v_traceMsgs_606_; lean_object* v_expandedMacroDecls_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_796_; 
v_quotContext_579_ = lean_ctor_get(v___y_573_, 1);
v_currMacroScope_580_ = lean_ctor_get(v___y_573_, 2);
v_ref_581_ = lean_ctor_get(v___y_573_, 5);
v_ref_582_ = l_Lean_replaceRef(v___x_576_, v_ref_581_);
v___x_583_ = 0;
v___x_584_ = l_Lean_SourceInfo_fromRef(v_ref_582_, v___x_583_);
lean_dec(v_ref_582_);
v___x_585_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__0));
lean_inc_ref_n(v___x_566_, 3);
lean_inc_ref_n(v___x_565_, 3);
lean_inc_ref_n(v___x_564_, 3);
v___x_586_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_585_);
v___x_587_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__1));
v___x_588_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_587_);
v___x_589_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__2));
lean_inc_n(v___x_584_, 6);
v___x_590_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_584_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4);
v___x_592_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7));
lean_inc(v_currMacroScope_580_);
lean_inc(v_quotContext_579_);
v___x_593_ = l_Lean_addMacroScope(v_quotContext_579_, v___x_592_, v_currMacroScope_580_);
v___x_594_ = lean_box(0);
v___x_595_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__11));
v___x_596_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_596_, 0, v___x_584_);
lean_ctor_set(v___x_596_, 1, v___x_591_);
lean_ctor_set(v___x_596_, 2, v___x_593_);
lean_ctor_set(v___x_596_, 3, v___x_595_);
lean_inc(v___x_588_);
v___x_597_ = l_Lean_Syntax_node2(v___x_584_, v___x_588_, v___x_590_, v___x_596_);
v___x_598_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_599_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__14));
v___x_600_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_599_);
v___x_601_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15));
v___x_602_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_584_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
lean_inc(v___x_600_);
v___x_603_ = l_Lean_Syntax_node1(v___x_584_, v___x_600_, v___x_602_);
lean_inc(v___x_576_);
lean_inc_n(v___x_603_, 2);
v___x_604_ = l_Lean_Syntax_node4(v___x_584_, v___x_598_, v___x_603_, v___x_603_, v___x_603_, v___x_576_);
v_macroScope_605_ = lean_ctor_get(v___y_578_, 0);
v_traceMsgs_606_ = lean_ctor_get(v___y_578_, 1);
v_expandedMacroDecls_607_ = lean_ctor_get(v___y_578_, 2);
v_isSharedCheck_796_ = !lean_is_exclusive(v___y_578_);
if (v_isSharedCheck_796_ == 0)
{
v___x_609_ = v___y_578_;
v_isShared_610_ = v_isSharedCheck_796_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_expandedMacroDecls_607_);
lean_inc(v_traceMsgs_606_);
lean_inc(v_macroScope_605_);
lean_dec(v___y_578_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_796_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_611_ = lean_nat_add(v_macroScope_605_, v___x_562_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v___x_611_);
v___x_613_ = v___x_609_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v_traceMsgs_606_);
lean_ctor_set(v_reuseFailAlloc_795_, 2, v_expandedMacroDecls_607_);
v___x_613_ = v_reuseFailAlloc_795_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_614_; 
lean_inc_ref(v___f_567_);
lean_inc_ref(v___y_573_);
lean_inc(v_ref_581_);
v___x_614_ = lean_apply_3(v___f_567_, v_ref_581_, v___y_573_, v___x_613_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v_a_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc_n(v_a_615_, 9);
v_a_616_ = lean_ctor_get(v___x_614_, 1);
lean_inc(v_a_616_);
lean_dec_ref_known(v___x_614_, 2);
lean_inc(v___x_586_);
v___x_617_ = l_Lean_Syntax_node2(v___x_584_, v___x_586_, v___x_597_, v___x_604_);
v___x_618_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17));
lean_inc(v_quotContext_579_);
v___x_619_ = l_Lean_addMacroScope(v_quotContext_579_, v___x_618_, v_macroScope_605_);
v___x_620_ = l_Lean_mkIdentFrom(v___x_576_, v___x_619_, v___x_583_);
lean_dec(v___x_576_);
v___x_621_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__18));
lean_inc_ref_n(v___x_566_, 6);
lean_inc_ref_n(v___x_565_, 6);
lean_inc_ref_n(v___x_564_, 6);
v___x_622_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_621_);
v___x_623_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__19));
v___x_624_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_623_);
v___x_625_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__20));
v___x_626_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_626_, 0, v_a_615_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v___x_627_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__21));
v___x_628_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_628_, 0, v_a_615_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
v___x_629_ = l_Lean_Syntax_node1(v_a_615_, v___x_598_, v___x_628_);
v___x_630_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__22));
v___x_631_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_630_);
v___x_632_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_633_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_633_, 0, v_a_615_);
lean_ctor_set(v___x_633_, 1, v___x_598_);
lean_ctor_set(v___x_633_, 2, v___x_632_);
lean_inc_ref_n(v___x_633_, 3);
v___x_634_ = l_Lean_Syntax_node1(v_a_615_, v___x_631_, v___x_633_);
v___x_635_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__24));
v___x_636_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_635_);
v___x_637_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25));
v___x_638_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_637_);
v___x_639_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__26));
v___x_640_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_639_);
lean_inc(v___x_620_);
lean_inc(v___x_640_);
v___x_641_ = l_Lean_Syntax_node1(v_a_615_, v___x_640_, v___x_620_);
v___x_642_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__27));
v___x_643_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_643_, 0, v_a_615_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
v___x_644_ = l_Lean_Syntax_node5(v_a_615_, v___x_638_, v___x_641_, v___x_633_, v___x_633_, v___x_643_, v___x_617_);
lean_inc_ref(v___y_573_);
lean_inc(v_ref_581_);
v___x_645_ = lean_apply_3(v___f_567_, v_ref_581_, v___y_573_, v_a_616_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_776_; 
v_a_646_ = lean_ctor_get(v___x_645_, 0);
v_a_647_ = lean_ctor_get(v___x_645_, 1);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_776_ == 0)
{
v___x_649_ = v___x_645_;
v_isShared_650_ = v_isSharedCheck_776_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_inc(v_a_646_);
lean_dec(v___x_645_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_776_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_774_; 
lean_inc_n(v_a_615_, 2);
v___x_651_ = l_Lean_Syntax_node1(v_a_615_, v___x_636_, v___x_644_);
v___x_652_ = l_Lean_Syntax_node4(v_a_615_, v___x_624_, v___x_626_, v___x_629_, v___x_634_, v___x_651_);
lean_inc_n(v___x_622_, 4);
v___x_653_ = l_Lean_Syntax_node2(v_a_615_, v___x_622_, v___x_652_, v___x_633_);
v___x_654_ = lean_array_push(v_fst_568_, v___x_653_);
v___x_655_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28));
lean_inc_ref_n(v___x_566_, 11);
lean_inc_ref_n(v___x_565_, 11);
lean_inc_ref_n(v___x_564_, 13);
v___x_656_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_655_);
v___x_657_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29));
v___x_658_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_657_);
v___x_659_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_n(v_a_646_, 54);
v___x_660_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_660_, 0, v_a_646_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
v___x_661_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_661_, 0, v_a_646_);
lean_ctor_set(v___x_661_, 1, v___x_598_);
lean_ctor_set(v___x_661_, 2, v___x_632_);
v___x_662_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31));
v___x_663_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_662_);
v___x_664_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_664_, 0, v_a_646_);
lean_ctor_set(v___x_664_, 1, v___x_589_);
v___x_665_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33);
v___x_666_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36));
lean_inc_n(v_currMacroScope_580_, 5);
lean_inc_n(v_quotContext_579_, 5);
v___x_667_ = l_Lean_addMacroScope(v_quotContext_579_, v___x_666_, v_currMacroScope_580_);
v___x_668_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38));
v___x_669_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_669_, 0, v_a_646_);
lean_ctor_set(v___x_669_, 1, v___x_665_);
lean_ctor_set(v___x_669_, 2, v___x_667_);
lean_ctor_set(v___x_669_, 3, v___x_668_);
v___x_670_ = l_Lean_Syntax_node2(v_a_646_, v___x_588_, v___x_664_, v___x_669_);
v___x_671_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_671_, 0, v_a_646_);
lean_ctor_set(v___x_671_, 1, v___x_601_);
v___x_672_ = l_Lean_Syntax_node1(v_a_646_, v___x_600_, v___x_671_);
lean_inc(v___x_620_);
lean_inc_n(v___x_672_, 2);
v___x_673_ = l_Lean_Syntax_node4(v_a_646_, v___x_598_, v___x_672_, v___x_672_, v___x_672_, v___x_620_);
lean_inc(v___x_586_);
v___x_674_ = l_Lean_Syntax_node2(v_a_646_, v___x_586_, v___x_670_, v___x_673_);
lean_inc_ref_n(v___x_661_, 9);
v___x_675_ = l_Lean_Syntax_node2(v_a_646_, v___x_663_, v___x_661_, v___x_674_);
v___x_676_ = l_Lean_Syntax_node1(v_a_646_, v___x_598_, v___x_675_);
v___x_677_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_678_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_678_, 0, v_a_646_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v___x_679_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40));
v___x_680_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_679_);
v___x_681_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41));
v___x_682_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_681_);
v___x_683_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_684_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_684_, 0, v_a_646_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44);
v___x_686_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__45));
v___x_687_ = l_Lean_addMacroScope(v_quotContext_579_, v___x_686_, v_currMacroScope_580_);
v___x_688_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49));
v___x_689_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_689_, 0, v_a_646_);
lean_ctor_set(v___x_689_, 1, v___x_685_);
lean_ctor_set(v___x_689_, 2, v___x_687_);
lean_ctor_set(v___x_689_, 3, v___x_688_);
v___x_690_ = l_Lean_Syntax_node1(v_a_646_, v___x_598_, v___x_689_);
v___x_691_ = l_Lean_Syntax_node1(v_a_646_, v___x_598_, v___x_690_);
v___x_692_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_693_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_693_, 0, v_a_646_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v___x_694_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__51));
v___x_695_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_694_);
v___x_696_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__52));
v___x_697_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_697_, 0, v_a_646_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
v___x_698_ = l_Lean_Syntax_node1(v_a_646_, v___x_695_, v___x_697_);
v___x_699_ = l_Lean_Syntax_node2(v_a_646_, v___x_622_, v___x_698_, v___x_661_);
v___x_700_ = l_Lean_Syntax_node1(v_a_646_, v___x_598_, v___x_699_);
lean_inc_n(v___x_656_, 2);
v___x_701_ = l_Lean_Syntax_node1(v_a_646_, v___x_656_, v___x_700_);
lean_inc_ref(v___x_693_);
lean_inc_ref(v___x_684_);
lean_inc(v___x_682_);
v___x_702_ = l_Lean_Syntax_node4(v_a_646_, v___x_682_, v___x_684_, v___x_691_, v___x_693_, v___x_701_);
v___x_703_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54);
v___x_704_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__55));
v___x_705_ = l_Lean_addMacroScope(v_quotContext_579_, v___x_704_, v_currMacroScope_580_);
v___x_706_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__58));
v___x_707_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_707_, 0, v_a_646_);
lean_ctor_set(v___x_707_, 1, v___x_703_);
lean_ctor_set(v___x_707_, 2, v___x_705_);
lean_ctor_set(v___x_707_, 3, v___x_706_);
v___x_708_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__59));
v___x_709_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_708_);
v___x_710_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__60));
v___x_711_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_710_);
v___x_712_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__61));
v___x_713_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_713_, 0, v_a_646_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
v___x_714_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__63));
v___x_715_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65);
v___x_716_ = lean_box(0);
v___x_717_ = l_Lean_addMacroScope(v_quotContext_579_, v___x_716_, v_currMacroScope_580_);
v___x_718_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66));
v___x_719_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67));
v___x_720_ = l_Lean_Name_mkStr3(v___x_564_, v___x_718_, v___x_719_);
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
v___x_722_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__68));
v___x_723_ = l_Lean_Name_mkStr2(v___x_564_, v___x_722_);
v___x_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
v___x_725_ = l_Lean_Name_mkStr3(v___x_564_, v___x_565_, v___x_566_);
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
v___x_727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
lean_ctor_set(v___x_727_, 1, v___x_594_);
v___x_728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_724_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
v___x_729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_721_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_730_, 0, v_a_646_);
lean_ctor_set(v___x_730_, 1, v___x_715_);
lean_ctor_set(v___x_730_, 2, v___x_717_);
lean_ctor_set(v___x_730_, 3, v___x_729_);
v___x_731_ = l_Lean_Syntax_node1(v_a_646_, v___x_714_, v___x_730_);
v___x_732_ = l_Lean_Syntax_node2(v_a_646_, v___x_711_, v___x_713_, v___x_731_);
v___x_733_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_733_, 0, v_a_646_);
lean_ctor_set(v___x_733_, 1, v___x_569_);
v___x_734_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70);
v___x_735_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__71));
v___x_736_ = l_Lean_addMacroScope(v_quotContext_579_, v___x_735_, v_currMacroScope_580_);
v___x_737_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_737_, 0, v_a_646_);
lean_ctor_set(v___x_737_, 1, v___x_734_);
lean_ctor_set(v___x_737_, 2, v___x_736_);
lean_ctor_set(v___x_737_, 3, v___x_594_);
lean_inc_ref(v___x_737_);
v___x_738_ = l_Lean_Syntax_node1(v_a_646_, v___x_598_, v___x_737_);
v___x_739_ = l_Lean_Syntax_node3(v_a_646_, v___x_598_, v___x_575_, v___x_733_, v___x_738_);
v___x_740_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__72));
v___x_741_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_741_, 0, v_a_646_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = l_Lean_Syntax_node3(v_a_646_, v___x_709_, v___x_732_, v___x_739_, v___x_741_);
v___x_743_ = l_Lean_Syntax_node1(v_a_646_, v___x_598_, v___x_742_);
v___x_744_ = l_Lean_Syntax_node2(v_a_646_, v___x_586_, v___x_707_, v___x_743_);
v___x_745_ = l_Lean_Syntax_node1(v_a_646_, v___x_598_, v___x_744_);
v___x_746_ = l_Lean_Syntax_node1(v_a_646_, v___x_598_, v___x_745_);
v___x_747_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__73));
v___x_748_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_747_);
v___x_749_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__74));
v___x_750_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_749_);
v___x_751_ = l_Lean_Syntax_node1(v_a_646_, v___x_640_, v___x_620_);
v___x_752_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_752_, 0, v_a_646_);
lean_ctor_set(v___x_752_, 1, v___x_642_);
v___x_753_ = l_Lean_Syntax_node5(v_a_646_, v___x_750_, v___x_751_, v___x_661_, v___x_661_, v___x_752_, v___x_737_);
v___x_754_ = l_Lean_Syntax_node1(v_a_646_, v___x_748_, v___x_753_);
v___x_755_ = l_Lean_Syntax_node2(v_a_646_, v___x_622_, v___x_754_, v___x_661_);
v___x_756_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75));
v___x_757_ = l_Lean_Name_mkStr4(v___x_564_, v___x_565_, v___x_566_, v___x_756_);
v___x_758_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_759_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_759_, 0, v_a_646_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v___x_760_ = l_Lean_Syntax_node2(v_a_646_, v___x_757_, v___x_759_, v_snd_570_);
v___x_761_ = l_Lean_Syntax_node2(v_a_646_, v___x_622_, v___x_760_, v___x_661_);
v___x_762_ = l_Lean_Syntax_node2(v_a_646_, v___x_598_, v___x_755_, v___x_761_);
v___x_763_ = l_Lean_Syntax_node1(v_a_646_, v___x_656_, v___x_762_);
v___x_764_ = l_Lean_Syntax_node4(v_a_646_, v___x_682_, v___x_684_, v___x_746_, v___x_693_, v___x_763_);
v___x_765_ = l_Lean_Syntax_node2(v_a_646_, v___x_598_, v___x_702_, v___x_764_);
v___x_766_ = l_Lean_Syntax_node1(v_a_646_, v___x_680_, v___x_765_);
v___x_767_ = l_Lean_Syntax_node7(v_a_646_, v___x_658_, v___x_660_, v___x_661_, v___x_661_, v___x_661_, v___x_676_, v___x_678_, v___x_766_);
v___x_768_ = l_Lean_Syntax_node2(v_a_646_, v___x_622_, v___x_767_, v___x_661_);
v___x_769_ = l_Lean_Syntax_node1(v_a_646_, v___x_598_, v___x_768_);
v___x_770_ = l_Lean_Syntax_node1(v_a_646_, v___x_656_, v___x_769_);
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_654_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___x_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v___x_772_);
v___x_774_ = v___x_649_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_a_647_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
else
{
lean_object* v_a_777_; lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_dec(v___x_644_);
lean_dec(v___x_640_);
lean_dec(v___x_636_);
lean_dec(v___x_634_);
lean_dec_ref_known(v___x_633_, 3);
lean_dec(v___x_629_);
lean_dec_ref_known(v___x_626_, 2);
lean_dec(v___x_624_);
lean_dec(v___x_622_);
lean_dec(v___x_620_);
lean_dec(v_a_615_);
lean_dec(v___x_600_);
lean_dec(v___x_588_);
lean_dec(v___x_586_);
lean_dec(v___x_575_);
lean_dec(v_snd_570_);
lean_dec_ref(v___x_569_);
lean_dec(v_fst_568_);
lean_dec_ref(v___x_566_);
lean_dec_ref(v___x_565_);
lean_dec_ref(v___x_564_);
v_a_777_ = lean_ctor_get(v___x_645_, 0);
v_a_778_ = lean_ctor_get(v___x_645_, 1);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_645_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_inc(v_a_777_);
lean_dec(v___x_645_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_777_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
else
{
lean_object* v_a_786_; lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec(v_macroScope_605_);
lean_dec(v___x_604_);
lean_dec(v___x_600_);
lean_dec(v___x_597_);
lean_dec(v___x_588_);
lean_dec(v___x_586_);
lean_dec(v___x_584_);
lean_dec(v___x_576_);
lean_dec(v___x_575_);
lean_dec(v_snd_570_);
lean_dec_ref(v___x_569_);
lean_dec(v_fst_568_);
lean_dec_ref(v___f_567_);
lean_dec_ref(v___x_566_);
lean_dec_ref(v___x_565_);
lean_dec_ref(v___x_564_);
v_a_786_ = lean_ctor_get(v___x_614_, 0);
v_a_787_ = lean_ctor_get(v___x_614_, 1);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_614_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_inc(v_a_786_);
lean_dec(v___x_614_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_786_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___lam__1___boxed(lean_object* v___x_810_, lean_object* v___x_811_, lean_object* v___x_812_, lean_object* v___x_813_, lean_object* v___x_814_, lean_object* v___x_815_, lean_object* v___f_816_, lean_object* v_fst_817_, lean_object* v___x_818_, lean_object* v_snd_819_, lean_object* v_x_820_, lean_object* v_h_x3f_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___lam__1(v___x_810_, v___x_811_, v___x_812_, v___x_813_, v___x_814_, v___x_815_, v___f_816_, v_fst_817_, v___x_818_, v_snd_819_, v_x_820_, v_h_x3f_821_, v___y_822_, v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec(v_h_x3f_821_);
lean_dec(v___x_812_);
lean_dec(v___x_811_);
lean_dec(v___x_810_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___lam__0(lean_object* v_____do__lift_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
uint8_t v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_828_ = 0;
v___x_829_ = l_Lean_SourceInfo_fromRef(v_____do__lift_825_, v___x_828_);
v___x_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
lean_ctor_set(v___x_830_, 1, v___y_827_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___lam__0___boxed(lean_object* v_____do__lift_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___lam__0(v_____do__lift_831_, v___y_832_, v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v_____do__lift_831_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg(lean_object* v_a_836_, lean_object* v_b_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_array_840_; lean_object* v_start_841_; lean_object* v_stop_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_935_; 
v_array_840_ = lean_ctor_get(v_a_836_, 0);
v_start_841_ = lean_ctor_get(v_a_836_, 1);
v_stop_842_ = lean_ctor_get(v_a_836_, 2);
v_isSharedCheck_935_ = !lean_is_exclusive(v_a_836_);
if (v_isSharedCheck_935_ == 0)
{
v___x_844_ = v_a_836_;
v_isShared_845_ = v_isSharedCheck_935_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_stop_842_);
lean_inc(v_start_841_);
lean_inc(v_array_840_);
lean_dec(v_a_836_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_935_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
uint8_t v___x_846_; 
v___x_846_ = lean_nat_dec_lt(v_start_841_, v_stop_842_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; 
lean_del_object(v___x_844_);
lean_dec(v_stop_842_);
lean_dec(v_start_841_);
lean_dec_ref(v_array_840_);
v___x_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_847_, 0, v_b_837_);
lean_ctor_set(v___x_847_, 1, v___y_839_);
return v___x_847_;
}
else
{
lean_object* v_fst_848_; lean_object* v_snd_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_934_; 
v_fst_848_ = lean_ctor_get(v_b_837_, 0);
v_snd_849_ = lean_ctor_get(v_b_837_, 1);
v_isSharedCheck_934_ = !lean_is_exclusive(v_b_837_);
if (v_isSharedCheck_934_ == 0)
{
v___x_851_ = v_b_837_;
v_isShared_852_ = v_isSharedCheck_934_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_snd_849_);
lean_inc(v_fst_848_);
lean_dec(v_b_837_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_934_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_853_ = lean_unsigned_to_nat(1u);
v___x_854_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0));
v___x_855_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1));
v___x_856_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2));
v___x_857_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
v___x_858_ = lean_nat_add(v_start_841_, v___x_853_);
lean_inc_ref(v_array_840_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 1, v___x_858_);
v___x_860_ = v___x_844_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_array_840_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_933_, 2, v_stop_842_);
v___x_860_ = v_reuseFailAlloc_933_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___y_862_; lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_886_ = lean_array_fget(v_array_840_, v_start_841_);
lean_dec(v_start_841_);
lean_dec_ref(v_array_840_);
lean_inc(v___x_886_);
v___x_887_ = l_Lean_Syntax_isOfKind(v___x_886_, v___x_857_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; 
lean_dec(v___x_886_);
v___x_888_ = l_Lean_Macro_throwUnsupported___redArg(v___y_839_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_891_; 
v_a_889_ = lean_ctor_get(v___x_888_, 1);
lean_inc(v_a_889_);
lean_dec_ref_known(v___x_888_, 2);
if (v_isShared_852_ == 0)
{
v___x_891_ = v___x_851_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_fst_848_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v_snd_849_);
v___x_891_ = v_reuseFailAlloc_893_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
v_a_836_ = v___x_860_;
v_b_837_ = v___x_891_;
v___y_839_ = v_a_889_;
goto _start;
}
}
else
{
lean_object* v_a_894_; lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_dec_ref(v___x_860_);
lean_del_object(v___x_851_);
lean_dec(v_snd_849_);
lean_dec(v_fst_848_);
v_a_894_ = lean_ctor_get(v___x_888_, 0);
v_a_895_ = lean_ctor_get(v___x_888_, 1);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_888_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_inc(v_a_894_);
lean_dec(v___x_888_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_894_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
else
{
lean_object* v___f_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; uint8_t v___x_908_; 
v___f_903_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___closed__0));
v___x_904_ = lean_unsigned_to_nat(3u);
v___x_905_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__5));
v___x_906_ = lean_unsigned_to_nat(0u);
v___x_907_ = l_Lean_Syntax_getArg(v___x_886_, v___x_906_);
v___x_908_ = l_Lean_Syntax_isNone(v___x_907_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; uint8_t v___x_910_; 
v___x_909_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_907_);
v___x_910_ = l_Lean_Syntax_matchesNull(v___x_907_, v___x_909_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; 
lean_dec(v___x_907_);
lean_dec(v___x_886_);
v___x_911_ = l_Lean_Macro_throwUnsupported___redArg(v___y_839_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_914_; 
v_a_912_ = lean_ctor_get(v___x_911_, 1);
lean_inc(v_a_912_);
lean_dec_ref_known(v___x_911_, 2);
if (v_isShared_852_ == 0)
{
v___x_914_ = v___x_851_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_fst_848_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v_snd_849_);
v___x_914_ = v_reuseFailAlloc_916_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
v_a_836_ = v___x_860_;
v_b_837_ = v___x_914_;
v___y_839_ = v_a_912_;
goto _start;
}
}
else
{
lean_object* v_a_917_; lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
lean_dec_ref(v___x_860_);
lean_del_object(v___x_851_);
lean_dec(v_snd_849_);
lean_dec(v_fst_848_);
v_a_917_ = lean_ctor_get(v___x_911_, 0);
v_a_918_ = lean_ctor_get(v___x_911_, 1);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_911_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_inc(v_a_917_);
lean_dec(v___x_911_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_917_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v_a_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
else
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
lean_del_object(v___x_851_);
v___x_926_ = l_Lean_Syntax_getArg(v___x_907_, v___x_906_);
lean_dec(v___x_907_);
v___x_927_ = lean_box(0);
v___x_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_928_, 0, v___x_926_);
v___x_929_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___lam__1(v___x_886_, v___x_853_, v___x_904_, v___x_854_, v___x_855_, v___x_856_, v___f_903_, v_fst_848_, v___x_905_, v_snd_849_, v___x_927_, v___x_928_, v___y_838_, v___y_839_);
lean_dec_ref_known(v___x_928_, 1);
lean_dec(v___x_886_);
v___y_862_ = v___x_929_;
goto v___jp_861_;
}
}
else
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
lean_dec(v___x_907_);
lean_del_object(v___x_851_);
v___x_930_ = lean_box(0);
v___x_931_ = lean_box(0);
v___x_932_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___lam__1(v___x_886_, v___x_853_, v___x_904_, v___x_854_, v___x_855_, v___x_856_, v___f_903_, v_fst_848_, v___x_905_, v_snd_849_, v___x_930_, v___x_931_, v___y_838_, v___y_839_);
lean_dec(v___x_886_);
v___y_862_ = v___x_932_;
goto v___jp_861_;
}
}
v___jp_861_:
{
if (lean_obj_tag(v___y_862_) == 0)
{
lean_object* v_a_863_; 
v_a_863_ = lean_ctor_get(v___y_862_, 0);
lean_inc(v_a_863_);
if (lean_obj_tag(v_a_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_872_; 
lean_dec_ref(v___x_860_);
v_a_864_ = lean_ctor_get(v___y_862_, 1);
v_isSharedCheck_872_ = !lean_is_exclusive(v___y_862_);
if (v_isSharedCheck_872_ == 0)
{
lean_object* v_unused_873_; 
v_unused_873_ = lean_ctor_get(v___y_862_, 0);
lean_dec(v_unused_873_);
v___x_866_ = v___y_862_;
v_isShared_867_ = v_isSharedCheck_872_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___y_862_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_872_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v_a_868_; lean_object* v___x_870_; 
v_a_868_ = lean_ctor_get(v_a_863_, 0);
lean_inc(v_a_868_);
lean_dec_ref_known(v_a_863_, 1);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v_a_868_);
v___x_870_ = v___x_866_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_868_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v_a_864_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
else
{
lean_object* v_a_874_; lean_object* v_a_875_; 
v_a_874_ = lean_ctor_get(v___y_862_, 1);
lean_inc(v_a_874_);
lean_dec_ref_known(v___y_862_, 2);
v_a_875_ = lean_ctor_get(v_a_863_, 0);
lean_inc(v_a_875_);
lean_dec_ref_known(v_a_863_, 1);
v_a_836_ = v___x_860_;
v_b_837_ = v_a_875_;
v___y_839_ = v_a_874_;
goto _start;
}
}
else
{
lean_object* v_a_877_; lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
lean_dec_ref(v___x_860_);
v_a_877_ = lean_ctor_get(v___y_862_, 0);
v_a_878_ = lean_ctor_get(v___y_862_, 1);
v_isSharedCheck_885_ = !lean_is_exclusive(v___y_862_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___y_862_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_inc(v_a_877_);
lean_dec(v___y_862_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_877_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg___boxed(lean_object* v_a_936_, lean_object* v_b_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg(v_a_936_, v_b_937_, v___y_938_, v___y_939_);
lean_dec_ref(v___y_938_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor(lean_object* v_stx_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_){
_start:
{
lean_object* v___x_1013_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; uint8_t v___x_1149_; 
v___x_1013_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
lean_inc(v_stx_1010_);
v___x_1149_ = l_Lean_Syntax_isOfKind(v_stx_1010_, v___x_1013_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; 
lean_dec(v_stx_1010_);
v___x_1150_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1012_);
return v___x_1150_;
}
else
{
lean_object* v___x_1151_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v___y_1177_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v_tk_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; uint8_t v___x_1264_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v_x_1273_; lean_object* v_body_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v_h_x3f_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; 
v___x_1151_ = lean_unsigned_to_nat(0u);
v_tk_1261_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_1151_);
v___x_1262_ = lean_unsigned_to_nat(1u);
v___x_1263_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_1262_);
lean_inc(v___x_1263_);
v___x_1264_ = l_Lean_Syntax_matchesNull(v___x_1263_, v___x_1262_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1384_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v_dec_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v_inv_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___x_1446_; uint8_t v___x_1447_; 
v___x_1384_ = lean_unsigned_to_nat(2u);
v___x_1446_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_1384_);
v___x_1447_ = l_Lean_Syntax_isNone(v___x_1446_);
if (v___x_1447_ == 0)
{
uint8_t v___x_1448_; 
lean_inc(v___x_1446_);
v___x_1448_ = l_Lean_Syntax_matchesNull(v___x_1446_, v___x_1262_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; 
lean_dec(v___x_1446_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_1449_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1012_);
return v___x_1449_;
}
else
{
lean_object* v_inv_1450_; lean_object* v___x_1451_; uint8_t v___x_1452_; 
v_inv_1450_ = l_Lean_Syntax_getArg(v___x_1446_, v___x_1151_);
lean_dec(v___x_1446_);
v___x_1451_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__19));
lean_inc(v_inv_1450_);
v___x_1452_ = l_Lean_Syntax_isOfKind(v_inv_1450_, v___x_1451_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1453_; 
lean_dec(v_inv_1450_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_1453_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1012_);
return v___x_1453_;
}
else
{
lean_object* v___x_1454_; 
v___x_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1454_, 0, v_inv_1450_);
v_inv_1432_ = v___x_1454_;
v___y_1433_ = v_a_1011_;
v___y_1434_ = v_a_1012_;
goto v___jp_1431_;
}
}
}
else
{
lean_object* v___x_1455_; 
lean_dec(v___x_1446_);
v___x_1455_ = lean_box(0);
v_inv_1432_ = v___x_1455_;
v___y_1433_ = v_a_1011_;
v___y_1434_ = v_a_1012_;
goto v___jp_1431_;
}
v___jp_1385_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; 
v___x_1394_ = lean_box(0);
v___x_1395_ = lean_array_get(v___x_1394_, v___y_1389_, v___x_1151_);
lean_inc(v___x_1395_);
v___x_1396_ = l_Lean_Syntax_isOfKind(v___x_1395_, v___y_1388_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; 
lean_dec(v___x_1395_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec(v_tk_1261_);
v___x_1397_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1393_);
return v___x_1397_;
}
else
{
lean_object* v___x_1398_; uint8_t v___x_1399_; 
v___x_1398_ = l_Lean_Syntax_getArg(v___x_1395_, v___x_1151_);
v___x_1399_ = l_Lean_Syntax_isNone(v___x_1398_);
if (v___x_1399_ == 0)
{
uint8_t v___x_1400_; 
lean_inc(v___x_1398_);
v___x_1400_ = l_Lean_Syntax_matchesNull(v___x_1398_, v___x_1384_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; 
lean_dec(v___x_1398_);
lean_dec(v___x_1395_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec(v_tk_1261_);
v___x_1401_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1393_);
return v___x_1401_;
}
else
{
lean_object* v_h_x3f_1402_; lean_object* v___x_1403_; 
v_h_x3f_1402_ = l_Lean_Syntax_getArg(v___x_1398_, v___x_1151_);
lean_dec(v___x_1398_);
v___x_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1403_, 0, v_h_x3f_1402_);
v___y_1314_ = v___y_1386_;
v___y_1315_ = v___y_1387_;
v___y_1316_ = v___y_1388_;
v___y_1317_ = v___y_1389_;
v___y_1318_ = v___y_1390_;
v___y_1319_ = v___x_1395_;
v___y_1320_ = v___y_1391_;
v_h_x3f_1321_ = v___x_1403_;
v___y_1322_ = v___y_1392_;
v___y_1323_ = v___y_1393_;
goto v___jp_1313_;
}
}
else
{
lean_object* v___x_1404_; 
lean_dec(v___x_1398_);
v___x_1404_ = lean_box(0);
v___y_1314_ = v___y_1386_;
v___y_1315_ = v___y_1387_;
v___y_1316_ = v___y_1388_;
v___y_1317_ = v___y_1389_;
v___y_1318_ = v___y_1390_;
v___y_1319_ = v___x_1395_;
v___y_1320_ = v___y_1391_;
v_h_x3f_1321_ = v___x_1404_;
v___y_1322_ = v___y_1392_;
v___y_1323_ = v___y_1393_;
goto v___jp_1313_;
}
}
}
v___jp_1405_:
{
lean_object* v___x_1411_; lean_object* v_body_1412_; lean_object* v___x_1413_; lean_object* v_decls_1414_; lean_object* v_decls_1415_; 
v___x_1411_ = lean_unsigned_to_nat(5u);
v_body_1412_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_1411_);
lean_dec(v_stx_1010_);
v___x_1413_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
v_decls_1414_ = l_Lean_Syntax_getArgs(v___x_1263_);
lean_dec(v___x_1263_);
v_decls_1415_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_1414_);
lean_dec_ref(v_decls_1414_);
if (lean_obj_tag(v___y_1406_) == 1)
{
lean_object* v_val_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
v_val_1416_ = lean_ctor_get(v___y_1406_, 0);
v___x_1417_ = lean_array_get_size(v_decls_1415_);
v___x_1418_ = lean_nat_dec_lt(v___x_1262_, v___x_1417_);
if (v___x_1418_ == 0)
{
v___y_1386_ = v_body_1412_;
v___y_1387_ = v___y_1406_;
v___y_1388_ = v___x_1413_;
v___y_1389_ = v_decls_1415_;
v___y_1390_ = v_dec_1408_;
v___y_1391_ = v___y_1407_;
v___y_1392_ = v___y_1409_;
v___y_1393_ = v___y_1410_;
goto v___jp_1385_;
}
else
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1419_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__15));
v___x_1420_ = l_Lean_Macro_throwErrorAt___redArg(v_val_1416_, v___x_1419_, v___y_1409_, v___y_1410_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v_a_1421_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 1);
lean_inc(v_a_1421_);
lean_dec_ref_known(v___x_1420_, 2);
v___y_1386_ = v_body_1412_;
v___y_1387_ = v___y_1406_;
v___y_1388_ = v___x_1413_;
v___y_1389_ = v_decls_1415_;
v___y_1390_ = v_dec_1408_;
v___y_1391_ = v___y_1407_;
v___y_1392_ = v___y_1409_;
v___y_1393_ = v_a_1421_;
goto v___jp_1385_;
}
else
{
lean_object* v_a_1422_; lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
lean_dec_ref_known(v___y_1406_, 1);
lean_dec_ref(v_decls_1415_);
lean_dec(v_body_1412_);
lean_dec(v_dec_1408_);
lean_dec(v_tk_1261_);
v_a_1422_ = lean_ctor_get(v___x_1420_, 0);
v_a_1423_ = lean_ctor_get(v___x_1420_, 1);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1425_ = v___x_1420_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_inc(v_a_1422_);
lean_dec(v___x_1420_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1428_; 
if (v_isShared_1426_ == 0)
{
v___x_1428_ = v___x_1425_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_a_1422_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v_a_1423_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
}
else
{
v___y_1386_ = v_body_1412_;
v___y_1387_ = v___y_1406_;
v___y_1388_ = v___x_1413_;
v___y_1389_ = v_decls_1415_;
v___y_1390_ = v_dec_1408_;
v___y_1391_ = v___y_1407_;
v___y_1392_ = v___y_1409_;
v___y_1393_ = v___y_1410_;
goto v___jp_1385_;
}
}
v___jp_1431_:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; uint8_t v___x_1437_; 
v___x_1435_ = lean_unsigned_to_nat(3u);
v___x_1436_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_1435_);
v___x_1437_ = l_Lean_Syntax_isNone(v___x_1436_);
if (v___x_1437_ == 0)
{
uint8_t v___x_1438_; 
lean_inc(v___x_1436_);
v___x_1438_ = l_Lean_Syntax_matchesNull(v___x_1436_, v___x_1262_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1439_; 
lean_dec(v___x_1436_);
lean_dec(v_inv_1432_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_1439_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1434_);
return v___x_1439_;
}
else
{
lean_object* v_dec_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; 
v_dec_1440_ = l_Lean_Syntax_getArg(v___x_1436_, v___x_1151_);
lean_dec(v___x_1436_);
v___x_1441_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v_dec_1440_);
v___x_1442_ = l_Lean_Syntax_isOfKind(v_dec_1440_, v___x_1441_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; 
lean_dec(v_dec_1440_);
lean_dec(v_inv_1432_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_1443_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1434_);
return v___x_1443_;
}
else
{
lean_object* v___x_1444_; 
v___x_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1444_, 0, v_dec_1440_);
v___y_1406_ = v_inv_1432_;
v___y_1407_ = v___x_1435_;
v_dec_1408_ = v___x_1444_;
v___y_1409_ = v___y_1433_;
v___y_1410_ = v___y_1434_;
goto v___jp_1405_;
}
}
}
else
{
lean_object* v___x_1445_; 
lean_dec(v___x_1436_);
v___x_1445_ = lean_box(0);
v___y_1406_ = v_inv_1432_;
v___y_1407_ = v___x_1435_;
v_dec_1408_ = v___x_1445_;
v___y_1409_ = v___y_1433_;
v___y_1410_ = v___y_1434_;
goto v___jp_1405_;
}
}
}
else
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1482_; lean_object* v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___y_1493_; lean_object* v___y_1494_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v_x_1511_; lean_object* v_body_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v_h_x3f_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___y_1628_; lean_object* v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v_inv_1645_; lean_object* v_dec_1646_; lean_object* v_body_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1668_; uint8_t v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; uint8_t v___y_1673_; lean_object* v_inv_1674_; lean_object* v___y_1675_; lean_object* v___y_1676_; uint8_t v___y_1685_; uint8_t v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; uint8_t v___y_1691_; lean_object* v_inv_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1700_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1704_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v_dec_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; uint8_t v___y_1774_; lean_object* v_x_1775_; lean_object* v_body_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1816_; lean_object* v___y_1817_; lean_object* v___y_1818_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; uint8_t v___y_1822_; lean_object* v_h_x3f_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; uint8_t v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; uint8_t v___y_1911_; lean_object* v_dec_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1935_; lean_object* v___y_1936_; uint8_t v___y_1937_; lean_object* v_inv_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; uint8_t v___x_2013_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v_x_2021_; lean_object* v_body_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2062_; lean_object* v___y_2063_; lean_object* v___y_2064_; lean_object* v___y_2065_; lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v_h_x3f_2068_; lean_object* v___y_2069_; lean_object* v___y_2070_; 
v___x_1456_ = l_Lean_Syntax_getArg(v___x_1263_, v___x_1151_);
v___x_1457_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
lean_inc(v___x_1456_);
v___x_2013_ = l_Lean_Syntax_isOfKind(v___x_1456_, v___x_1457_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2131_; lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v_dec_2154_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v_inv_2177_; lean_object* v___y_2178_; lean_object* v___y_2179_; lean_object* v___x_2191_; uint8_t v___x_2192_; 
lean_dec(v___x_1456_);
v___x_2131_ = lean_unsigned_to_nat(2u);
v___x_2191_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_2131_);
v___x_2192_ = l_Lean_Syntax_isNone(v___x_2191_);
if (v___x_2192_ == 0)
{
uint8_t v___x_2193_; 
lean_inc(v___x_2191_);
v___x_2193_ = l_Lean_Syntax_matchesNull(v___x_2191_, v___x_1262_);
if (v___x_2193_ == 0)
{
lean_object* v___x_2194_; 
lean_dec(v___x_2191_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_2194_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1012_);
return v___x_2194_;
}
else
{
lean_object* v_inv_2195_; lean_object* v___x_2196_; uint8_t v___x_2197_; 
v_inv_2195_ = l_Lean_Syntax_getArg(v___x_2191_, v___x_1151_);
lean_dec(v___x_2191_);
v___x_2196_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__19));
lean_inc(v_inv_2195_);
v___x_2197_ = l_Lean_Syntax_isOfKind(v_inv_2195_, v___x_2196_);
if (v___x_2197_ == 0)
{
lean_object* v___x_2198_; 
lean_dec(v_inv_2195_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_2198_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1012_);
return v___x_2198_;
}
else
{
lean_object* v___x_2199_; 
v___x_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2199_, 0, v_inv_2195_);
v_inv_2177_ = v___x_2199_;
v___y_2178_ = v_a_1011_;
v___y_2179_ = v_a_1012_;
goto v___jp_2176_;
}
}
}
else
{
lean_object* v___x_2200_; 
lean_dec(v___x_2191_);
v___x_2200_ = lean_box(0);
v_inv_2177_ = v___x_2200_;
v___y_2178_ = v_a_1011_;
v___y_2179_ = v_a_1012_;
goto v___jp_2176_;
}
v___jp_2132_:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; 
v___x_2140_ = lean_box(0);
v___x_2141_ = lean_array_get(v___x_2140_, v___y_2136_, v___x_1151_);
lean_inc(v___x_2141_);
v___x_2142_ = l_Lean_Syntax_isOfKind(v___x_2141_, v___x_1457_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; 
lean_dec(v___x_2141_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
lean_dec(v___y_2135_);
lean_dec(v___y_2133_);
lean_dec(v_tk_1261_);
v___x_2143_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2139_);
return v___x_2143_;
}
else
{
lean_object* v___x_2144_; uint8_t v___x_2145_; 
v___x_2144_ = l_Lean_Syntax_getArg(v___x_2141_, v___x_1151_);
v___x_2145_ = l_Lean_Syntax_isNone(v___x_2144_);
if (v___x_2145_ == 0)
{
uint8_t v___x_2146_; 
lean_inc(v___x_2144_);
v___x_2146_ = l_Lean_Syntax_matchesNull(v___x_2144_, v___x_2131_);
if (v___x_2146_ == 0)
{
lean_object* v___x_2147_; 
lean_dec(v___x_2144_);
lean_dec(v___x_2141_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
lean_dec(v___y_2135_);
lean_dec(v___y_2133_);
lean_dec(v_tk_1261_);
v___x_2147_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2139_);
return v___x_2147_;
}
else
{
lean_object* v_h_x3f_2148_; lean_object* v___x_2149_; 
v_h_x3f_2148_ = l_Lean_Syntax_getArg(v___x_2144_, v___x_1151_);
lean_dec(v___x_2144_);
v___x_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2149_, 0, v_h_x3f_2148_);
v___y_2062_ = v___y_2133_;
v___y_2063_ = v___y_2135_;
v___y_2064_ = v___y_2136_;
v___y_2065_ = v___y_2134_;
v___y_2066_ = v___x_2141_;
v___y_2067_ = v___y_2137_;
v_h_x3f_2068_ = v___x_2149_;
v___y_2069_ = v___y_2138_;
v___y_2070_ = v___y_2139_;
goto v___jp_2061_;
}
}
else
{
lean_object* v___x_2150_; 
lean_dec(v___x_2144_);
v___x_2150_ = lean_box(0);
v___y_2062_ = v___y_2133_;
v___y_2063_ = v___y_2135_;
v___y_2064_ = v___y_2136_;
v___y_2065_ = v___y_2134_;
v___y_2066_ = v___x_2141_;
v___y_2067_ = v___y_2137_;
v_h_x3f_2068_ = v___x_2150_;
v___y_2069_ = v___y_2138_;
v___y_2070_ = v___y_2139_;
goto v___jp_2061_;
}
}
}
v___jp_2151_:
{
lean_object* v___x_2157_; lean_object* v_body_2158_; lean_object* v_decls_2159_; lean_object* v_decls_2160_; 
v___x_2157_ = lean_unsigned_to_nat(5u);
v_body_2158_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_2157_);
lean_dec(v_stx_1010_);
v_decls_2159_ = l_Lean_Syntax_getArgs(v___x_1263_);
lean_dec(v___x_1263_);
v_decls_2160_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_2159_);
lean_dec_ref(v_decls_2159_);
if (lean_obj_tag(v___y_2153_) == 1)
{
lean_object* v_val_2161_; lean_object* v___x_2162_; uint8_t v___x_2163_; 
v_val_2161_ = lean_ctor_get(v___y_2153_, 0);
v___x_2162_ = lean_array_get_size(v_decls_2160_);
v___x_2163_ = lean_nat_dec_lt(v___x_1262_, v___x_2162_);
if (v___x_2163_ == 0)
{
v___y_2133_ = v_dec_2154_;
v___y_2134_ = v___y_2152_;
v___y_2135_ = v_body_2158_;
v___y_2136_ = v_decls_2160_;
v___y_2137_ = v___y_2153_;
v___y_2138_ = v___y_2155_;
v___y_2139_ = v___y_2156_;
goto v___jp_2132_;
}
else
{
lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2164_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__15));
v___x_2165_ = l_Lean_Macro_throwErrorAt___redArg(v_val_2161_, v___x_2164_, v___y_2155_, v___y_2156_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v_a_2166_; 
v_a_2166_ = lean_ctor_get(v___x_2165_, 1);
lean_inc(v_a_2166_);
lean_dec_ref_known(v___x_2165_, 2);
v___y_2133_ = v_dec_2154_;
v___y_2134_ = v___y_2152_;
v___y_2135_ = v_body_2158_;
v___y_2136_ = v_decls_2160_;
v___y_2137_ = v___y_2153_;
v___y_2138_ = v___y_2155_;
v___y_2139_ = v_a_2166_;
goto v___jp_2132_;
}
else
{
lean_object* v_a_2167_; lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
lean_dec_ref_known(v___y_2153_, 1);
lean_dec_ref(v_decls_2160_);
lean_dec(v_body_2158_);
lean_dec(v_dec_2154_);
lean_dec(v_tk_1261_);
v_a_2167_ = lean_ctor_get(v___x_2165_, 0);
v_a_2168_ = lean_ctor_get(v___x_2165_, 1);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2170_ = v___x_2165_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_inc(v_a_2167_);
lean_dec(v___x_2165_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2167_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v_a_2168_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
}
else
{
v___y_2133_ = v_dec_2154_;
v___y_2134_ = v___y_2152_;
v___y_2135_ = v_body_2158_;
v___y_2136_ = v_decls_2160_;
v___y_2137_ = v___y_2153_;
v___y_2138_ = v___y_2155_;
v___y_2139_ = v___y_2156_;
goto v___jp_2132_;
}
}
v___jp_2176_:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; uint8_t v___x_2182_; 
v___x_2180_ = lean_unsigned_to_nat(3u);
v___x_2181_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_2180_);
v___x_2182_ = l_Lean_Syntax_isNone(v___x_2181_);
if (v___x_2182_ == 0)
{
uint8_t v___x_2183_; 
lean_inc(v___x_2181_);
v___x_2183_ = l_Lean_Syntax_matchesNull(v___x_2181_, v___x_1262_);
if (v___x_2183_ == 0)
{
lean_object* v___x_2184_; 
lean_dec(v___x_2181_);
lean_dec(v_inv_2177_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_2184_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2179_);
return v___x_2184_;
}
else
{
lean_object* v_dec_2185_; lean_object* v___x_2186_; uint8_t v___x_2187_; 
v_dec_2185_ = l_Lean_Syntax_getArg(v___x_2181_, v___x_1151_);
lean_dec(v___x_2181_);
v___x_2186_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v_dec_2185_);
v___x_2187_ = l_Lean_Syntax_isOfKind(v_dec_2185_, v___x_2186_);
if (v___x_2187_ == 0)
{
lean_object* v___x_2188_; 
lean_dec(v_dec_2185_);
lean_dec(v_inv_2177_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_2188_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2179_);
return v___x_2188_;
}
else
{
lean_object* v___x_2189_; 
v___x_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2189_, 0, v_dec_2185_);
v___y_2152_ = v___x_2180_;
v___y_2153_ = v_inv_2177_;
v_dec_2154_ = v___x_2189_;
v___y_2155_ = v___y_2178_;
v___y_2156_ = v___y_2179_;
goto v___jp_2151_;
}
}
}
else
{
lean_object* v___x_2190_; 
lean_dec(v___x_2181_);
v___x_2190_ = lean_box(0);
v___y_2152_ = v___x_2180_;
v___y_2153_ = v_inv_2177_;
v_dec_2154_ = v___x_2190_;
v___y_2155_ = v___y_2178_;
v___y_2156_ = v___y_2179_;
goto v___jp_2151_;
}
}
}
else
{
lean_object* v___x_2201_; uint8_t v___x_2202_; 
v___x_2201_ = l_Lean_Syntax_getArg(v___x_1456_, v___x_1151_);
v___x_2202_ = l_Lean_Syntax_isNone(v___x_2201_);
if (v___x_2202_ == 0)
{
lean_object* v___x_2203_; uint8_t v___x_2204_; lean_object* v___y_2206_; lean_object* v___y_2207_; lean_object* v___y_2208_; lean_object* v___y_2209_; lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v_x_2212_; lean_object* v_body_2213_; lean_object* v___y_2214_; lean_object* v___y_2215_; 
v___x_2203_ = lean_unsigned_to_nat(2u);
v___x_2204_ = l_Lean_Syntax_matchesNull(v___x_2201_, v___x_2203_);
if (v___x_2204_ == 0)
{
lean_object* v___x_2252_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v_h_x3f_2259_; lean_object* v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2325_; lean_object* v___y_2326_; lean_object* v___y_2327_; lean_object* v___y_2328_; lean_object* v___y_2341_; lean_object* v_dec_2342_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v_inv_2365_; lean_object* v___y_2366_; lean_object* v___y_2367_; lean_object* v___x_2378_; uint8_t v___x_2379_; 
lean_dec(v___x_1456_);
v___x_2252_ = lean_unsigned_to_nat(3u);
v___x_2378_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_2203_);
v___x_2379_ = l_Lean_Syntax_isNone(v___x_2378_);
if (v___x_2379_ == 0)
{
uint8_t v___x_2380_; 
lean_inc(v___x_2378_);
v___x_2380_ = l_Lean_Syntax_matchesNull(v___x_2378_, v___x_1262_);
if (v___x_2380_ == 0)
{
lean_object* v___x_2381_; 
lean_dec(v___x_2378_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_2381_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1012_);
return v___x_2381_;
}
else
{
lean_object* v_inv_2382_; lean_object* v___x_2383_; uint8_t v___x_2384_; 
v_inv_2382_ = l_Lean_Syntax_getArg(v___x_2378_, v___x_1151_);
lean_dec(v___x_2378_);
v___x_2383_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__19));
lean_inc(v_inv_2382_);
v___x_2384_ = l_Lean_Syntax_isOfKind(v_inv_2382_, v___x_2383_);
if (v___x_2384_ == 0)
{
lean_object* v___x_2385_; 
lean_dec(v_inv_2382_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_2385_ = l_Lean_Macro_throwUnsupported___redArg(v_a_1012_);
return v___x_2385_;
}
else
{
lean_object* v___x_2386_; 
v___x_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2386_, 0, v_inv_2382_);
v_inv_2365_ = v___x_2386_;
v___y_2366_ = v_a_1011_;
v___y_2367_ = v_a_1012_;
goto v___jp_2364_;
}
}
}
else
{
lean_object* v___x_2387_; 
lean_dec(v___x_2378_);
v___x_2387_ = lean_box(0);
v_inv_2365_ = v___x_2387_;
v___y_2366_ = v_a_1011_;
v___y_2367_ = v_a_1012_;
goto v___jp_2364_;
}
v___jp_2253_:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v_doElems_2264_; uint8_t v___x_2265_; 
v___x_2262_ = l_Lean_Syntax_getArg(v___y_2257_, v___x_1262_);
v___x_2263_ = l_Lean_Syntax_getArg(v___y_2257_, v___x_2252_);
lean_dec(v___y_2257_);
v_doElems_2264_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_2265_ = l_Lean_Syntax_isIdent(v___x_2262_);
if (v___x_2265_ == 0)
{
lean_object* v___x_2266_; uint8_t v___x_2267_; 
v___x_2266_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_2262_);
v___x_2267_ = l_Lean_Syntax_isOfKind(v___x_2262_, v___x_2266_);
if (v___x_2267_ == 0)
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_2262_, v___x_2267_, v___y_2260_, v___y_2261_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v_a_2269_; lean_object* v_a_2270_; lean_object* v_ref_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc_n(v_a_2269_, 2);
v_a_2270_ = lean_ctor_get(v___x_2268_, 1);
lean_inc(v_a_2270_);
lean_dec_ref_known(v___x_2268_, 2);
v_ref_2271_ = lean_ctor_get(v___y_2260_, 5);
v___x_2272_ = l_Lean_SourceInfo_fromRef(v_ref_2271_, v___x_2267_);
v___x_2273_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_2274_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_2275_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
v___x_2276_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_2277_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_n(v___x_2272_, 15);
v___x_2278_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2272_);
lean_ctor_set(v___x_2278_, 1, v___x_2277_);
v___x_2279_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_2280_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2272_);
lean_ctor_set(v___x_2280_, 1, v___x_2274_);
lean_ctor_set(v___x_2280_, 2, v___x_2279_);
v___x_2281_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_2280_, 4);
v___x_2282_ = l_Lean_Syntax_node2(v___x_2272_, v___x_2281_, v___x_2280_, v_a_2269_);
v___x_2283_ = l_Lean_Syntax_node1(v___x_2272_, v___x_2274_, v___x_2282_);
v___x_2284_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_2285_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2272_);
lean_ctor_set(v___x_2285_, 1, v___x_2284_);
v___x_2286_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_2287_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_2288_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_2289_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2272_);
lean_ctor_set(v___x_2289_, 1, v___x_2288_);
v___x_2290_ = l_Lean_Syntax_node1(v___x_2272_, v___x_2274_, v___x_2262_);
v___x_2291_ = l_Lean_Syntax_node1(v___x_2272_, v___x_2274_, v___x_2290_);
v___x_2292_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_2293_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2272_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
v___x_2294_ = l_Lean_Syntax_node4(v___x_2272_, v___x_2287_, v___x_2289_, v___x_2291_, v___x_2293_, v___y_2258_);
v___x_2295_ = l_Lean_Syntax_node1(v___x_2272_, v___x_2274_, v___x_2294_);
v___x_2296_ = l_Lean_Syntax_node1(v___x_2272_, v___x_2286_, v___x_2295_);
v___x_2297_ = l_Lean_Syntax_node7(v___x_2272_, v___x_2276_, v___x_2278_, v___x_2280_, v___x_2280_, v___x_2280_, v___x_2283_, v___x_2285_, v___x_2296_);
v___x_2298_ = l_Lean_Syntax_node2(v___x_2272_, v___x_2275_, v___x_2297_, v___x_2280_);
v___x_2299_ = l_Lean_Syntax_node1(v___x_2272_, v___x_2274_, v___x_2298_);
v___x_2300_ = l_Lean_Syntax_node1(v___x_2272_, v___x_2273_, v___x_2299_);
v___y_2206_ = v_doElems_2264_;
v___y_2207_ = v___y_2254_;
v___y_2208_ = v___y_2256_;
v___y_2209_ = v___y_2255_;
v___y_2210_ = v___x_2263_;
v___y_2211_ = v_h_x3f_2259_;
v_x_2212_ = v_a_2269_;
v_body_2213_ = v___x_2300_;
v___y_2214_ = v___y_2260_;
v___y_2215_ = v_a_2270_;
goto v___jp_2205_;
}
else
{
lean_object* v_a_2301_; lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2309_; 
lean_dec(v___x_2263_);
lean_dec(v___x_2262_);
lean_dec(v_h_x3f_2259_);
lean_dec(v___y_2258_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec(v_tk_1261_);
v_a_2301_ = lean_ctor_get(v___x_2268_, 0);
v_a_2302_ = lean_ctor_get(v___x_2268_, 1);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2304_ = v___x_2268_;
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_inc(v_a_2301_);
lean_dec(v___x_2268_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2305_ == 0)
{
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2301_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_a_2302_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
else
{
lean_object* v___x_2310_; 
v___x_2310_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_2262_, v___x_2265_, v___y_2260_, v___y_2261_);
lean_dec(v___x_2262_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; lean_object* v_a_2312_; 
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_a_2311_);
v_a_2312_ = lean_ctor_get(v___x_2310_, 1);
lean_inc(v_a_2312_);
lean_dec_ref_known(v___x_2310_, 2);
v___y_2206_ = v_doElems_2264_;
v___y_2207_ = v___y_2254_;
v___y_2208_ = v___y_2256_;
v___y_2209_ = v___y_2255_;
v___y_2210_ = v___x_2263_;
v___y_2211_ = v_h_x3f_2259_;
v_x_2212_ = v_a_2311_;
v_body_2213_ = v___y_2258_;
v___y_2214_ = v___y_2260_;
v___y_2215_ = v_a_2312_;
goto v___jp_2205_;
}
else
{
lean_object* v_a_2313_; lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
lean_dec(v___x_2263_);
lean_dec(v_h_x3f_2259_);
lean_dec(v___y_2258_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec(v_tk_1261_);
v_a_2313_ = lean_ctor_get(v___x_2310_, 0);
v_a_2314_ = lean_ctor_get(v___x_2310_, 1);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2310_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_inc(v_a_2313_);
lean_dec(v___x_2310_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2313_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
}
else
{
v___y_2206_ = v_doElems_2264_;
v___y_2207_ = v___y_2254_;
v___y_2208_ = v___y_2256_;
v___y_2209_ = v___y_2255_;
v___y_2210_ = v___x_2263_;
v___y_2211_ = v_h_x3f_2259_;
v_x_2212_ = v___x_2262_;
v_body_2213_ = v___y_2258_;
v___y_2214_ = v___y_2260_;
v___y_2215_ = v___y_2261_;
goto v___jp_2205_;
}
}
v___jp_2322_:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; 
v___x_2329_ = lean_box(0);
v___x_2330_ = lean_array_get(v___x_2329_, v___y_2325_, v___x_1151_);
lean_inc(v___x_2330_);
v___x_2331_ = l_Lean_Syntax_isOfKind(v___x_2330_, v___x_1457_);
if (v___x_2331_ == 0)
{
lean_object* v___x_2332_; 
lean_dec(v___x_2330_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec(v_tk_1261_);
v___x_2332_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2328_);
return v___x_2332_;
}
else
{
lean_object* v___x_2333_; uint8_t v___x_2334_; 
v___x_2333_ = l_Lean_Syntax_getArg(v___x_2330_, v___x_1151_);
v___x_2334_ = l_Lean_Syntax_isNone(v___x_2333_);
if (v___x_2334_ == 0)
{
uint8_t v___x_2335_; 
lean_inc(v___x_2333_);
v___x_2335_ = l_Lean_Syntax_matchesNull(v___x_2333_, v___x_2203_);
if (v___x_2335_ == 0)
{
lean_object* v___x_2336_; 
lean_dec(v___x_2333_);
lean_dec(v___x_2330_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec(v_tk_1261_);
v___x_2336_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2328_);
return v___x_2336_;
}
else
{
lean_object* v_h_x3f_2337_; lean_object* v___x_2338_; 
v_h_x3f_2337_ = l_Lean_Syntax_getArg(v___x_2333_, v___x_1151_);
lean_dec(v___x_2333_);
v___x_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2338_, 0, v_h_x3f_2337_);
v___y_2254_ = v___y_2323_;
v___y_2255_ = v___y_2325_;
v___y_2256_ = v___y_2324_;
v___y_2257_ = v___x_2330_;
v___y_2258_ = v___y_2326_;
v_h_x3f_2259_ = v___x_2338_;
v___y_2260_ = v___y_2327_;
v___y_2261_ = v___y_2328_;
goto v___jp_2253_;
}
}
else
{
lean_object* v___x_2339_; 
lean_dec(v___x_2333_);
v___x_2339_ = lean_box(0);
v___y_2254_ = v___y_2323_;
v___y_2255_ = v___y_2325_;
v___y_2256_ = v___y_2324_;
v___y_2257_ = v___x_2330_;
v___y_2258_ = v___y_2326_;
v_h_x3f_2259_ = v___x_2339_;
v___y_2260_ = v___y_2327_;
v___y_2261_ = v___y_2328_;
goto v___jp_2253_;
}
}
}
v___jp_2340_:
{
lean_object* v___x_2345_; lean_object* v_body_2346_; lean_object* v_decls_2347_; lean_object* v_decls_2348_; 
v___x_2345_ = lean_unsigned_to_nat(5u);
v_body_2346_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_2345_);
lean_dec(v_stx_1010_);
v_decls_2347_ = l_Lean_Syntax_getArgs(v___x_1263_);
lean_dec(v___x_1263_);
v_decls_2348_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_2347_);
lean_dec_ref(v_decls_2347_);
if (lean_obj_tag(v___y_2341_) == 1)
{
lean_object* v_val_2349_; lean_object* v___x_2350_; uint8_t v___x_2351_; 
v_val_2349_ = lean_ctor_get(v___y_2341_, 0);
v___x_2350_ = lean_array_get_size(v_decls_2348_);
v___x_2351_ = lean_nat_dec_lt(v___x_1262_, v___x_2350_);
if (v___x_2351_ == 0)
{
v___y_2323_ = v_dec_2342_;
v___y_2324_ = v___y_2341_;
v___y_2325_ = v_decls_2348_;
v___y_2326_ = v_body_2346_;
v___y_2327_ = v___y_2343_;
v___y_2328_ = v___y_2344_;
goto v___jp_2322_;
}
else
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__15));
v___x_2353_ = l_Lean_Macro_throwErrorAt___redArg(v_val_2349_, v___x_2352_, v___y_2343_, v___y_2344_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 1);
lean_inc(v_a_2354_);
lean_dec_ref_known(v___x_2353_, 2);
v___y_2323_ = v_dec_2342_;
v___y_2324_ = v___y_2341_;
v___y_2325_ = v_decls_2348_;
v___y_2326_ = v_body_2346_;
v___y_2327_ = v___y_2343_;
v___y_2328_ = v_a_2354_;
goto v___jp_2322_;
}
else
{
lean_object* v_a_2355_; lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2363_; 
lean_dec_ref_known(v___y_2341_, 1);
lean_dec_ref(v_decls_2348_);
lean_dec(v_body_2346_);
lean_dec(v_dec_2342_);
lean_dec(v_tk_1261_);
v_a_2355_ = lean_ctor_get(v___x_2353_, 0);
v_a_2356_ = lean_ctor_get(v___x_2353_, 1);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2358_ = v___x_2353_;
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_inc(v_a_2355_);
lean_dec(v___x_2353_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2361_; 
if (v_isShared_2359_ == 0)
{
v___x_2361_ = v___x_2358_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2355_);
lean_ctor_set(v_reuseFailAlloc_2362_, 1, v_a_2356_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
}
}
else
{
v___y_2323_ = v_dec_2342_;
v___y_2324_ = v___y_2341_;
v___y_2325_ = v_decls_2348_;
v___y_2326_ = v_body_2346_;
v___y_2327_ = v___y_2343_;
v___y_2328_ = v___y_2344_;
goto v___jp_2322_;
}
}
v___jp_2364_:
{
lean_object* v___x_2368_; uint8_t v___x_2369_; 
v___x_2368_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_2252_);
v___x_2369_ = l_Lean_Syntax_isNone(v___x_2368_);
if (v___x_2369_ == 0)
{
uint8_t v___x_2370_; 
lean_inc(v___x_2368_);
v___x_2370_ = l_Lean_Syntax_matchesNull(v___x_2368_, v___x_1262_);
if (v___x_2370_ == 0)
{
lean_object* v___x_2371_; 
lean_dec(v___x_2368_);
lean_dec(v_inv_2365_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_2371_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2367_);
return v___x_2371_;
}
else
{
lean_object* v_dec_2372_; lean_object* v___x_2373_; uint8_t v___x_2374_; 
v_dec_2372_ = l_Lean_Syntax_getArg(v___x_2368_, v___x_1151_);
lean_dec(v___x_2368_);
v___x_2373_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v_dec_2372_);
v___x_2374_ = l_Lean_Syntax_isOfKind(v_dec_2372_, v___x_2373_);
if (v___x_2374_ == 0)
{
lean_object* v___x_2375_; 
lean_dec(v_dec_2372_);
lean_dec(v_inv_2365_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_2375_ = l_Lean_Macro_throwUnsupported___redArg(v___y_2367_);
return v___x_2375_;
}
else
{
lean_object* v___x_2376_; 
v___x_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2376_, 0, v_dec_2372_);
v___y_2341_ = v_inv_2365_;
v_dec_2342_ = v___x_2376_;
v___y_2343_ = v___y_2366_;
v___y_2344_ = v___y_2367_;
goto v___jp_2340_;
}
}
}
else
{
lean_object* v___x_2377_; 
lean_dec(v___x_2368_);
v___x_2377_ = lean_box(0);
v___y_2341_ = v_inv_2365_;
v_dec_2342_ = v___x_2377_;
v___y_2343_ = v___y_2366_;
v___y_2344_ = v___y_2367_;
goto v___jp_2340_;
}
}
}
else
{
v___y_1952_ = v_a_1011_;
v___y_1953_ = v_a_1012_;
goto v___jp_1951_;
}
v___jp_2205_:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2216_ = lean_array_get_size(v___y_2209_);
v___x_2217_ = l_Array_toSubarray___redArg(v___y_2209_, v___x_1262_, v___x_2216_);
lean_inc_ref(v___y_2206_);
v___x_2218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___y_2206_);
lean_ctor_set(v___x_2218_, 1, v_body_2213_);
v___x_2219_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_2204_, v___x_2217_, v___x_2218_, v___y_2214_, v___y_2215_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v_a_2220_; lean_object* v_a_2221_; lean_object* v_fst_2222_; lean_object* v_snd_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2242_; 
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_a_2220_);
v_a_2221_ = lean_ctor_get(v___x_2219_, 1);
lean_inc(v_a_2221_);
lean_dec_ref_known(v___x_2219_, 2);
v_fst_2222_ = lean_ctor_get(v_a_2220_, 0);
v_snd_2223_ = lean_ctor_get(v_a_2220_, 1);
v_isSharedCheck_2242_ = !lean_is_exclusive(v_a_2220_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2225_ = v_a_2220_;
v_isShared_2226_ = v_isSharedCheck_2242_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_snd_2223_);
lean_inc(v_fst_2222_);
lean_dec(v_a_2220_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2242_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v_ref_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2233_; 
v_ref_2227_ = lean_ctor_get(v___y_2214_, 5);
v___x_2228_ = l_Lean_SourceInfo_fromRef(v_ref_2227_, v___x_2204_);
v___x_2229_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
v___x_2230_ = l_Lean_SourceInfo_fromRef(v_tk_1261_, v___x_1149_);
lean_dec(v_tk_1261_);
v___x_2231_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
if (v_isShared_2226_ == 0)
{
lean_ctor_set_tag(v___x_2225_, 2);
lean_ctor_set(v___x_2225_, 1, v___x_2231_);
lean_ctor_set(v___x_2225_, 0, v___x_2230_);
v___x_2233_ = v___x_2225_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2230_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v___x_2231_);
v___x_2233_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_2235_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
if (lean_obj_tag(v___y_2211_) == 1)
{
lean_object* v_val_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v_val_2236_ = lean_ctor_get(v___y_2211_, 0);
lean_inc(v_val_2236_);
lean_dec_ref_known(v___y_2211_, 1);
v___x_2237_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
lean_inc(v___x_2228_);
v___x_2238_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2228_);
lean_ctor_set(v___x_2238_, 1, v___x_2237_);
v___x_2239_ = l_Array_mkArray2___redArg(v_val_2236_, v___x_2238_);
v___y_1459_ = v___x_2234_;
v___y_1460_ = v_snd_2223_;
v___y_1461_ = v___x_2233_;
v___y_1462_ = v___y_2207_;
v___y_1463_ = v___y_2208_;
v___y_1464_ = v___x_2229_;
v___y_1465_ = v___x_2228_;
v___y_1466_ = v___x_2235_;
v___y_1467_ = v_a_2221_;
v___y_1468_ = v___y_2210_;
v___y_1469_ = v_x_2212_;
v___y_1470_ = v_fst_2222_;
v___y_1471_ = v___x_2239_;
goto v___jp_1458_;
}
else
{
lean_object* v___x_2240_; 
lean_dec(v___y_2211_);
v___x_2240_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___y_1459_ = v___x_2234_;
v___y_1460_ = v_snd_2223_;
v___y_1461_ = v___x_2233_;
v___y_1462_ = v___y_2207_;
v___y_1463_ = v___y_2208_;
v___y_1464_ = v___x_2229_;
v___y_1465_ = v___x_2228_;
v___y_1466_ = v___x_2235_;
v___y_1467_ = v_a_2221_;
v___y_1468_ = v___y_2210_;
v___y_1469_ = v_x_2212_;
v___y_1470_ = v_fst_2222_;
v___y_1471_ = v___x_2240_;
goto v___jp_1458_;
}
}
}
}
else
{
lean_object* v_a_2243_; lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2251_; 
lean_dec(v_x_2212_);
lean_dec(v___y_2211_);
lean_dec(v___y_2210_);
lean_dec(v___y_2208_);
lean_dec(v___y_2207_);
lean_dec(v_tk_1261_);
v_a_2243_ = lean_ctor_get(v___x_2219_, 0);
v_a_2244_ = lean_ctor_get(v___x_2219_, 1);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2246_ = v___x_2219_;
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_inc(v_a_2243_);
lean_dec(v___x_2219_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2249_; 
if (v_isShared_2247_ == 0)
{
v___x_2249_ = v___x_2246_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2243_);
lean_ctor_set(v_reuseFailAlloc_2250_, 1, v_a_2244_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
}
else
{
lean_dec(v___x_2201_);
v___y_1952_ = v_a_1011_;
v___y_1953_ = v_a_1012_;
goto v___jp_1951_;
}
}
v___jp_1458_:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
lean_inc_ref(v___y_1466_);
v___x_1472_ = l_Array_append___redArg(v___y_1466_, v___y_1471_);
lean_dec_ref(v___y_1471_);
lean_inc_n(v___y_1459_, 2);
lean_inc_n(v___y_1465_, 4);
v___x_1473_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1473_, 0, v___y_1465_);
lean_ctor_set(v___x_1473_, 1, v___y_1459_);
lean_ctor_set(v___x_1473_, 2, v___x_1472_);
v___x_1474_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_1475_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1475_, 0, v___y_1465_);
lean_ctor_set(v___x_1475_, 1, v___x_1474_);
v___x_1476_ = l_Lean_Syntax_node4(v___y_1465_, v___x_1457_, v___x_1473_, v___y_1469_, v___x_1475_, v___y_1468_);
v___x_1477_ = l_Lean_Syntax_node1(v___y_1465_, v___y_1459_, v___x_1476_);
if (lean_obj_tag(v___y_1463_) == 1)
{
lean_object* v_val_1478_; lean_object* v___x_1479_; 
v_val_1478_ = lean_ctor_get(v___y_1463_, 0);
lean_inc(v_val_1478_);
lean_dec_ref_known(v___y_1463_, 1);
v___x_1479_ = l_Array_mkArray1___redArg(v_val_1478_);
v___y_1245_ = v___y_1459_;
v___y_1246_ = v___y_1461_;
v___y_1247_ = v___y_1460_;
v___y_1248_ = v___y_1462_;
v___y_1249_ = v___y_1464_;
v___y_1250_ = v___y_1465_;
v___y_1251_ = v___y_1466_;
v___y_1252_ = v___y_1467_;
v___y_1253_ = v___x_1477_;
v___y_1254_ = v___y_1470_;
v___y_1255_ = v___x_1479_;
goto v___jp_1244_;
}
else
{
lean_object* v___x_1480_; 
lean_dec(v___y_1463_);
v___x_1480_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___y_1245_ = v___y_1459_;
v___y_1246_ = v___y_1461_;
v___y_1247_ = v___y_1460_;
v___y_1248_ = v___y_1462_;
v___y_1249_ = v___y_1464_;
v___y_1250_ = v___y_1465_;
v___y_1251_ = v___y_1466_;
v___y_1252_ = v___y_1467_;
v___y_1253_ = v___x_1477_;
v___y_1254_ = v___y_1470_;
v___y_1255_ = v___x_1480_;
goto v___jp_1244_;
}
}
v___jp_1481_:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
lean_inc_ref(v___y_1490_);
v___x_1495_ = l_Array_append___redArg(v___y_1490_, v___y_1494_);
lean_dec_ref(v___y_1494_);
lean_inc_n(v___y_1483_, 2);
lean_inc_n(v___y_1493_, 4);
v___x_1496_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1496_, 0, v___y_1493_);
lean_ctor_set(v___x_1496_, 1, v___y_1483_);
lean_ctor_set(v___x_1496_, 2, v___x_1495_);
v___x_1497_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_1498_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1498_, 0, v___y_1493_);
lean_ctor_set(v___x_1498_, 1, v___x_1497_);
v___x_1499_ = l_Lean_Syntax_node4(v___y_1493_, v___x_1457_, v___x_1496_, v___y_1485_, v___x_1498_, v___y_1492_);
v___x_1500_ = l_Lean_Syntax_node1(v___y_1493_, v___y_1483_, v___x_1499_);
if (lean_obj_tag(v___y_1486_) == 1)
{
lean_object* v_val_1501_; lean_object* v___x_1502_; 
v_val_1501_ = lean_ctor_get(v___y_1486_, 0);
lean_inc(v_val_1501_);
lean_dec_ref_known(v___y_1486_, 1);
v___x_1502_ = l_Array_mkArray1___redArg(v_val_1501_);
v___y_1211_ = v___y_1482_;
v___y_1212_ = v___y_1483_;
v___y_1213_ = v___y_1484_;
v___y_1214_ = v___y_1487_;
v___y_1215_ = v___x_1500_;
v___y_1216_ = v___y_1488_;
v___y_1217_ = v___y_1489_;
v___y_1218_ = v___y_1490_;
v___y_1219_ = v___y_1491_;
v___y_1220_ = v___y_1493_;
v___y_1221_ = v___x_1502_;
goto v___jp_1210_;
}
else
{
lean_object* v___x_1503_; 
lean_dec(v___y_1486_);
v___x_1503_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___y_1211_ = v___y_1482_;
v___y_1212_ = v___y_1483_;
v___y_1213_ = v___y_1484_;
v___y_1214_ = v___y_1487_;
v___y_1215_ = v___x_1500_;
v___y_1216_ = v___y_1488_;
v___y_1217_ = v___y_1489_;
v___y_1218_ = v___y_1490_;
v___y_1219_ = v___y_1491_;
v___y_1220_ = v___y_1493_;
v___y_1221_ = v___x_1503_;
goto v___jp_1210_;
}
}
v___jp_1504_:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1515_ = lean_array_get_size(v___y_1509_);
v___x_1516_ = l_Array_toSubarray___redArg(v___y_1509_, v___x_1262_, v___x_1515_);
lean_inc_ref(v___y_1508_);
v___x_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1517_, 0, v___y_1508_);
lean_ctor_set(v___x_1517_, 1, v_body_1512_);
v___x_1518_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg(v___x_1516_, v___x_1517_, v___y_1513_, v___y_1514_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v_a_1520_; lean_object* v_fst_1521_; lean_object* v_snd_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1542_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1519_);
v_a_1520_ = lean_ctor_get(v___x_1518_, 1);
lean_inc(v_a_1520_);
lean_dec_ref_known(v___x_1518_, 2);
v_fst_1521_ = lean_ctor_get(v_a_1519_, 0);
v_snd_1522_ = lean_ctor_get(v_a_1519_, 1);
v_isSharedCheck_1542_ = !lean_is_exclusive(v_a_1519_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1524_ = v_a_1519_;
v_isShared_1525_ = v_isSharedCheck_1542_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_snd_1522_);
lean_inc(v_fst_1521_);
lean_dec(v_a_1519_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1542_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v_ref_1526_; uint8_t v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1533_; 
v_ref_1526_ = lean_ctor_get(v___y_1513_, 5);
v___x_1527_ = 0;
v___x_1528_ = l_Lean_SourceInfo_fromRef(v_ref_1526_, v___x_1527_);
v___x_1529_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
v___x_1530_ = l_Lean_SourceInfo_fromRef(v_tk_1261_, v___x_1149_);
lean_dec(v_tk_1261_);
v___x_1531_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
if (v_isShared_1525_ == 0)
{
lean_ctor_set_tag(v___x_1524_, 2);
lean_ctor_set(v___x_1524_, 1, v___x_1531_);
lean_ctor_set(v___x_1524_, 0, v___x_1530_);
v___x_1533_ = v___x_1524_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1530_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v___x_1531_);
v___x_1533_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1535_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
if (lean_obj_tag(v___y_1507_) == 1)
{
lean_object* v_val_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v_val_1536_ = lean_ctor_get(v___y_1507_, 0);
lean_inc(v_val_1536_);
lean_dec_ref_known(v___y_1507_, 1);
v___x_1537_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
lean_inc(v___x_1528_);
v___x_1538_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1528_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
v___x_1539_ = l_Array_mkArray2___redArg(v_val_1536_, v___x_1538_);
v___y_1482_ = v___y_1505_;
v___y_1483_ = v___x_1534_;
v___y_1484_ = v_fst_1521_;
v___y_1485_ = v_x_1511_;
v___y_1486_ = v___y_1506_;
v___y_1487_ = v_a_1520_;
v___y_1488_ = v___x_1533_;
v___y_1489_ = v_snd_1522_;
v___y_1490_ = v___x_1535_;
v___y_1491_ = v___x_1529_;
v___y_1492_ = v___y_1510_;
v___y_1493_ = v___x_1528_;
v___y_1494_ = v___x_1539_;
goto v___jp_1481_;
}
else
{
lean_object* v___x_1540_; 
lean_dec(v___y_1507_);
v___x_1540_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___y_1482_ = v___y_1505_;
v___y_1483_ = v___x_1534_;
v___y_1484_ = v_fst_1521_;
v___y_1485_ = v_x_1511_;
v___y_1486_ = v___y_1506_;
v___y_1487_ = v_a_1520_;
v___y_1488_ = v___x_1533_;
v___y_1489_ = v_snd_1522_;
v___y_1490_ = v___x_1535_;
v___y_1491_ = v___x_1529_;
v___y_1492_ = v___y_1510_;
v___y_1493_ = v___x_1528_;
v___y_1494_ = v___x_1540_;
goto v___jp_1481_;
}
}
}
}
else
{
lean_object* v_a_1543_; lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1551_; 
lean_dec(v_x_1511_);
lean_dec(v___y_1510_);
lean_dec(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec(v_tk_1261_);
v_a_1543_ = lean_ctor_get(v___x_1518_, 0);
v_a_1544_ = lean_ctor_get(v___x_1518_, 1);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1546_ = v___x_1518_;
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_inc(v_a_1543_);
lean_dec(v___x_1518_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1549_; 
if (v_isShared_1547_ == 0)
{
v___x_1549_ = v___x_1546_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_a_1543_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v_a_1544_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
v___jp_1552_:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v_doElems_1564_; uint8_t v___x_1565_; 
v___x_1562_ = l_Lean_Syntax_getArg(v___y_1555_, v___x_1262_);
v___x_1563_ = l_Lean_Syntax_getArg(v___y_1555_, v___y_1558_);
lean_dec(v___y_1555_);
v_doElems_1564_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_1565_ = l_Lean_Syntax_isIdent(v___x_1562_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; uint8_t v___x_1567_; 
v___x_1566_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_1562_);
v___x_1567_ = l_Lean_Syntax_isOfKind(v___x_1562_, v___x_1566_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1562_, v___x_1567_, v___y_1560_, v___y_1561_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v_a_1570_; lean_object* v_ref_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc_n(v_a_1569_, 2);
v_a_1570_ = lean_ctor_get(v___x_1568_, 1);
lean_inc(v_a_1570_);
lean_dec_ref_known(v___x_1568_, 2);
v_ref_1571_ = lean_ctor_get(v___y_1560_, 5);
v___x_1572_ = l_Lean_SourceInfo_fromRef(v_ref_1571_, v___x_1567_);
v___x_1573_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_1574_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1575_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
v___x_1576_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_1577_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_n(v___x_1572_, 15);
v___x_1578_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1572_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_1580_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1572_);
lean_ctor_set(v___x_1580_, 1, v___x_1574_);
lean_ctor_set(v___x_1580_, 2, v___x_1579_);
v___x_1581_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_1580_, 4);
v___x_1582_ = l_Lean_Syntax_node2(v___x_1572_, v___x_1581_, v___x_1580_, v_a_1569_);
v___x_1583_ = l_Lean_Syntax_node1(v___x_1572_, v___x_1574_, v___x_1582_);
v___x_1584_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_1585_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1572_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
v___x_1586_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_1587_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_1588_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_1589_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1572_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
v___x_1590_ = l_Lean_Syntax_node1(v___x_1572_, v___x_1574_, v___x_1562_);
v___x_1591_ = l_Lean_Syntax_node1(v___x_1572_, v___x_1574_, v___x_1590_);
v___x_1592_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_1593_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1572_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
v___x_1594_ = l_Lean_Syntax_node4(v___x_1572_, v___x_1587_, v___x_1589_, v___x_1591_, v___x_1593_, v___y_1556_);
v___x_1595_ = l_Lean_Syntax_node1(v___x_1572_, v___x_1574_, v___x_1594_);
v___x_1596_ = l_Lean_Syntax_node1(v___x_1572_, v___x_1586_, v___x_1595_);
v___x_1597_ = l_Lean_Syntax_node7(v___x_1572_, v___x_1576_, v___x_1578_, v___x_1580_, v___x_1580_, v___x_1580_, v___x_1583_, v___x_1585_, v___x_1596_);
v___x_1598_ = l_Lean_Syntax_node2(v___x_1572_, v___x_1575_, v___x_1597_, v___x_1580_);
v___x_1599_ = l_Lean_Syntax_node1(v___x_1572_, v___x_1574_, v___x_1598_);
v___x_1600_ = l_Lean_Syntax_node1(v___x_1572_, v___x_1573_, v___x_1599_);
v___y_1505_ = v___y_1553_;
v___y_1506_ = v___y_1554_;
v___y_1507_ = v_h_x3f_1559_;
v___y_1508_ = v_doElems_1564_;
v___y_1509_ = v___y_1557_;
v___y_1510_ = v___x_1563_;
v_x_1511_ = v_a_1569_;
v_body_1512_ = v___x_1600_;
v___y_1513_ = v___y_1560_;
v___y_1514_ = v_a_1570_;
goto v___jp_1504_;
}
else
{
lean_object* v_a_1601_; lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_dec(v___x_1563_);
lean_dec(v___x_1562_);
lean_dec(v_h_x3f_1559_);
lean_dec_ref(v___y_1557_);
lean_dec(v___y_1556_);
lean_dec(v___y_1554_);
lean_dec(v___y_1553_);
lean_dec(v_tk_1261_);
v_a_1601_ = lean_ctor_get(v___x_1568_, 0);
v_a_1602_ = lean_ctor_get(v___x_1568_, 1);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1568_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_inc(v_a_1601_);
lean_dec(v___x_1568_);
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
else
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1562_, v___x_1565_, v___y_1560_, v___y_1561_);
lean_dec(v___x_1562_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v_a_1612_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_a_1611_);
v_a_1612_ = lean_ctor_get(v___x_1610_, 1);
lean_inc(v_a_1612_);
lean_dec_ref_known(v___x_1610_, 2);
v___y_1505_ = v___y_1553_;
v___y_1506_ = v___y_1554_;
v___y_1507_ = v_h_x3f_1559_;
v___y_1508_ = v_doElems_1564_;
v___y_1509_ = v___y_1557_;
v___y_1510_ = v___x_1563_;
v_x_1511_ = v_a_1611_;
v_body_1512_ = v___y_1556_;
v___y_1513_ = v___y_1560_;
v___y_1514_ = v_a_1612_;
goto v___jp_1504_;
}
else
{
lean_object* v_a_1613_; lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
lean_dec(v___x_1563_);
lean_dec(v_h_x3f_1559_);
lean_dec_ref(v___y_1557_);
lean_dec(v___y_1556_);
lean_dec(v___y_1554_);
lean_dec(v___y_1553_);
lean_dec(v_tk_1261_);
v_a_1613_ = lean_ctor_get(v___x_1610_, 0);
v_a_1614_ = lean_ctor_get(v___x_1610_, 1);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1616_ = v___x_1610_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_inc(v_a_1613_);
lean_dec(v___x_1610_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1613_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_a_1614_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
}
else
{
v___y_1505_ = v___y_1553_;
v___y_1506_ = v___y_1554_;
v___y_1507_ = v_h_x3f_1559_;
v___y_1508_ = v_doElems_1564_;
v___y_1509_ = v___y_1557_;
v___y_1510_ = v___x_1563_;
v_x_1511_ = v___x_1562_;
v_body_1512_ = v___y_1556_;
v___y_1513_ = v___y_1560_;
v___y_1514_ = v___y_1561_;
goto v___jp_1504_;
}
}
v___jp_1622_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; uint8_t v___x_1633_; 
v___x_1631_ = lean_box(0);
v___x_1632_ = lean_array_get(v___x_1631_, v___y_1628_, v___x_1151_);
lean_inc(v___x_1632_);
v___x_1633_ = l_Lean_Syntax_isOfKind(v___x_1632_, v___x_1457_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; 
lean_dec(v___x_1632_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec(v_tk_1261_);
v___x_1634_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1630_);
return v___x_1634_;
}
else
{
lean_object* v___x_1635_; uint8_t v___x_1636_; 
v___x_1635_ = l_Lean_Syntax_getArg(v___x_1632_, v___x_1151_);
v___x_1636_ = l_Lean_Syntax_isNone(v___x_1635_);
if (v___x_1636_ == 0)
{
uint8_t v___x_1637_; 
lean_inc(v___x_1635_);
v___x_1637_ = l_Lean_Syntax_matchesNull(v___x_1635_, v___y_1626_);
if (v___x_1637_ == 0)
{
lean_object* v___x_1638_; 
lean_dec(v___x_1635_);
lean_dec(v___x_1632_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec(v_tk_1261_);
v___x_1638_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1630_);
return v___x_1638_;
}
else
{
lean_object* v_h_x3f_1639_; lean_object* v___x_1640_; 
v_h_x3f_1639_ = l_Lean_Syntax_getArg(v___x_1635_, v___x_1151_);
lean_dec(v___x_1635_);
v___x_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1640_, 0, v_h_x3f_1639_);
v___y_1553_ = v___y_1623_;
v___y_1554_ = v___y_1624_;
v___y_1555_ = v___x_1632_;
v___y_1556_ = v___y_1625_;
v___y_1557_ = v___y_1628_;
v___y_1558_ = v___y_1627_;
v_h_x3f_1559_ = v___x_1640_;
v___y_1560_ = v___y_1629_;
v___y_1561_ = v___y_1630_;
goto v___jp_1552_;
}
}
else
{
lean_object* v___x_1641_; 
lean_dec(v___x_1635_);
v___x_1641_ = lean_box(0);
v___y_1553_ = v___y_1623_;
v___y_1554_ = v___y_1624_;
v___y_1555_ = v___x_1632_;
v___y_1556_ = v___y_1625_;
v___y_1557_ = v___y_1628_;
v___y_1558_ = v___y_1627_;
v_h_x3f_1559_ = v___x_1641_;
v___y_1560_ = v___y_1629_;
v___y_1561_ = v___y_1630_;
goto v___jp_1552_;
}
}
}
v___jp_1642_:
{
lean_object* v_decls_1650_; lean_object* v_decls_1651_; 
v_decls_1650_ = l_Lean_Syntax_getArgs(v___x_1263_);
lean_dec(v___x_1263_);
v_decls_1651_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_1650_);
lean_dec_ref(v_decls_1650_);
if (lean_obj_tag(v_inv_1645_) == 1)
{
lean_object* v_val_1652_; lean_object* v___x_1653_; uint8_t v___x_1654_; 
v_val_1652_ = lean_ctor_get(v_inv_1645_, 0);
v___x_1653_ = lean_array_get_size(v_decls_1651_);
v___x_1654_ = lean_nat_dec_lt(v___x_1262_, v___x_1653_);
if (v___x_1654_ == 0)
{
v___y_1623_ = v_dec_1646_;
v___y_1624_ = v_inv_1645_;
v___y_1625_ = v_body_1647_;
v___y_1626_ = v___y_1643_;
v___y_1627_ = v___y_1644_;
v___y_1628_ = v_decls_1651_;
v___y_1629_ = v___y_1648_;
v___y_1630_ = v___y_1649_;
goto v___jp_1622_;
}
else
{
lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1655_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__15));
v___x_1656_ = l_Lean_Macro_throwErrorAt___redArg(v_val_1652_, v___x_1655_, v___y_1648_, v___y_1649_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 1);
lean_inc(v_a_1657_);
lean_dec_ref_known(v___x_1656_, 2);
v___y_1623_ = v_dec_1646_;
v___y_1624_ = v_inv_1645_;
v___y_1625_ = v_body_1647_;
v___y_1626_ = v___y_1643_;
v___y_1627_ = v___y_1644_;
v___y_1628_ = v_decls_1651_;
v___y_1629_ = v___y_1648_;
v___y_1630_ = v_a_1657_;
goto v___jp_1622_;
}
else
{
lean_object* v_a_1658_; lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
lean_dec_ref_known(v_inv_1645_, 1);
lean_dec_ref(v_decls_1651_);
lean_dec(v_body_1647_);
lean_dec(v_dec_1646_);
lean_dec(v_tk_1261_);
v_a_1658_ = lean_ctor_get(v___x_1656_, 0);
v_a_1659_ = lean_ctor_get(v___x_1656_, 1);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1656_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_inc(v_a_1658_);
lean_dec(v___x_1656_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1658_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
}
else
{
v___y_1623_ = v_dec_1646_;
v___y_1624_ = v_inv_1645_;
v___y_1625_ = v_body_1647_;
v___y_1626_ = v___y_1643_;
v___y_1627_ = v___y_1644_;
v___y_1628_ = v_decls_1651_;
v___y_1629_ = v___y_1648_;
v___y_1630_ = v___y_1649_;
goto v___jp_1622_;
}
}
v___jp_1667_:
{
if (v___y_1669_ == 0)
{
if (v___y_1673_ == 0)
{
lean_object* v___x_1677_; 
lean_dec(v_inv_1674_);
lean_dec(v___y_1670_);
lean_dec(v___y_1668_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
v___x_1677_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1676_);
return v___x_1677_;
}
else
{
lean_object* v_dec_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; 
v_dec_1678_ = l_Lean_Syntax_getArg(v___y_1670_, v___x_1151_);
lean_dec(v___y_1670_);
v___x_1679_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v_dec_1678_);
v___x_1680_ = l_Lean_Syntax_isOfKind(v_dec_1678_, v___x_1679_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1681_; 
lean_dec(v_dec_1678_);
lean_dec(v_inv_1674_);
lean_dec(v___y_1668_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
v___x_1681_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1676_);
return v___x_1681_;
}
else
{
lean_object* v___x_1682_; 
v___x_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1682_, 0, v_dec_1678_);
v___y_1643_ = v___y_1671_;
v___y_1644_ = v___y_1672_;
v_inv_1645_ = v_inv_1674_;
v_dec_1646_ = v___x_1682_;
v_body_1647_ = v___y_1668_;
v___y_1648_ = v___y_1675_;
v___y_1649_ = v___y_1676_;
goto v___jp_1642_;
}
}
}
else
{
lean_object* v___x_1683_; 
lean_dec(v___y_1670_);
v___x_1683_ = lean_box(0);
v___y_1643_ = v___y_1671_;
v___y_1644_ = v___y_1672_;
v_inv_1645_ = v_inv_1674_;
v_dec_1646_ = v___x_1683_;
v_body_1647_ = v___y_1668_;
v___y_1648_ = v___y_1675_;
v___y_1649_ = v___y_1676_;
goto v___jp_1642_;
}
}
v___jp_1684_:
{
if (v___y_1686_ == 0)
{
if (v___y_1691_ == 0)
{
lean_object* v___x_1695_; 
lean_dec(v_inv_1692_);
lean_dec(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
v___x_1695_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1694_);
return v___x_1695_;
}
else
{
if (v___y_1685_ == 0)
{
lean_object* v___x_1696_; 
lean_dec(v_inv_1692_);
lean_dec(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
v___x_1696_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1694_);
return v___x_1696_;
}
else
{
lean_object* v___x_1697_; 
v___x_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1697_, 0, v___y_1687_);
v___y_1643_ = v___y_1689_;
v___y_1644_ = v___y_1690_;
v_inv_1645_ = v_inv_1692_;
v_dec_1646_ = v___x_1697_;
v_body_1647_ = v___y_1688_;
v___y_1648_ = v___y_1693_;
v___y_1649_ = v___y_1694_;
goto v___jp_1642_;
}
}
}
else
{
lean_object* v___x_1698_; 
lean_dec(v___y_1687_);
v___x_1698_ = lean_box(0);
v___y_1643_ = v___y_1689_;
v___y_1644_ = v___y_1690_;
v_inv_1645_ = v_inv_1692_;
v_dec_1646_ = v___x_1698_;
v_body_1647_ = v___y_1688_;
v___y_1648_ = v___y_1693_;
v___y_1649_ = v___y_1694_;
goto v___jp_1642_;
}
}
v___jp_1699_:
{
lean_object* v___x_1705_; uint8_t v___x_1706_; 
v___x_1705_ = l_Lean_Syntax_getArg(v_stx_1010_, v___y_1702_);
v___x_1706_ = l_Lean_Syntax_isNone(v___x_1705_);
if (v___x_1706_ == 0)
{
uint8_t v___x_1707_; 
lean_inc(v___x_1705_);
v___x_1707_ = l_Lean_Syntax_matchesNull(v___x_1705_, v___x_1262_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; lean_object* v_body_1709_; uint8_t v___x_1710_; 
v___x_1708_ = lean_unsigned_to_nat(5u);
v_body_1709_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_1708_);
lean_dec(v_stx_1010_);
v___x_1710_ = l_Lean_Syntax_isNone(v___y_1700_);
if (v___x_1710_ == 0)
{
uint8_t v___x_1711_; 
lean_inc(v___y_1700_);
v___x_1711_ = l_Lean_Syntax_matchesNull(v___y_1700_, v___x_1262_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; 
lean_dec(v_body_1709_);
lean_dec(v___x_1705_);
lean_dec(v___y_1700_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
v___x_1712_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1704_);
return v___x_1712_;
}
else
{
lean_object* v_inv_1713_; lean_object* v___x_1714_; uint8_t v___x_1715_; 
v_inv_1713_ = l_Lean_Syntax_getArg(v___y_1700_, v___x_1151_);
lean_dec(v___y_1700_);
v___x_1714_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__19));
lean_inc(v_inv_1713_);
v___x_1715_ = l_Lean_Syntax_isOfKind(v_inv_1713_, v___x_1714_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1716_; 
lean_dec(v_inv_1713_);
lean_dec(v_body_1709_);
lean_dec(v___x_1705_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
v___x_1716_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1704_);
return v___x_1716_;
}
else
{
lean_object* v___x_1717_; 
v___x_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1717_, 0, v_inv_1713_);
v___y_1668_ = v_body_1709_;
v___y_1669_ = v___x_1706_;
v___y_1670_ = v___x_1705_;
v___y_1671_ = v___y_1701_;
v___y_1672_ = v___y_1702_;
v___y_1673_ = v___x_1707_;
v_inv_1674_ = v___x_1717_;
v___y_1675_ = v___y_1703_;
v___y_1676_ = v___y_1704_;
goto v___jp_1667_;
}
}
}
else
{
lean_object* v___x_1718_; 
lean_dec(v___y_1700_);
v___x_1718_ = lean_box(0);
v___y_1668_ = v_body_1709_;
v___y_1669_ = v___x_1706_;
v___y_1670_ = v___x_1705_;
v___y_1671_ = v___y_1701_;
v___y_1672_ = v___y_1702_;
v___y_1673_ = v___x_1707_;
v_inv_1674_ = v___x_1718_;
v___y_1675_ = v___y_1703_;
v___y_1676_ = v___y_1704_;
goto v___jp_1667_;
}
}
else
{
lean_object* v_dec_1719_; lean_object* v___x_1720_; uint8_t v___x_1721_; 
v_dec_1719_ = l_Lean_Syntax_getArg(v___x_1705_, v___x_1151_);
lean_dec(v___x_1705_);
v___x_1720_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v_dec_1719_);
v___x_1721_ = l_Lean_Syntax_isOfKind(v_dec_1719_, v___x_1720_);
if (v___x_1721_ == 0)
{
lean_object* v___x_1722_; lean_object* v_body_1723_; uint8_t v___x_1724_; 
v___x_1722_ = lean_unsigned_to_nat(5u);
v_body_1723_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_1722_);
lean_dec(v_stx_1010_);
v___x_1724_ = l_Lean_Syntax_isNone(v___y_1700_);
if (v___x_1724_ == 0)
{
uint8_t v___x_1725_; 
lean_inc(v___y_1700_);
v___x_1725_ = l_Lean_Syntax_matchesNull(v___y_1700_, v___x_1262_);
if (v___x_1725_ == 0)
{
lean_object* v___x_1726_; 
lean_dec(v_body_1723_);
lean_dec(v_dec_1719_);
lean_dec(v___y_1700_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
v___x_1726_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1704_);
return v___x_1726_;
}
else
{
lean_object* v_inv_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; 
v_inv_1727_ = l_Lean_Syntax_getArg(v___y_1700_, v___x_1151_);
lean_dec(v___y_1700_);
v___x_1728_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__19));
lean_inc(v_inv_1727_);
v___x_1729_ = l_Lean_Syntax_isOfKind(v_inv_1727_, v___x_1728_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; 
lean_dec(v_inv_1727_);
lean_dec(v_body_1723_);
lean_dec(v_dec_1719_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
v___x_1730_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1704_);
return v___x_1730_;
}
else
{
lean_object* v___x_1731_; 
v___x_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1731_, 0, v_inv_1727_);
v___y_1685_ = v___x_1721_;
v___y_1686_ = v___x_1706_;
v___y_1687_ = v_dec_1719_;
v___y_1688_ = v_body_1723_;
v___y_1689_ = v___y_1701_;
v___y_1690_ = v___y_1702_;
v___y_1691_ = v___x_1707_;
v_inv_1692_ = v___x_1731_;
v___y_1693_ = v___y_1703_;
v___y_1694_ = v___y_1704_;
goto v___jp_1684_;
}
}
}
else
{
lean_object* v___x_1732_; 
lean_dec(v___y_1700_);
v___x_1732_ = lean_box(0);
v___y_1685_ = v___x_1721_;
v___y_1686_ = v___x_1706_;
v___y_1687_ = v_dec_1719_;
v___y_1688_ = v_body_1723_;
v___y_1689_ = v___y_1701_;
v___y_1690_ = v___y_1702_;
v___y_1691_ = v___x_1707_;
v_inv_1692_ = v___x_1732_;
v___y_1693_ = v___y_1703_;
v___y_1694_ = v___y_1704_;
goto v___jp_1684_;
}
}
else
{
lean_object* v___x_1733_; 
lean_dec(v_dec_1719_);
lean_dec(v___y_1700_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_1733_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1704_);
return v___x_1733_;
}
}
}
else
{
lean_object* v___x_1734_; 
lean_dec(v___x_1705_);
lean_dec(v___y_1700_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_1734_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1704_);
return v___x_1734_;
}
}
v___jp_1735_:
{
lean_object* v___x_1742_; lean_object* v_body_1743_; 
v___x_1742_ = lean_unsigned_to_nat(5u);
v_body_1743_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_1742_);
lean_dec(v_stx_1010_);
v___y_1643_ = v___y_1737_;
v___y_1644_ = v___y_1738_;
v_inv_1645_ = v___y_1736_;
v_dec_1646_ = v_dec_1739_;
v_body_1647_ = v_body_1743_;
v___y_1648_ = v___y_1740_;
v___y_1649_ = v___y_1741_;
goto v___jp_1642_;
}
v___jp_1744_:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
lean_inc_ref(v___y_1750_);
v___x_1758_ = l_Array_append___redArg(v___y_1750_, v___y_1757_);
lean_dec_ref(v___y_1757_);
lean_inc_n(v___y_1749_, 2);
lean_inc_n(v___y_1747_, 4);
v___x_1759_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1759_, 0, v___y_1747_);
lean_ctor_set(v___x_1759_, 1, v___y_1749_);
lean_ctor_set(v___x_1759_, 2, v___x_1758_);
v___x_1760_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_1761_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___y_1747_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
v___x_1762_ = l_Lean_Syntax_node4(v___y_1747_, v___x_1457_, v___x_1759_, v___y_1748_, v___x_1761_, v___y_1756_);
v___x_1763_ = l_Lean_Syntax_node1(v___y_1747_, v___y_1749_, v___x_1762_);
if (lean_obj_tag(v___y_1745_) == 1)
{
lean_object* v_val_1764_; lean_object* v___x_1765_; 
v_val_1764_ = lean_ctor_get(v___y_1745_, 0);
lean_inc(v_val_1764_);
lean_dec_ref_known(v___y_1745_, 1);
v___x_1765_ = l_Array_mkArray1___redArg(v_val_1764_);
v___y_1228_ = v___x_1763_;
v___y_1229_ = v___y_1746_;
v___y_1230_ = v___y_1747_;
v___y_1231_ = v___y_1749_;
v___y_1232_ = v___y_1750_;
v___y_1233_ = v___y_1751_;
v___y_1234_ = v___y_1753_;
v___y_1235_ = v___y_1752_;
v___y_1236_ = v___y_1754_;
v___y_1237_ = v___y_1755_;
v___y_1238_ = v___x_1765_;
goto v___jp_1227_;
}
else
{
lean_object* v___x_1766_; 
lean_dec(v___y_1745_);
v___x_1766_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___y_1228_ = v___x_1763_;
v___y_1229_ = v___y_1746_;
v___y_1230_ = v___y_1747_;
v___y_1231_ = v___y_1749_;
v___y_1232_ = v___y_1750_;
v___y_1233_ = v___y_1751_;
v___y_1234_ = v___y_1753_;
v___y_1235_ = v___y_1752_;
v___y_1236_ = v___y_1754_;
v___y_1237_ = v___y_1755_;
v___y_1238_ = v___x_1766_;
goto v___jp_1227_;
}
}
v___jp_1767_:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1779_ = lean_array_get_size(v___y_1769_);
v___x_1780_ = l_Array_toSubarray___redArg(v___y_1769_, v___x_1262_, v___x_1779_);
lean_inc_ref(v___y_1770_);
v___x_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___y_1770_);
lean_ctor_set(v___x_1781_, 1, v_body_1776_);
v___x_1782_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___y_1774_, v___x_1780_, v___x_1781_, v___y_1777_, v___y_1778_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v_a_1784_; lean_object* v_fst_1785_; lean_object* v_snd_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1805_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1783_);
v_a_1784_ = lean_ctor_get(v___x_1782_, 1);
lean_inc(v_a_1784_);
lean_dec_ref_known(v___x_1782_, 2);
v_fst_1785_ = lean_ctor_get(v_a_1783_, 0);
v_snd_1786_ = lean_ctor_get(v_a_1783_, 1);
v_isSharedCheck_1805_ = !lean_is_exclusive(v_a_1783_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1788_ = v_a_1783_;
v_isShared_1789_ = v_isSharedCheck_1805_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_snd_1786_);
lean_inc(v_fst_1785_);
lean_dec(v_a_1783_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1805_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v_ref_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1796_; 
v_ref_1790_ = lean_ctor_get(v___y_1777_, 5);
v___x_1791_ = l_Lean_SourceInfo_fromRef(v_ref_1790_, v___y_1774_);
v___x_1792_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
v___x_1793_ = l_Lean_SourceInfo_fromRef(v_tk_1261_, v___x_1149_);
lean_dec(v_tk_1261_);
v___x_1794_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
if (v_isShared_1789_ == 0)
{
lean_ctor_set_tag(v___x_1788_, 2);
lean_ctor_set(v___x_1788_, 1, v___x_1794_);
lean_ctor_set(v___x_1788_, 0, v___x_1793_);
v___x_1796_ = v___x_1788_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1793_);
lean_ctor_set(v_reuseFailAlloc_1804_, 1, v___x_1794_);
v___x_1796_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1798_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
if (lean_obj_tag(v___y_1771_) == 1)
{
lean_object* v_val_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v_val_1799_ = lean_ctor_get(v___y_1771_, 0);
lean_inc(v_val_1799_);
lean_dec_ref_known(v___y_1771_, 1);
v___x_1800_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
lean_inc(v___x_1791_);
v___x_1801_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1791_);
lean_ctor_set(v___x_1801_, 1, v___x_1800_);
v___x_1802_ = l_Array_mkArray2___redArg(v_val_1799_, v___x_1801_);
v___y_1745_ = v___y_1768_;
v___y_1746_ = v_fst_1785_;
v___y_1747_ = v___x_1791_;
v___y_1748_ = v_x_1775_;
v___y_1749_ = v___x_1797_;
v___y_1750_ = v___x_1798_;
v___y_1751_ = v_a_1784_;
v___y_1752_ = v___x_1792_;
v___y_1753_ = v_snd_1786_;
v___y_1754_ = v___x_1796_;
v___y_1755_ = v___y_1773_;
v___y_1756_ = v___y_1772_;
v___y_1757_ = v___x_1802_;
goto v___jp_1744_;
}
else
{
lean_object* v___x_1803_; 
lean_dec(v___y_1771_);
v___x_1803_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___y_1745_ = v___y_1768_;
v___y_1746_ = v_fst_1785_;
v___y_1747_ = v___x_1791_;
v___y_1748_ = v_x_1775_;
v___y_1749_ = v___x_1797_;
v___y_1750_ = v___x_1798_;
v___y_1751_ = v_a_1784_;
v___y_1752_ = v___x_1792_;
v___y_1753_ = v_snd_1786_;
v___y_1754_ = v___x_1796_;
v___y_1755_ = v___y_1773_;
v___y_1756_ = v___y_1772_;
v___y_1757_ = v___x_1803_;
goto v___jp_1744_;
}
}
}
}
else
{
lean_object* v_a_1806_; lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1814_; 
lean_dec(v_x_1775_);
lean_dec(v___y_1773_);
lean_dec(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec(v___y_1768_);
lean_dec(v_tk_1261_);
v_a_1806_ = lean_ctor_get(v___x_1782_, 0);
v_a_1807_ = lean_ctor_get(v___x_1782_, 1);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1809_ = v___x_1782_;
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_inc(v_a_1806_);
lean_dec(v___x_1782_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1812_; 
if (v_isShared_1810_ == 0)
{
v___x_1812_ = v___x_1809_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1806_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v_a_1807_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
v___jp_1815_:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v_doElems_1828_; uint8_t v___x_1829_; 
v___x_1826_ = l_Lean_Syntax_getArg(v___y_1821_, v___x_1262_);
v___x_1827_ = l_Lean_Syntax_getArg(v___y_1821_, v___y_1820_);
lean_dec(v___y_1821_);
v_doElems_1828_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_1829_ = l_Lean_Syntax_isIdent(v___x_1826_);
if (v___x_1829_ == 0)
{
lean_object* v___x_1830_; uint8_t v___x_1831_; 
v___x_1830_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_1826_);
v___x_1831_ = l_Lean_Syntax_isOfKind(v___x_1826_, v___x_1830_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; 
v___x_1832_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1826_, v___y_1822_, v___y_1824_, v___y_1825_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v_a_1833_; lean_object* v_a_1834_; lean_object* v_ref_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
lean_inc_n(v_a_1833_, 2);
v_a_1834_ = lean_ctor_get(v___x_1832_, 1);
lean_inc(v_a_1834_);
lean_dec_ref_known(v___x_1832_, 2);
v_ref_1835_ = lean_ctor_get(v___y_1824_, 5);
v___x_1836_ = l_Lean_SourceInfo_fromRef(v_ref_1835_, v___y_1822_);
v___x_1837_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_1838_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1839_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
v___x_1840_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_1841_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_n(v___x_1836_, 15);
v___x_1842_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1836_);
lean_ctor_set(v___x_1842_, 1, v___x_1841_);
v___x_1843_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_1844_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1836_);
lean_ctor_set(v___x_1844_, 1, v___x_1838_);
lean_ctor_set(v___x_1844_, 2, v___x_1843_);
v___x_1845_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_1844_, 4);
v___x_1846_ = l_Lean_Syntax_node2(v___x_1836_, v___x_1845_, v___x_1844_, v_a_1833_);
v___x_1847_ = l_Lean_Syntax_node1(v___x_1836_, v___x_1838_, v___x_1846_);
v___x_1848_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_1849_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1836_);
lean_ctor_set(v___x_1849_, 1, v___x_1848_);
v___x_1850_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_1851_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_1852_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_1853_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1836_);
lean_ctor_set(v___x_1853_, 1, v___x_1852_);
v___x_1854_ = l_Lean_Syntax_node1(v___x_1836_, v___x_1838_, v___x_1826_);
v___x_1855_ = l_Lean_Syntax_node1(v___x_1836_, v___x_1838_, v___x_1854_);
v___x_1856_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_1857_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1836_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
v___x_1858_ = l_Lean_Syntax_node4(v___x_1836_, v___x_1851_, v___x_1853_, v___x_1855_, v___x_1857_, v___y_1817_);
v___x_1859_ = l_Lean_Syntax_node1(v___x_1836_, v___x_1838_, v___x_1858_);
v___x_1860_ = l_Lean_Syntax_node1(v___x_1836_, v___x_1850_, v___x_1859_);
v___x_1861_ = l_Lean_Syntax_node7(v___x_1836_, v___x_1840_, v___x_1842_, v___x_1844_, v___x_1844_, v___x_1844_, v___x_1847_, v___x_1849_, v___x_1860_);
v___x_1862_ = l_Lean_Syntax_node2(v___x_1836_, v___x_1839_, v___x_1861_, v___x_1844_);
v___x_1863_ = l_Lean_Syntax_node1(v___x_1836_, v___x_1838_, v___x_1862_);
v___x_1864_ = l_Lean_Syntax_node1(v___x_1836_, v___x_1837_, v___x_1863_);
v___y_1768_ = v___y_1816_;
v___y_1769_ = v___y_1818_;
v___y_1770_ = v_doElems_1828_;
v___y_1771_ = v_h_x3f_1823_;
v___y_1772_ = v___x_1827_;
v___y_1773_ = v___y_1819_;
v___y_1774_ = v___y_1822_;
v_x_1775_ = v_a_1833_;
v_body_1776_ = v___x_1864_;
v___y_1777_ = v___y_1824_;
v___y_1778_ = v_a_1834_;
goto v___jp_1767_;
}
else
{
lean_object* v_a_1865_; lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
lean_dec(v___x_1827_);
lean_dec(v___x_1826_);
lean_dec(v_h_x3f_1823_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec(v_tk_1261_);
v_a_1865_ = lean_ctor_get(v___x_1832_, 0);
v_a_1866_ = lean_ctor_get(v___x_1832_, 1);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1832_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_inc(v_a_1865_);
lean_dec(v___x_1832_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1865_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v_a_1866_);
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
else
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1826_, v___y_1822_, v___y_1824_, v___y_1825_);
lean_dec(v___x_1826_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1875_; lean_object* v_a_1876_; 
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_a_1875_);
v_a_1876_ = lean_ctor_get(v___x_1874_, 1);
lean_inc(v_a_1876_);
lean_dec_ref_known(v___x_1874_, 2);
v___y_1768_ = v___y_1816_;
v___y_1769_ = v___y_1818_;
v___y_1770_ = v_doElems_1828_;
v___y_1771_ = v_h_x3f_1823_;
v___y_1772_ = v___x_1827_;
v___y_1773_ = v___y_1819_;
v___y_1774_ = v___y_1822_;
v_x_1775_ = v_a_1875_;
v_body_1776_ = v___y_1817_;
v___y_1777_ = v___y_1824_;
v___y_1778_ = v_a_1876_;
goto v___jp_1767_;
}
else
{
lean_object* v_a_1877_; lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1885_; 
lean_dec(v___x_1827_);
lean_dec(v_h_x3f_1823_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec(v_tk_1261_);
v_a_1877_ = lean_ctor_get(v___x_1874_, 0);
v_a_1878_ = lean_ctor_get(v___x_1874_, 1);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1880_ = v___x_1874_;
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_inc(v_a_1877_);
lean_dec(v___x_1874_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1883_; 
if (v_isShared_1881_ == 0)
{
v___x_1883_ = v___x_1880_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1877_);
lean_ctor_set(v_reuseFailAlloc_1884_, 1, v_a_1878_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
}
else
{
v___y_1768_ = v___y_1816_;
v___y_1769_ = v___y_1818_;
v___y_1770_ = v_doElems_1828_;
v___y_1771_ = v_h_x3f_1823_;
v___y_1772_ = v___x_1827_;
v___y_1773_ = v___y_1819_;
v___y_1774_ = v___y_1822_;
v_x_1775_ = v___x_1826_;
v_body_1776_ = v___y_1817_;
v___y_1777_ = v___y_1824_;
v___y_1778_ = v___y_1825_;
goto v___jp_1767_;
}
}
v___jp_1886_:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; uint8_t v___x_1898_; 
v___x_1896_ = lean_box(0);
v___x_1897_ = lean_array_get(v___x_1896_, v___y_1890_, v___x_1151_);
lean_inc(v___x_1897_);
v___x_1898_ = l_Lean_Syntax_isOfKind(v___x_1897_, v___x_1457_);
if (v___x_1898_ == 0)
{
lean_object* v___x_1899_; 
lean_dec(v___x_1897_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec(v___y_1887_);
lean_dec(v_tk_1261_);
v___x_1899_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1895_);
return v___x_1899_;
}
else
{
lean_object* v___x_1900_; uint8_t v___x_1901_; 
v___x_1900_ = l_Lean_Syntax_getArg(v___x_1897_, v___x_1151_);
v___x_1901_ = l_Lean_Syntax_isNone(v___x_1900_);
if (v___x_1901_ == 0)
{
uint8_t v___x_1902_; 
lean_inc(v___x_1900_);
v___x_1902_ = l_Lean_Syntax_matchesNull(v___x_1900_, v___y_1888_);
if (v___x_1902_ == 0)
{
lean_object* v___x_1903_; 
lean_dec(v___x_1900_);
lean_dec(v___x_1897_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec(v___y_1887_);
lean_dec(v_tk_1261_);
v___x_1903_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1895_);
return v___x_1903_;
}
else
{
lean_object* v_h_x3f_1904_; lean_object* v___x_1905_; 
v_h_x3f_1904_ = l_Lean_Syntax_getArg(v___x_1900_, v___x_1151_);
lean_dec(v___x_1900_);
v___x_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1905_, 0, v_h_x3f_1904_);
v___y_1816_ = v___y_1887_;
v___y_1817_ = v___y_1889_;
v___y_1818_ = v___y_1890_;
v___y_1819_ = v___y_1891_;
v___y_1820_ = v___y_1892_;
v___y_1821_ = v___x_1897_;
v___y_1822_ = v___y_1893_;
v_h_x3f_1823_ = v___x_1905_;
v___y_1824_ = v___y_1894_;
v___y_1825_ = v___y_1895_;
goto v___jp_1815_;
}
}
else
{
lean_object* v___x_1906_; 
lean_dec(v___x_1900_);
v___x_1906_ = lean_box(0);
v___y_1816_ = v___y_1887_;
v___y_1817_ = v___y_1889_;
v___y_1818_ = v___y_1890_;
v___y_1819_ = v___y_1891_;
v___y_1820_ = v___y_1892_;
v___y_1821_ = v___x_1897_;
v___y_1822_ = v___y_1893_;
v_h_x3f_1823_ = v___x_1906_;
v___y_1824_ = v___y_1894_;
v___y_1825_ = v___y_1895_;
goto v___jp_1815_;
}
}
}
v___jp_1907_:
{
lean_object* v___x_1915_; lean_object* v_body_1916_; lean_object* v_decls_1917_; lean_object* v_decls_1918_; 
v___x_1915_ = lean_unsigned_to_nat(5u);
v_body_1916_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_1915_);
lean_dec(v_stx_1010_);
v_decls_1917_ = l_Lean_Syntax_getArgs(v___x_1263_);
lean_dec(v___x_1263_);
v_decls_1918_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_1917_);
lean_dec_ref(v_decls_1917_);
if (lean_obj_tag(v___y_1908_) == 1)
{
lean_object* v_val_1919_; lean_object* v___x_1920_; uint8_t v___x_1921_; 
v_val_1919_ = lean_ctor_get(v___y_1908_, 0);
v___x_1920_ = lean_array_get_size(v_decls_1918_);
v___x_1921_ = lean_nat_dec_lt(v___x_1262_, v___x_1920_);
if (v___x_1921_ == 0)
{
v___y_1887_ = v___y_1908_;
v___y_1888_ = v___y_1909_;
v___y_1889_ = v_body_1916_;
v___y_1890_ = v_decls_1918_;
v___y_1891_ = v_dec_1912_;
v___y_1892_ = v___y_1910_;
v___y_1893_ = v___y_1911_;
v___y_1894_ = v___y_1913_;
v___y_1895_ = v___y_1914_;
goto v___jp_1886_;
}
else
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1922_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__15));
v___x_1923_ = l_Lean_Macro_throwErrorAt___redArg(v_val_1919_, v___x_1922_, v___y_1913_, v___y_1914_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 1);
lean_inc(v_a_1924_);
lean_dec_ref_known(v___x_1923_, 2);
v___y_1887_ = v___y_1908_;
v___y_1888_ = v___y_1909_;
v___y_1889_ = v_body_1916_;
v___y_1890_ = v_decls_1918_;
v___y_1891_ = v_dec_1912_;
v___y_1892_ = v___y_1910_;
v___y_1893_ = v___y_1911_;
v___y_1894_ = v___y_1913_;
v___y_1895_ = v_a_1924_;
goto v___jp_1886_;
}
else
{
lean_object* v_a_1925_; lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
lean_dec_ref_known(v___y_1908_, 1);
lean_dec_ref(v_decls_1918_);
lean_dec(v_body_1916_);
lean_dec(v_dec_1912_);
lean_dec(v_tk_1261_);
v_a_1925_ = lean_ctor_get(v___x_1923_, 0);
v_a_1926_ = lean_ctor_get(v___x_1923_, 1);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1923_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_inc(v_a_1925_);
lean_dec(v___x_1923_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1925_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_a_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
}
else
{
v___y_1887_ = v___y_1908_;
v___y_1888_ = v___y_1909_;
v___y_1889_ = v_body_1916_;
v___y_1890_ = v_decls_1918_;
v___y_1891_ = v_dec_1912_;
v___y_1892_ = v___y_1910_;
v___y_1893_ = v___y_1911_;
v___y_1894_ = v___y_1913_;
v___y_1895_ = v___y_1914_;
goto v___jp_1886_;
}
}
v___jp_1934_:
{
lean_object* v___x_1941_; uint8_t v___x_1942_; 
v___x_1941_ = l_Lean_Syntax_getArg(v_stx_1010_, v___y_1936_);
v___x_1942_ = l_Lean_Syntax_isNone(v___x_1941_);
if (v___x_1942_ == 0)
{
uint8_t v___x_1943_; 
lean_inc(v___x_1941_);
v___x_1943_ = l_Lean_Syntax_matchesNull(v___x_1941_, v___x_1262_);
if (v___x_1943_ == 0)
{
lean_object* v___x_1944_; 
lean_dec(v___x_1941_);
lean_dec(v_inv_1938_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_1944_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1940_);
return v___x_1944_;
}
else
{
lean_object* v_dec_1945_; lean_object* v___x_1946_; uint8_t v___x_1947_; 
v_dec_1945_ = l_Lean_Syntax_getArg(v___x_1941_, v___x_1151_);
lean_dec(v___x_1941_);
v___x_1946_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v_dec_1945_);
v___x_1947_ = l_Lean_Syntax_isOfKind(v_dec_1945_, v___x_1946_);
if (v___x_1947_ == 0)
{
lean_object* v___x_1948_; 
lean_dec(v_dec_1945_);
lean_dec(v_inv_1938_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_1948_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1940_);
return v___x_1948_;
}
else
{
lean_object* v___x_1949_; 
v___x_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1949_, 0, v_dec_1945_);
v___y_1908_ = v_inv_1938_;
v___y_1909_ = v___y_1935_;
v___y_1910_ = v___y_1936_;
v___y_1911_ = v___y_1937_;
v_dec_1912_ = v___x_1949_;
v___y_1913_ = v___y_1939_;
v___y_1914_ = v___y_1940_;
goto v___jp_1907_;
}
}
}
else
{
lean_object* v___x_1950_; 
lean_dec(v___x_1941_);
v___x_1950_ = lean_box(0);
v___y_1908_ = v_inv_1938_;
v___y_1909_ = v___y_1935_;
v___y_1910_ = v___y_1936_;
v___y_1911_ = v___y_1937_;
v_dec_1912_ = v___x_1950_;
v___y_1913_ = v___y_1939_;
v___y_1914_ = v___y_1940_;
goto v___jp_1907_;
}
}
v___jp_1951_:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; uint8_t v___x_1956_; 
v___x_1954_ = l_Lean_Syntax_getArg(v___x_1456_, v___x_1262_);
lean_dec(v___x_1456_);
v___x_1955_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__21));
v___x_1956_ = l_Lean_Syntax_isOfKind(v___x_1954_, v___x_1955_);
if (v___x_1956_ == 0)
{
lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; 
v___x_1957_ = lean_unsigned_to_nat(2u);
v___x_1958_ = lean_unsigned_to_nat(3u);
v___x_1959_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_1957_);
v___x_1960_ = l_Lean_Syntax_isNone(v___x_1959_);
if (v___x_1960_ == 0)
{
uint8_t v___x_1961_; 
lean_inc(v___x_1959_);
v___x_1961_ = l_Lean_Syntax_matchesNull(v___x_1959_, v___x_1262_);
if (v___x_1961_ == 0)
{
lean_object* v___x_1962_; 
lean_dec(v___x_1959_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_1962_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1953_);
return v___x_1962_;
}
else
{
lean_object* v_inv_1963_; lean_object* v___x_1964_; uint8_t v___x_1965_; 
v_inv_1963_ = l_Lean_Syntax_getArg(v___x_1959_, v___x_1151_);
lean_dec(v___x_1959_);
v___x_1964_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__19));
lean_inc(v_inv_1963_);
v___x_1965_ = l_Lean_Syntax_isOfKind(v_inv_1963_, v___x_1964_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1966_; 
lean_dec(v_inv_1963_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_1966_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1953_);
return v___x_1966_;
}
else
{
lean_object* v___x_1967_; 
v___x_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1967_, 0, v_inv_1963_);
v___y_1935_ = v___x_1957_;
v___y_1936_ = v___x_1958_;
v___y_1937_ = v___x_1956_;
v_inv_1938_ = v___x_1967_;
v___y_1939_ = v___y_1952_;
v___y_1940_ = v___y_1953_;
goto v___jp_1934_;
}
}
}
else
{
lean_object* v___x_1968_; 
lean_dec(v___x_1959_);
v___x_1968_ = lean_box(0);
v___y_1935_ = v___x_1957_;
v___y_1936_ = v___x_1958_;
v___y_1937_ = v___x_1956_;
v_inv_1938_ = v___x_1968_;
v___y_1939_ = v___y_1952_;
v___y_1940_ = v___y_1953_;
goto v___jp_1934_;
}
}
else
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; uint8_t v___x_1972_; 
v___x_1969_ = lean_unsigned_to_nat(2u);
v___x_1970_ = lean_unsigned_to_nat(3u);
v___x_1971_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_1969_);
v___x_1972_ = l_Lean_Syntax_isNone(v___x_1971_);
if (v___x_1972_ == 0)
{
uint8_t v___x_1973_; 
lean_inc(v___x_1971_);
v___x_1973_ = l_Lean_Syntax_matchesNull(v___x_1971_, v___x_1262_);
if (v___x_1973_ == 0)
{
lean_object* v___x_1974_; 
lean_dec(v___x_1971_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_1974_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1953_);
return v___x_1974_;
}
else
{
lean_object* v_inv_1975_; lean_object* v___x_1976_; uint8_t v___x_1977_; 
v_inv_1975_ = l_Lean_Syntax_getArg(v___x_1971_, v___x_1151_);
v___x_1976_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__19));
lean_inc(v_inv_1975_);
v___x_1977_ = l_Lean_Syntax_isOfKind(v_inv_1975_, v___x_1976_);
if (v___x_1977_ == 0)
{
lean_dec(v___x_1971_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; 
lean_dec(v_inv_1975_);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_1978_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1953_);
return v___x_1978_;
}
else
{
lean_object* v___x_1979_; lean_object* v___x_1980_; uint8_t v___x_1981_; 
v___x_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1979_, 0, v_inv_1975_);
v___x_1980_ = l_Lean_Syntax_getArg(v_stx_1010_, v___x_1970_);
v___x_1981_ = l_Lean_Syntax_isNone(v___x_1980_);
if (v___x_1981_ == 0)
{
uint8_t v___x_1982_; 
lean_inc(v___x_1980_);
v___x_1982_ = l_Lean_Syntax_matchesNull(v___x_1980_, v___x_1262_);
if (v___x_1982_ == 0)
{
lean_object* v___x_1983_; 
lean_dec(v___x_1980_);
lean_dec_ref_known(v___x_1979_, 1);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_1983_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1953_);
return v___x_1983_;
}
else
{
lean_object* v_dec_1984_; lean_object* v___x_1985_; uint8_t v___x_1986_; 
v_dec_1984_ = l_Lean_Syntax_getArg(v___x_1980_, v___x_1151_);
lean_dec(v___x_1980_);
v___x_1985_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v_dec_1984_);
v___x_1986_ = l_Lean_Syntax_isOfKind(v_dec_1984_, v___x_1985_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1987_; 
lean_dec(v_dec_1984_);
lean_dec_ref_known(v___x_1979_, 1);
lean_dec(v___x_1263_);
lean_dec(v_tk_1261_);
lean_dec(v_stx_1010_);
v___x_1987_ = l_Lean_Macro_throwUnsupported___redArg(v___y_1953_);
return v___x_1987_;
}
else
{
lean_object* v___x_1988_; 
v___x_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1988_, 0, v_dec_1984_);
v___y_1736_ = v___x_1979_;
v___y_1737_ = v___x_1969_;
v___y_1738_ = v___x_1970_;
v_dec_1739_ = v___x_1988_;
v___y_1740_ = v___y_1952_;
v___y_1741_ = v___y_1953_;
goto v___jp_1735_;
}
}
}
else
{
lean_object* v___x_1989_; 
lean_dec(v___x_1980_);
v___x_1989_ = lean_box(0);
v___y_1736_ = v___x_1979_;
v___y_1737_ = v___x_1969_;
v___y_1738_ = v___x_1970_;
v_dec_1739_ = v___x_1989_;
v___y_1740_ = v___y_1952_;
v___y_1741_ = v___y_1953_;
goto v___jp_1735_;
}
}
}
else
{
lean_dec(v_inv_1975_);
v___y_1700_ = v___x_1971_;
v___y_1701_ = v___x_1969_;
v___y_1702_ = v___x_1970_;
v___y_1703_ = v___y_1952_;
v___y_1704_ = v___y_1953_;
goto v___jp_1699_;
}
}
}
else
{
v___y_1700_ = v___x_1971_;
v___y_1701_ = v___x_1969_;
v___y_1702_ = v___x_1970_;
v___y_1703_ = v___y_1952_;
v___y_1704_ = v___y_1953_;
goto v___jp_1699_;
}
}
}
v___jp_1990_:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
lean_inc_ref(v___y_2000_);
v___x_2004_ = l_Array_append___redArg(v___y_2000_, v___y_2003_);
lean_dec_ref(v___y_2003_);
lean_inc_n(v___y_1993_, 2);
lean_inc_n(v___y_1995_, 4);
v___x_2005_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2005_, 0, v___y_1995_);
lean_ctor_set(v___x_2005_, 1, v___y_1993_);
lean_ctor_set(v___x_2005_, 2, v___x_2004_);
v___x_2006_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_2007_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___y_1995_);
lean_ctor_set(v___x_2007_, 1, v___x_2006_);
v___x_2008_ = l_Lean_Syntax_node4(v___y_1995_, v___x_1457_, v___x_2005_, v___y_2002_, v___x_2007_, v___y_1992_);
v___x_2009_ = l_Lean_Syntax_node1(v___y_1995_, v___y_1993_, v___x_2008_);
if (lean_obj_tag(v___y_1998_) == 1)
{
lean_object* v_val_2010_; lean_object* v___x_2011_; 
v_val_2010_ = lean_ctor_get(v___y_1998_, 0);
lean_inc(v_val_2010_);
lean_dec_ref_known(v___y_1998_, 1);
v___x_2011_ = l_Array_mkArray1___redArg(v_val_2010_);
v___y_1153_ = v___y_1991_;
v___y_1154_ = v___x_2009_;
v___y_1155_ = v___y_1993_;
v___y_1156_ = v___y_1994_;
v___y_1157_ = v___y_1995_;
v___y_1158_ = v___y_1996_;
v___y_1159_ = v___y_1997_;
v___y_1160_ = v___y_1999_;
v___y_1161_ = v___y_2000_;
v___y_1162_ = v___y_2001_;
v___y_1163_ = v___x_2011_;
goto v___jp_1152_;
}
else
{
lean_object* v___x_2012_; 
lean_dec(v___y_1998_);
v___x_2012_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___y_1153_ = v___y_1991_;
v___y_1154_ = v___x_2009_;
v___y_1155_ = v___y_1993_;
v___y_1156_ = v___y_1994_;
v___y_1157_ = v___y_1995_;
v___y_1158_ = v___y_1996_;
v___y_1159_ = v___y_1997_;
v___y_1160_ = v___y_1999_;
v___y_1161_ = v___y_2000_;
v___y_1162_ = v___y_2001_;
v___y_1163_ = v___x_2012_;
goto v___jp_1152_;
}
}
v___jp_2014_:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2025_ = lean_array_get_size(v___y_2017_);
v___x_2026_ = l_Array_toSubarray___redArg(v___y_2017_, v___x_1262_, v___x_2025_);
lean_inc_ref(v___y_2020_);
v___x_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2027_, 0, v___y_2020_);
lean_ctor_set(v___x_2027_, 1, v_body_2022_);
v___x_2028_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_2013_, v___x_2026_, v___x_2027_, v___y_2023_, v___y_2024_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v_a_2029_; lean_object* v_a_2030_; lean_object* v_fst_2031_; lean_object* v_snd_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2051_; 
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
lean_inc(v_a_2029_);
v_a_2030_ = lean_ctor_get(v___x_2028_, 1);
lean_inc(v_a_2030_);
lean_dec_ref_known(v___x_2028_, 2);
v_fst_2031_ = lean_ctor_get(v_a_2029_, 0);
v_snd_2032_ = lean_ctor_get(v_a_2029_, 1);
v_isSharedCheck_2051_ = !lean_is_exclusive(v_a_2029_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2034_ = v_a_2029_;
v_isShared_2035_ = v_isSharedCheck_2051_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_snd_2032_);
lean_inc(v_fst_2031_);
lean_dec(v_a_2029_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2051_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v_ref_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2042_; 
v_ref_2036_ = lean_ctor_get(v___y_2023_, 5);
v___x_2037_ = l_Lean_SourceInfo_fromRef(v_ref_2036_, v___x_2013_);
v___x_2038_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
v___x_2039_ = l_Lean_SourceInfo_fromRef(v_tk_1261_, v___x_1149_);
lean_dec(v_tk_1261_);
v___x_2040_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
if (v_isShared_2035_ == 0)
{
lean_ctor_set_tag(v___x_2034_, 2);
lean_ctor_set(v___x_2034_, 1, v___x_2040_);
lean_ctor_set(v___x_2034_, 0, v___x_2039_);
v___x_2042_ = v___x_2034_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2039_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2043_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_2044_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
if (lean_obj_tag(v___y_2018_) == 1)
{
lean_object* v_val_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
v_val_2045_ = lean_ctor_get(v___y_2018_, 0);
lean_inc(v_val_2045_);
lean_dec_ref_known(v___y_2018_, 1);
v___x_2046_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
lean_inc(v___x_2037_);
v___x_2047_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2037_);
lean_ctor_set(v___x_2047_, 1, v___x_2046_);
v___x_2048_ = l_Array_mkArray2___redArg(v_val_2045_, v___x_2047_);
v___y_1991_ = v___y_2015_;
v___y_1992_ = v___y_2016_;
v___y_1993_ = v___x_2043_;
v___y_1994_ = v_a_2030_;
v___y_1995_ = v___x_2037_;
v___y_1996_ = v_snd_2032_;
v___y_1997_ = v___x_2038_;
v___y_1998_ = v___y_2019_;
v___y_1999_ = v_fst_2031_;
v___y_2000_ = v___x_2044_;
v___y_2001_ = v___x_2042_;
v___y_2002_ = v_x_2021_;
v___y_2003_ = v___x_2048_;
goto v___jp_1990_;
}
else
{
lean_object* v___x_2049_; 
lean_dec(v___y_2018_);
v___x_2049_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___y_1991_ = v___y_2015_;
v___y_1992_ = v___y_2016_;
v___y_1993_ = v___x_2043_;
v___y_1994_ = v_a_2030_;
v___y_1995_ = v___x_2037_;
v___y_1996_ = v_snd_2032_;
v___y_1997_ = v___x_2038_;
v___y_1998_ = v___y_2019_;
v___y_1999_ = v_fst_2031_;
v___y_2000_ = v___x_2044_;
v___y_2001_ = v___x_2042_;
v___y_2002_ = v_x_2021_;
v___y_2003_ = v___x_2049_;
goto v___jp_1990_;
}
}
}
}
else
{
lean_object* v_a_2052_; lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec(v_x_2021_);
lean_dec(v___y_2019_);
lean_dec(v___y_2018_);
lean_dec(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec(v_tk_1261_);
v_a_2052_ = lean_ctor_get(v___x_2028_, 0);
v_a_2053_ = lean_ctor_get(v___x_2028_, 1);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2028_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_inc(v_a_2052_);
lean_dec(v___x_2028_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2052_);
lean_ctor_set(v_reuseFailAlloc_2059_, 1, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
v___jp_2061_:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v_doElems_2073_; uint8_t v___x_2074_; 
v___x_2071_ = l_Lean_Syntax_getArg(v___y_2066_, v___x_1262_);
v___x_2072_ = l_Lean_Syntax_getArg(v___y_2066_, v___y_2065_);
lean_dec(v___y_2066_);
v_doElems_2073_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_2074_ = l_Lean_Syntax_isIdent(v___x_2071_);
if (v___x_2074_ == 0)
{
lean_object* v___x_2075_; uint8_t v___x_2076_; 
v___x_2075_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_2071_);
v___x_2076_ = l_Lean_Syntax_isOfKind(v___x_2071_, v___x_2075_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; 
v___x_2077_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_2071_, v___x_2076_, v___y_2069_, v___y_2070_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; lean_object* v_a_2079_; lean_object* v_ref_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc_n(v_a_2078_, 2);
v_a_2079_ = lean_ctor_get(v___x_2077_, 1);
lean_inc(v_a_2079_);
lean_dec_ref_known(v___x_2077_, 2);
v_ref_2080_ = lean_ctor_get(v___y_2069_, 5);
v___x_2081_ = l_Lean_SourceInfo_fromRef(v_ref_2080_, v___x_2076_);
v___x_2082_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_2083_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_2084_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
v___x_2085_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_2086_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_n(v___x_2081_, 15);
v___x_2087_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2081_);
lean_ctor_set(v___x_2087_, 1, v___x_2086_);
v___x_2088_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_2089_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2081_);
lean_ctor_set(v___x_2089_, 1, v___x_2083_);
lean_ctor_set(v___x_2089_, 2, v___x_2088_);
v___x_2090_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_2089_, 4);
v___x_2091_ = l_Lean_Syntax_node2(v___x_2081_, v___x_2090_, v___x_2089_, v_a_2078_);
v___x_2092_ = l_Lean_Syntax_node1(v___x_2081_, v___x_2083_, v___x_2091_);
v___x_2093_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_2094_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2081_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
v___x_2095_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_2096_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_2097_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_2098_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2081_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
v___x_2099_ = l_Lean_Syntax_node1(v___x_2081_, v___x_2083_, v___x_2071_);
v___x_2100_ = l_Lean_Syntax_node1(v___x_2081_, v___x_2083_, v___x_2099_);
v___x_2101_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_2102_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2081_);
lean_ctor_set(v___x_2102_, 1, v___x_2101_);
v___x_2103_ = l_Lean_Syntax_node4(v___x_2081_, v___x_2096_, v___x_2098_, v___x_2100_, v___x_2102_, v___y_2063_);
v___x_2104_ = l_Lean_Syntax_node1(v___x_2081_, v___x_2083_, v___x_2103_);
v___x_2105_ = l_Lean_Syntax_node1(v___x_2081_, v___x_2095_, v___x_2104_);
v___x_2106_ = l_Lean_Syntax_node7(v___x_2081_, v___x_2085_, v___x_2087_, v___x_2089_, v___x_2089_, v___x_2089_, v___x_2092_, v___x_2094_, v___x_2105_);
v___x_2107_ = l_Lean_Syntax_node2(v___x_2081_, v___x_2084_, v___x_2106_, v___x_2089_);
v___x_2108_ = l_Lean_Syntax_node1(v___x_2081_, v___x_2083_, v___x_2107_);
v___x_2109_ = l_Lean_Syntax_node1(v___x_2081_, v___x_2082_, v___x_2108_);
v___y_2015_ = v___y_2062_;
v___y_2016_ = v___x_2072_;
v___y_2017_ = v___y_2064_;
v___y_2018_ = v_h_x3f_2068_;
v___y_2019_ = v___y_2067_;
v___y_2020_ = v_doElems_2073_;
v_x_2021_ = v_a_2078_;
v_body_2022_ = v___x_2109_;
v___y_2023_ = v___y_2069_;
v___y_2024_ = v_a_2079_;
goto v___jp_2014_;
}
else
{
lean_object* v_a_2110_; lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
lean_dec(v___x_2072_);
lean_dec(v___x_2071_);
lean_dec(v_h_x3f_2068_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec(v___y_2062_);
lean_dec(v_tk_1261_);
v_a_2110_ = lean_ctor_get(v___x_2077_, 0);
v_a_2111_ = lean_ctor_get(v___x_2077_, 1);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2077_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_inc(v_a_2110_);
lean_dec(v___x_2077_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2110_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
else
{
lean_object* v___x_2119_; 
v___x_2119_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_2071_, v___x_2074_, v___y_2069_, v___y_2070_);
lean_dec(v___x_2071_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; lean_object* v_a_2121_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_a_2120_);
v_a_2121_ = lean_ctor_get(v___x_2119_, 1);
lean_inc(v_a_2121_);
lean_dec_ref_known(v___x_2119_, 2);
v___y_2015_ = v___y_2062_;
v___y_2016_ = v___x_2072_;
v___y_2017_ = v___y_2064_;
v___y_2018_ = v_h_x3f_2068_;
v___y_2019_ = v___y_2067_;
v___y_2020_ = v_doElems_2073_;
v_x_2021_ = v_a_2120_;
v_body_2022_ = v___y_2063_;
v___y_2023_ = v___y_2069_;
v___y_2024_ = v_a_2121_;
goto v___jp_2014_;
}
else
{
lean_object* v_a_2122_; lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2130_; 
lean_dec(v___x_2072_);
lean_dec(v_h_x3f_2068_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec(v___y_2062_);
lean_dec(v_tk_1261_);
v_a_2122_ = lean_ctor_get(v___x_2119_, 0);
v_a_2123_ = lean_ctor_get(v___x_2119_, 1);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2125_ = v___x_2119_;
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_inc(v_a_2122_);
lean_dec(v___x_2119_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2128_; 
if (v_isShared_2126_ == 0)
{
v___x_2128_ = v___x_2125_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_a_2122_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v_a_2123_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
}
else
{
v___y_2015_ = v___y_2062_;
v___y_2016_ = v___x_2072_;
v___y_2017_ = v___y_2064_;
v___y_2018_ = v_h_x3f_2068_;
v___y_2019_ = v___y_2067_;
v___y_2020_ = v_doElems_2073_;
v_x_2021_ = v___x_2071_;
v_body_2022_ = v___y_2063_;
v___y_2023_ = v___y_2069_;
v___y_2024_ = v___y_2070_;
goto v___jp_2014_;
}
}
}
v___jp_1152_:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
lean_inc_ref(v___y_1161_);
v___x_1164_ = l_Array_append___redArg(v___y_1161_, v___y_1163_);
lean_dec_ref(v___y_1163_);
lean_inc(v___y_1155_);
lean_inc(v___y_1157_);
v___x_1165_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1165_, 0, v___y_1157_);
lean_ctor_set(v___x_1165_, 1, v___y_1155_);
lean_ctor_set(v___x_1165_, 2, v___x_1164_);
if (lean_obj_tag(v___y_1153_) == 1)
{
lean_object* v_val_1166_; lean_object* v___x_1167_; 
v_val_1166_ = lean_ctor_get(v___y_1153_, 0);
lean_inc(v_val_1166_);
lean_dec_ref_known(v___y_1153_, 1);
v___x_1167_ = l_Array_mkArray1___redArg(v_val_1166_);
v___y_1123_ = v___y_1154_;
v___y_1124_ = v___y_1155_;
v___y_1125_ = v___y_1156_;
v___y_1126_ = v___y_1157_;
v___y_1127_ = v___y_1158_;
v___y_1128_ = v___y_1159_;
v___y_1129_ = v___y_1160_;
v___y_1130_ = v___y_1161_;
v___y_1131_ = v___y_1162_;
v___y_1132_ = v___x_1165_;
v___y_1133_ = v___x_1167_;
goto v___jp_1122_;
}
else
{
lean_object* v___x_1168_; 
lean_dec(v___y_1153_);
v___x_1168_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___y_1123_ = v___y_1154_;
v___y_1124_ = v___y_1155_;
v___y_1125_ = v___y_1156_;
v___y_1126_ = v___y_1157_;
v___y_1127_ = v___y_1158_;
v___y_1128_ = v___y_1159_;
v___y_1129_ = v___y_1160_;
v___y_1130_ = v___y_1161_;
v___y_1131_ = v___y_1162_;
v___y_1132_ = v___x_1165_;
v___y_1133_ = v___x_1168_;
goto v___jp_1122_;
}
}
v___jp_1169_:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
lean_inc_ref(v___y_1173_);
v___x_1181_ = l_Array_append___redArg(v___y_1173_, v___y_1180_);
lean_dec_ref(v___y_1180_);
lean_inc(v___y_1172_);
lean_inc(v___y_1171_);
v___x_1182_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1182_, 0, v___y_1171_);
lean_ctor_set(v___x_1182_, 1, v___y_1172_);
lean_ctor_set(v___x_1182_, 2, v___x_1181_);
if (lean_obj_tag(v___y_1176_) == 1)
{
lean_object* v_val_1183_; lean_object* v___x_1184_; 
v_val_1183_ = lean_ctor_get(v___y_1176_, 0);
lean_inc(v_val_1183_);
lean_dec_ref_known(v___y_1176_, 1);
v___x_1184_ = l_Array_mkArray1___redArg(v_val_1183_);
v___y_1096_ = v___y_1170_;
v___y_1097_ = v___x_1182_;
v___y_1098_ = v___y_1171_;
v___y_1099_ = v___y_1172_;
v___y_1100_ = v___y_1173_;
v___y_1101_ = v___y_1174_;
v___y_1102_ = v___y_1175_;
v___y_1103_ = v___y_1177_;
v___y_1104_ = v___y_1178_;
v___y_1105_ = v___y_1179_;
v___y_1106_ = v___x_1184_;
goto v___jp_1095_;
}
else
{
lean_object* v___x_1185_; 
lean_dec(v___y_1176_);
v___x_1185_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___y_1096_ = v___y_1170_;
v___y_1097_ = v___x_1182_;
v___y_1098_ = v___y_1171_;
v___y_1099_ = v___y_1172_;
v___y_1100_ = v___y_1173_;
v___y_1101_ = v___y_1174_;
v___y_1102_ = v___y_1175_;
v___y_1103_ = v___y_1177_;
v___y_1104_ = v___y_1178_;
v___y_1105_ = v___y_1179_;
v___y_1106_ = v___x_1185_;
goto v___jp_1095_;
}
}
v___jp_1186_:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_inc_ref(v___y_1190_);
v___x_1201_ = l_Array_append___redArg(v___y_1190_, v___y_1200_);
lean_dec_ref(v___y_1200_);
lean_inc_n(v___y_1195_, 2);
lean_inc_n(v___y_1194_, 4);
v___x_1202_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1202_, 0, v___y_1194_);
lean_ctor_set(v___x_1202_, 1, v___y_1195_);
lean_ctor_set(v___x_1202_, 2, v___x_1201_);
v___x_1203_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_1204_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___y_1194_);
lean_ctor_set(v___x_1204_, 1, v___x_1203_);
lean_inc(v___y_1193_);
v___x_1205_ = l_Lean_Syntax_node4(v___y_1194_, v___y_1193_, v___x_1202_, v___y_1189_, v___x_1204_, v___y_1196_);
v___x_1206_ = l_Lean_Syntax_node1(v___y_1194_, v___y_1195_, v___x_1205_);
if (lean_obj_tag(v___y_1188_) == 1)
{
lean_object* v_val_1207_; lean_object* v___x_1208_; 
v_val_1207_ = lean_ctor_get(v___y_1188_, 0);
lean_inc(v_val_1207_);
lean_dec_ref_known(v___y_1188_, 1);
v___x_1208_ = l_Array_mkArray1___redArg(v_val_1207_);
v___y_1170_ = v___y_1187_;
v___y_1171_ = v___y_1194_;
v___y_1172_ = v___y_1195_;
v___y_1173_ = v___y_1190_;
v___y_1174_ = v___y_1197_;
v___y_1175_ = v___y_1191_;
v___y_1176_ = v___y_1192_;
v___y_1177_ = v___y_1198_;
v___y_1178_ = v___x_1206_;
v___y_1179_ = v___y_1199_;
v___y_1180_ = v___x_1208_;
goto v___jp_1169_;
}
else
{
lean_object* v___x_1209_; 
lean_dec(v___y_1188_);
v___x_1209_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___y_1170_ = v___y_1187_;
v___y_1171_ = v___y_1194_;
v___y_1172_ = v___y_1195_;
v___y_1173_ = v___y_1190_;
v___y_1174_ = v___y_1197_;
v___y_1175_ = v___y_1191_;
v___y_1176_ = v___y_1192_;
v___y_1177_ = v___y_1198_;
v___y_1178_ = v___x_1206_;
v___y_1179_ = v___y_1199_;
v___y_1180_ = v___x_1209_;
goto v___jp_1169_;
}
}
v___jp_1210_:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
lean_inc_ref(v___y_1218_);
v___x_1222_ = l_Array_append___redArg(v___y_1218_, v___y_1221_);
lean_dec_ref(v___y_1221_);
lean_inc(v___y_1212_);
lean_inc(v___y_1220_);
v___x_1223_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1223_, 0, v___y_1220_);
lean_ctor_set(v___x_1223_, 1, v___y_1212_);
lean_ctor_set(v___x_1223_, 2, v___x_1222_);
if (lean_obj_tag(v___y_1211_) == 1)
{
lean_object* v_val_1224_; lean_object* v___x_1225_; 
v_val_1224_ = lean_ctor_get(v___y_1211_, 0);
lean_inc(v_val_1224_);
lean_dec_ref_known(v___y_1211_, 1);
v___x_1225_ = l_Array_mkArray1___redArg(v_val_1224_);
v___y_1042_ = v___y_1212_;
v___y_1043_ = v___y_1213_;
v___y_1044_ = v___y_1214_;
v___y_1045_ = v___y_1215_;
v___y_1046_ = v___y_1216_;
v___y_1047_ = v___y_1217_;
v___y_1048_ = v___y_1218_;
v___y_1049_ = v___x_1223_;
v___y_1050_ = v___y_1219_;
v___y_1051_ = v___y_1220_;
v___y_1052_ = v___x_1225_;
goto v___jp_1041_;
}
else
{
lean_object* v___x_1226_; 
lean_dec(v___y_1211_);
v___x_1226_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___y_1042_ = v___y_1212_;
v___y_1043_ = v___y_1213_;
v___y_1044_ = v___y_1214_;
v___y_1045_ = v___y_1215_;
v___y_1046_ = v___y_1216_;
v___y_1047_ = v___y_1217_;
v___y_1048_ = v___y_1218_;
v___y_1049_ = v___x_1223_;
v___y_1050_ = v___y_1219_;
v___y_1051_ = v___y_1220_;
v___y_1052_ = v___x_1226_;
goto v___jp_1041_;
}
}
v___jp_1227_:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
lean_inc_ref(v___y_1232_);
v___x_1239_ = l_Array_append___redArg(v___y_1232_, v___y_1238_);
lean_dec_ref(v___y_1238_);
lean_inc(v___y_1231_);
lean_inc(v___y_1230_);
v___x_1240_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1240_, 0, v___y_1230_);
lean_ctor_set(v___x_1240_, 1, v___y_1231_);
lean_ctor_set(v___x_1240_, 2, v___x_1239_);
if (lean_obj_tag(v___y_1237_) == 1)
{
lean_object* v_val_1241_; lean_object* v___x_1242_; 
v_val_1241_ = lean_ctor_get(v___y_1237_, 0);
lean_inc(v_val_1241_);
lean_dec_ref_known(v___y_1237_, 1);
v___x_1242_ = l_Array_mkArray1___redArg(v_val_1241_);
v___y_1069_ = v___y_1229_;
v___y_1070_ = v___y_1228_;
v___y_1071_ = v___y_1230_;
v___y_1072_ = v___x_1240_;
v___y_1073_ = v___y_1231_;
v___y_1074_ = v___y_1232_;
v___y_1075_ = v___y_1233_;
v___y_1076_ = v___y_1235_;
v___y_1077_ = v___y_1234_;
v___y_1078_ = v___y_1236_;
v___y_1079_ = v___x_1242_;
goto v___jp_1068_;
}
else
{
lean_object* v___x_1243_; 
lean_dec(v___y_1237_);
v___x_1243_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___y_1069_ = v___y_1229_;
v___y_1070_ = v___y_1228_;
v___y_1071_ = v___y_1230_;
v___y_1072_ = v___x_1240_;
v___y_1073_ = v___y_1231_;
v___y_1074_ = v___y_1232_;
v___y_1075_ = v___y_1233_;
v___y_1076_ = v___y_1235_;
v___y_1077_ = v___y_1234_;
v___y_1078_ = v___y_1236_;
v___y_1079_ = v___x_1243_;
goto v___jp_1068_;
}
}
v___jp_1244_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
lean_inc_ref(v___y_1251_);
v___x_1256_ = l_Array_append___redArg(v___y_1251_, v___y_1255_);
lean_dec_ref(v___y_1255_);
lean_inc(v___y_1245_);
lean_inc(v___y_1250_);
v___x_1257_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1257_, 0, v___y_1250_);
lean_ctor_set(v___x_1257_, 1, v___y_1245_);
lean_ctor_set(v___x_1257_, 2, v___x_1256_);
if (lean_obj_tag(v___y_1248_) == 1)
{
lean_object* v_val_1258_; lean_object* v___x_1259_; 
v_val_1258_ = lean_ctor_get(v___y_1248_, 0);
lean_inc(v_val_1258_);
lean_dec_ref_known(v___y_1248_, 1);
v___x_1259_ = l_Array_mkArray1___redArg(v_val_1258_);
v___y_1015_ = v___x_1257_;
v___y_1016_ = v___y_1245_;
v___y_1017_ = v___y_1247_;
v___y_1018_ = v___y_1246_;
v___y_1019_ = v___y_1249_;
v___y_1020_ = v___y_1250_;
v___y_1021_ = v___y_1251_;
v___y_1022_ = v___y_1252_;
v___y_1023_ = v___y_1253_;
v___y_1024_ = v___y_1254_;
v___y_1025_ = v___x_1259_;
goto v___jp_1014_;
}
else
{
lean_object* v___x_1260_; 
lean_dec(v___y_1248_);
v___x_1260_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___y_1015_ = v___x_1257_;
v___y_1016_ = v___y_1245_;
v___y_1017_ = v___y_1247_;
v___y_1018_ = v___y_1246_;
v___y_1019_ = v___y_1249_;
v___y_1020_ = v___y_1250_;
v___y_1021_ = v___y_1251_;
v___y_1022_ = v___y_1252_;
v___y_1023_ = v___y_1253_;
v___y_1024_ = v___y_1254_;
v___y_1025_ = v___x_1260_;
goto v___jp_1014_;
}
}
v___jp_1265_:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1277_ = lean_array_get_size(v___y_1271_);
v___x_1278_ = l_Array_toSubarray___redArg(v___y_1271_, v___x_1262_, v___x_1277_);
lean_inc_ref(v___y_1268_);
v___x_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___y_1268_);
lean_ctor_set(v___x_1279_, 1, v_body_1274_);
v___x_1280_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_1264_, v___x_1278_, v___x_1279_, v___y_1275_, v___y_1276_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v_a_1282_; lean_object* v_fst_1283_; lean_object* v_snd_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1303_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1281_);
v_a_1282_ = lean_ctor_get(v___x_1280_, 1);
lean_inc(v_a_1282_);
lean_dec_ref_known(v___x_1280_, 2);
v_fst_1283_ = lean_ctor_get(v_a_1281_, 0);
v_snd_1284_ = lean_ctor_get(v_a_1281_, 1);
v_isSharedCheck_1303_ = !lean_is_exclusive(v_a_1281_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1286_ = v_a_1281_;
v_isShared_1287_ = v_isSharedCheck_1303_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_snd_1284_);
lean_inc(v_fst_1283_);
lean_dec(v_a_1281_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1303_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v_ref_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1294_; 
v_ref_1288_ = lean_ctor_get(v___y_1275_, 5);
v___x_1289_ = l_Lean_SourceInfo_fromRef(v_ref_1288_, v___x_1264_);
v___x_1290_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
v___x_1291_ = l_Lean_SourceInfo_fromRef(v_tk_1261_, v___x_1149_);
lean_dec(v_tk_1261_);
v___x_1292_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__7));
if (v_isShared_1287_ == 0)
{
lean_ctor_set_tag(v___x_1286_, 2);
lean_ctor_set(v___x_1286_, 1, v___x_1292_);
lean_ctor_set(v___x_1286_, 0, v___x_1291_);
v___x_1294_ = v___x_1286_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1291_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v___x_1292_);
v___x_1294_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1296_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
if (lean_obj_tag(v___y_1267_) == 1)
{
lean_object* v_val_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v_val_1297_ = lean_ctor_get(v___y_1267_, 0);
lean_inc(v_val_1297_);
lean_dec_ref_known(v___y_1267_, 1);
v___x_1298_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
lean_inc(v___x_1289_);
v___x_1299_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1289_);
lean_ctor_set(v___x_1299_, 1, v___x_1298_);
v___x_1300_ = l_Array_mkArray2___redArg(v_val_1297_, v___x_1299_);
v___y_1187_ = v_fst_1283_;
v___y_1188_ = v___y_1266_;
v___y_1189_ = v_x_1273_;
v___y_1190_ = v___x_1296_;
v___y_1191_ = v_snd_1284_;
v___y_1192_ = v___y_1272_;
v___y_1193_ = v___y_1269_;
v___y_1194_ = v___x_1289_;
v___y_1195_ = v___x_1295_;
v___y_1196_ = v___y_1270_;
v___y_1197_ = v___x_1290_;
v___y_1198_ = v___x_1294_;
v___y_1199_ = v_a_1282_;
v___y_1200_ = v___x_1300_;
goto v___jp_1186_;
}
else
{
lean_object* v___x_1301_; 
lean_dec(v___y_1267_);
v___x_1301_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__4));
v___y_1187_ = v_fst_1283_;
v___y_1188_ = v___y_1266_;
v___y_1189_ = v_x_1273_;
v___y_1190_ = v___x_1296_;
v___y_1191_ = v_snd_1284_;
v___y_1192_ = v___y_1272_;
v___y_1193_ = v___y_1269_;
v___y_1194_ = v___x_1289_;
v___y_1195_ = v___x_1295_;
v___y_1196_ = v___y_1270_;
v___y_1197_ = v___x_1290_;
v___y_1198_ = v___x_1294_;
v___y_1199_ = v_a_1282_;
v___y_1200_ = v___x_1301_;
goto v___jp_1186_;
}
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1312_; 
lean_dec(v_x_1273_);
lean_dec(v___y_1272_);
lean_dec(v___y_1270_);
lean_dec(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec(v_tk_1261_);
v_a_1304_ = lean_ctor_get(v___x_1280_, 0);
v_a_1305_ = lean_ctor_get(v___x_1280_, 1);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1307_ = v___x_1280_;
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_inc(v_a_1304_);
lean_dec(v___x_1280_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1304_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v_a_1305_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
v___jp_1313_:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v_doElems_1326_; uint8_t v___x_1327_; 
v___x_1324_ = l_Lean_Syntax_getArg(v___y_1319_, v___x_1262_);
v___x_1325_ = l_Lean_Syntax_getArg(v___y_1319_, v___y_1320_);
lean_dec(v___y_1319_);
v_doElems_1326_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_1327_ = l_Lean_Syntax_isIdent(v___x_1324_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; uint8_t v___x_1329_; 
v___x_1328_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_1324_);
v___x_1329_ = l_Lean_Syntax_isOfKind(v___x_1324_, v___x_1328_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1324_, v___x_1329_, v___y_1322_, v___y_1323_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; lean_object* v_a_1332_; lean_object* v_ref_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc_n(v_a_1331_, 2);
v_a_1332_ = lean_ctor_get(v___x_1330_, 1);
lean_inc(v_a_1332_);
lean_dec_ref_known(v___x_1330_, 2);
v_ref_1333_ = lean_ctor_get(v___y_1322_, 5);
v___x_1334_ = l_Lean_SourceInfo_fromRef(v_ref_1333_, v___x_1329_);
v___x_1335_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_1336_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_1337_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__6));
v___x_1338_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__11));
v___x_1339_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
lean_inc_n(v___x_1334_, 15);
v___x_1340_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1334_);
lean_ctor_set(v___x_1340_, 1, v___x_1339_);
v___x_1341_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_1342_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1334_);
lean_ctor_set(v___x_1342_, 1, v___x_1336_);
lean_ctor_set(v___x_1342_, 2, v___x_1341_);
v___x_1343_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc_ref_n(v___x_1342_, 4);
v___x_1344_ = l_Lean_Syntax_node2(v___x_1334_, v___x_1343_, v___x_1342_, v_a_1331_);
v___x_1345_ = l_Lean_Syntax_node1(v___x_1334_, v___x_1336_, v___x_1344_);
v___x_1346_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_1347_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1334_);
lean_ctor_set(v___x_1347_, 1, v___x_1346_);
v___x_1348_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_1349_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_1350_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_1351_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1334_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
v___x_1352_ = l_Lean_Syntax_node1(v___x_1334_, v___x_1336_, v___x_1324_);
v___x_1353_ = l_Lean_Syntax_node1(v___x_1334_, v___x_1336_, v___x_1352_);
v___x_1354_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_1355_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1334_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = l_Lean_Syntax_node4(v___x_1334_, v___x_1349_, v___x_1351_, v___x_1353_, v___x_1355_, v___y_1314_);
v___x_1357_ = l_Lean_Syntax_node1(v___x_1334_, v___x_1336_, v___x_1356_);
v___x_1358_ = l_Lean_Syntax_node1(v___x_1334_, v___x_1348_, v___x_1357_);
v___x_1359_ = l_Lean_Syntax_node7(v___x_1334_, v___x_1338_, v___x_1340_, v___x_1342_, v___x_1342_, v___x_1342_, v___x_1345_, v___x_1347_, v___x_1358_);
v___x_1360_ = l_Lean_Syntax_node2(v___x_1334_, v___x_1337_, v___x_1359_, v___x_1342_);
v___x_1361_ = l_Lean_Syntax_node1(v___x_1334_, v___x_1336_, v___x_1360_);
v___x_1362_ = l_Lean_Syntax_node1(v___x_1334_, v___x_1335_, v___x_1361_);
v___y_1266_ = v___y_1315_;
v___y_1267_ = v_h_x3f_1321_;
v___y_1268_ = v_doElems_1326_;
v___y_1269_ = v___y_1316_;
v___y_1270_ = v___x_1325_;
v___y_1271_ = v___y_1317_;
v___y_1272_ = v___y_1318_;
v_x_1273_ = v_a_1331_;
v_body_1274_ = v___x_1362_;
v___y_1275_ = v___y_1322_;
v___y_1276_ = v_a_1332_;
goto v___jp_1265_;
}
else
{
lean_object* v_a_1363_; lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec(v___x_1325_);
lean_dec(v___x_1324_);
lean_dec(v_h_x3f_1321_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec(v_tk_1261_);
v_a_1363_ = lean_ctor_get(v___x_1330_, 0);
v_a_1364_ = lean_ctor_get(v___x_1330_, 1);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1330_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_inc(v_a_1363_);
lean_dec(v___x_1330_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1363_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
else
{
lean_object* v___x_1372_; 
v___x_1372_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(v___x_1324_, v___x_1327_, v___y_1322_, v___y_1323_);
lean_dec(v___x_1324_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; lean_object* v_a_1374_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_a_1373_);
v_a_1374_ = lean_ctor_get(v___x_1372_, 1);
lean_inc(v_a_1374_);
lean_dec_ref_known(v___x_1372_, 2);
v___y_1266_ = v___y_1315_;
v___y_1267_ = v_h_x3f_1321_;
v___y_1268_ = v_doElems_1326_;
v___y_1269_ = v___y_1316_;
v___y_1270_ = v___x_1325_;
v___y_1271_ = v___y_1317_;
v___y_1272_ = v___y_1318_;
v_x_1273_ = v_a_1373_;
v_body_1274_ = v___y_1314_;
v___y_1275_ = v___y_1322_;
v___y_1276_ = v_a_1374_;
goto v___jp_1265_;
}
else
{
lean_object* v_a_1375_; lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
lean_dec(v___x_1325_);
lean_dec(v_h_x3f_1321_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec(v_tk_1261_);
v_a_1375_ = lean_ctor_get(v___x_1372_, 0);
v_a_1376_ = lean_ctor_get(v___x_1372_, 1);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1372_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_inc(v_a_1375_);
lean_dec(v___x_1372_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1379_ == 0)
{
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_a_1375_);
lean_ctor_set(v_reuseFailAlloc_1382_, 1, v_a_1376_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
}
else
{
v___y_1266_ = v___y_1315_;
v___y_1267_ = v_h_x3f_1321_;
v___y_1268_ = v_doElems_1326_;
v___y_1269_ = v___y_1316_;
v___y_1270_ = v___x_1325_;
v___y_1271_ = v___y_1317_;
v___y_1272_ = v___y_1318_;
v_x_1273_ = v___x_1324_;
v_body_1274_ = v___y_1314_;
v___y_1275_ = v___y_1322_;
v___y_1276_ = v___y_1323_;
goto v___jp_1265_;
}
}
}
v___jp_1014_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
lean_inc_ref_n(v___y_1021_, 3);
v___x_1026_ = l_Array_append___redArg(v___y_1021_, v___y_1025_);
lean_dec_ref(v___y_1025_);
lean_inc_n(v___y_1016_, 3);
lean_inc_n(v___y_1020_, 7);
v___x_1027_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1027_, 0, v___y_1020_);
lean_ctor_set(v___x_1027_, 1, v___y_1016_);
lean_ctor_set(v___x_1027_, 2, v___x_1026_);
v___x_1028_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_1029_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___y_1020_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
lean_inc_ref(v___x_1029_);
v___x_1030_ = l_Lean_Syntax_node6(v___y_1020_, v___x_1013_, v___y_1018_, v___y_1023_, v___y_1015_, v___x_1027_, v___x_1029_, v___y_1017_);
v___x_1031_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1031_, 0, v___y_1020_);
lean_ctor_set(v___x_1031_, 1, v___y_1016_);
lean_ctor_set(v___x_1031_, 2, v___y_1021_);
lean_inc(v___y_1019_);
v___x_1032_ = l_Lean_Syntax_node2(v___y_1020_, v___y_1019_, v___x_1030_, v___x_1031_);
v___x_1033_ = lean_array_push(v___y_1024_, v___x_1032_);
v___x_1034_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_1035_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_1036_ = l_Array_append___redArg(v___y_1021_, v___x_1033_);
lean_dec_ref(v___x_1033_);
v___x_1037_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1037_, 0, v___y_1020_);
lean_ctor_set(v___x_1037_, 1, v___y_1016_);
lean_ctor_set(v___x_1037_, 2, v___x_1036_);
v___x_1038_ = l_Lean_Syntax_node1(v___y_1020_, v___x_1035_, v___x_1037_);
v___x_1039_ = l_Lean_Syntax_node2(v___y_1020_, v___x_1034_, v___x_1029_, v___x_1038_);
v___x_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
lean_ctor_set(v___x_1040_, 1, v___y_1022_);
return v___x_1040_;
}
v___jp_1041_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
lean_inc_ref_n(v___y_1048_, 3);
v___x_1053_ = l_Array_append___redArg(v___y_1048_, v___y_1052_);
lean_dec_ref(v___y_1052_);
lean_inc_n(v___y_1042_, 3);
lean_inc_n(v___y_1051_, 7);
v___x_1054_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1054_, 0, v___y_1051_);
lean_ctor_set(v___x_1054_, 1, v___y_1042_);
lean_ctor_set(v___x_1054_, 2, v___x_1053_);
v___x_1055_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_1056_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___y_1051_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
lean_inc_ref(v___x_1056_);
v___x_1057_ = l_Lean_Syntax_node6(v___y_1051_, v___x_1013_, v___y_1046_, v___y_1045_, v___y_1049_, v___x_1054_, v___x_1056_, v___y_1047_);
v___x_1058_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1058_, 0, v___y_1051_);
lean_ctor_set(v___x_1058_, 1, v___y_1042_);
lean_ctor_set(v___x_1058_, 2, v___y_1048_);
lean_inc(v___y_1050_);
v___x_1059_ = l_Lean_Syntax_node2(v___y_1051_, v___y_1050_, v___x_1057_, v___x_1058_);
v___x_1060_ = lean_array_push(v___y_1043_, v___x_1059_);
v___x_1061_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_1062_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_1063_ = l_Array_append___redArg(v___y_1048_, v___x_1060_);
lean_dec_ref(v___x_1060_);
v___x_1064_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1064_, 0, v___y_1051_);
lean_ctor_set(v___x_1064_, 1, v___y_1042_);
lean_ctor_set(v___x_1064_, 2, v___x_1063_);
v___x_1065_ = l_Lean_Syntax_node1(v___y_1051_, v___x_1062_, v___x_1064_);
v___x_1066_ = l_Lean_Syntax_node2(v___y_1051_, v___x_1061_, v___x_1056_, v___x_1065_);
v___x_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
lean_ctor_set(v___x_1067_, 1, v___y_1044_);
return v___x_1067_;
}
v___jp_1068_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
lean_inc_ref_n(v___y_1074_, 3);
v___x_1080_ = l_Array_append___redArg(v___y_1074_, v___y_1079_);
lean_dec_ref(v___y_1079_);
lean_inc_n(v___y_1073_, 3);
lean_inc_n(v___y_1071_, 7);
v___x_1081_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1081_, 0, v___y_1071_);
lean_ctor_set(v___x_1081_, 1, v___y_1073_);
lean_ctor_set(v___x_1081_, 2, v___x_1080_);
v___x_1082_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_1083_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___y_1071_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
lean_inc_ref(v___x_1083_);
v___x_1084_ = l_Lean_Syntax_node6(v___y_1071_, v___x_1013_, v___y_1078_, v___y_1070_, v___y_1072_, v___x_1081_, v___x_1083_, v___y_1077_);
v___x_1085_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1085_, 0, v___y_1071_);
lean_ctor_set(v___x_1085_, 1, v___y_1073_);
lean_ctor_set(v___x_1085_, 2, v___y_1074_);
lean_inc(v___y_1076_);
v___x_1086_ = l_Lean_Syntax_node2(v___y_1071_, v___y_1076_, v___x_1084_, v___x_1085_);
v___x_1087_ = lean_array_push(v___y_1069_, v___x_1086_);
v___x_1088_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_1089_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_1090_ = l_Array_append___redArg(v___y_1074_, v___x_1087_);
lean_dec_ref(v___x_1087_);
v___x_1091_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1091_, 0, v___y_1071_);
lean_ctor_set(v___x_1091_, 1, v___y_1073_);
lean_ctor_set(v___x_1091_, 2, v___x_1090_);
v___x_1092_ = l_Lean_Syntax_node1(v___y_1071_, v___x_1089_, v___x_1091_);
v___x_1093_ = l_Lean_Syntax_node2(v___y_1071_, v___x_1088_, v___x_1083_, v___x_1092_);
v___x_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
lean_ctor_set(v___x_1094_, 1, v___y_1075_);
return v___x_1094_;
}
v___jp_1095_:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
lean_inc_ref_n(v___y_1100_, 3);
v___x_1107_ = l_Array_append___redArg(v___y_1100_, v___y_1106_);
lean_dec_ref(v___y_1106_);
lean_inc_n(v___y_1099_, 3);
lean_inc_n(v___y_1098_, 7);
v___x_1108_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1108_, 0, v___y_1098_);
lean_ctor_set(v___x_1108_, 1, v___y_1099_);
lean_ctor_set(v___x_1108_, 2, v___x_1107_);
v___x_1109_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_1110_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___y_1098_);
lean_ctor_set(v___x_1110_, 1, v___x_1109_);
lean_inc_ref(v___x_1110_);
v___x_1111_ = l_Lean_Syntax_node6(v___y_1098_, v___x_1013_, v___y_1103_, v___y_1104_, v___y_1097_, v___x_1108_, v___x_1110_, v___y_1102_);
v___x_1112_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1112_, 0, v___y_1098_);
lean_ctor_set(v___x_1112_, 1, v___y_1099_);
lean_ctor_set(v___x_1112_, 2, v___y_1100_);
lean_inc(v___y_1101_);
v___x_1113_ = l_Lean_Syntax_node2(v___y_1098_, v___y_1101_, v___x_1111_, v___x_1112_);
v___x_1114_ = lean_array_push(v___y_1096_, v___x_1113_);
v___x_1115_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_1116_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_1117_ = l_Array_append___redArg(v___y_1100_, v___x_1114_);
lean_dec_ref(v___x_1114_);
v___x_1118_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1118_, 0, v___y_1098_);
lean_ctor_set(v___x_1118_, 1, v___y_1099_);
lean_ctor_set(v___x_1118_, 2, v___x_1117_);
v___x_1119_ = l_Lean_Syntax_node1(v___y_1098_, v___x_1116_, v___x_1118_);
v___x_1120_ = l_Lean_Syntax_node2(v___y_1098_, v___x_1115_, v___x_1110_, v___x_1119_);
v___x_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1120_);
lean_ctor_set(v___x_1121_, 1, v___y_1105_);
return v___x_1121_;
}
v___jp_1122_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
lean_inc_ref_n(v___y_1130_, 3);
v___x_1134_ = l_Array_append___redArg(v___y_1130_, v___y_1133_);
lean_dec_ref(v___y_1133_);
lean_inc_n(v___y_1124_, 3);
lean_inc_n(v___y_1126_, 7);
v___x_1135_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1135_, 0, v___y_1126_);
lean_ctor_set(v___x_1135_, 1, v___y_1124_);
lean_ctor_set(v___x_1135_, 2, v___x_1134_);
v___x_1136_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76));
v___x_1137_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___y_1126_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
lean_inc_ref(v___x_1137_);
v___x_1138_ = l_Lean_Syntax_node6(v___y_1126_, v___x_1013_, v___y_1131_, v___y_1123_, v___y_1132_, v___x_1135_, v___x_1137_, v___y_1127_);
v___x_1139_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1139_, 0, v___y_1126_);
lean_ctor_set(v___x_1139_, 1, v___y_1124_);
lean_ctor_set(v___x_1139_, 2, v___y_1130_);
lean_inc(v___y_1128_);
v___x_1140_ = l_Lean_Syntax_node2(v___y_1126_, v___y_1128_, v___x_1138_, v___x_1139_);
v___x_1141_ = lean_array_push(v___y_1129_, v___x_1140_);
v___x_1142_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__2));
v___x_1143_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__3));
v___x_1144_ = l_Array_append___redArg(v___y_1130_, v___x_1141_);
lean_dec_ref(v___x_1141_);
v___x_1145_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1145_, 0, v___y_1126_);
lean_ctor_set(v___x_1145_, 1, v___y_1124_);
lean_ctor_set(v___x_1145_, 2, v___x_1144_);
v___x_1146_ = l_Lean_Syntax_node1(v___y_1126_, v___x_1143_, v___x_1145_);
v___x_1147_ = l_Lean_Syntax_node2(v___y_1126_, v___x_1142_, v___x_1137_, v___x_1146_);
v___x_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
lean_ctor_set(v___x_1148_, 1, v___y_1125_);
return v___x_1148_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_expandDoFor___boxed(lean_object* v_stx_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_Lean_Elab_Do_expandDoFor(v_stx_2388_, v_a_2389_, v_a_2390_);
lean_dec_ref(v_a_2389_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0(uint8_t v___x_2392_, lean_object* v_inst_2393_, lean_object* v_R_2394_, lean_object* v_a_2395_, lean_object* v_b_2396_, lean_object* v_c_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
lean_object* v___x_2400_; 
v___x_2400_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_2392_, v_a_2395_, v_b_2396_, v___y_2398_, v___y_2399_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___boxed(lean_object* v___x_2401_, lean_object* v_inst_2402_, lean_object* v_R_2403_, lean_object* v_a_2404_, lean_object* v_b_2405_, lean_object* v_c_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
uint8_t v___x_207923__boxed_2409_; lean_object* v_res_2410_; 
v___x_207923__boxed_2409_ = lean_unbox(v___x_2401_);
v_res_2410_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0(v___x_207923__boxed_2409_, v_inst_2402_, v_R_2403_, v_a_2404_, v_b_2405_, v_c_2406_, v___y_2407_, v___y_2408_);
lean_dec_ref(v___y_2407_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2(lean_object* v_inst_2411_, lean_object* v_R_2412_, lean_object* v_a_2413_, lean_object* v_b_2414_, lean_object* v_c_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___redArg(v_a_2413_, v_b_2414_, v___y_2416_, v___y_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2___boxed(lean_object* v_inst_2419_, lean_object* v_R_2420_, lean_object* v_a_2421_, lean_object* v_b_2422_, lean_object* v_c_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__2(v_inst_2419_, v_R_2420_, v_a_2421_, v_b_2422_, v_c_2423_, v___y_2424_, v___y_2425_);
lean_dec_ref(v___y_2424_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1(){
_start:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2434_ = l_Lean_Elab_macroAttribute;
v___x_2435_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
v___x_2436_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1));
v___x_2437_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_expandDoFor___boxed), 3, 0);
v___x_2438_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2434_, v___x_2435_, v___x_2436_, v___x_2437_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___boxed(lean_object* v_a_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1();
return v_res_2440_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__2(void){
_start:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2447_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__1));
v___x_2448_ = l_Lean_stringToMessageData(v___x_2447_);
return v___x_2448_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__3(void){
_start:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__2, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__2_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__2);
v___x_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2449_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg(lean_object* v_invClause_2462_, lean_object* v_h_x3f_2463_, lean_object* v_xs_2464_, lean_object* v_00_u03b1_2465_, lean_object* v_mi_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_){
_start:
{
uint8_t v___y_2475_; lean_object* v___y_2476_; 
if (lean_obj_tag(v_h_x3f_2463_) == 0)
{
uint8_t v___x_2577_; lean_object* v___x_2578_; 
v___x_2577_ = 1;
v___x_2578_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__6));
v___y_2475_ = v___x_2577_;
v___y_2476_ = v___x_2578_;
goto v___jp_2474_;
}
else
{
uint8_t v___x_2579_; lean_object* v___x_2580_; 
v___x_2579_ = 1;
v___x_2580_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__8));
v___y_2475_ = v___x_2579_;
v___y_2476_ = v___x_2580_;
goto v___jp_2474_;
}
v___jp_2474_:
{
lean_object* v___x_2477_; lean_object* v_env_2478_; uint8_t v___x_2479_; 
v___x_2477_ = lean_st_ref_get(v_a_2472_);
v_env_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc_ref(v_env_2478_);
lean_dec(v___x_2477_);
lean_inc(v___y_2476_);
v___x_2479_ = l_Lean_Environment_contains(v_env_2478_, v___y_2476_, v___y_2475_);
if (v___x_2479_ == 0)
{
lean_object* v___x_2480_; lean_object* v___x_2481_; 
lean_dec_ref(v_mi_2466_);
lean_dec_ref(v_00_u03b1_2465_);
lean_dec_ref(v_xs_2464_);
v___x_2480_ = lean_box(0);
v___x_2481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2480_);
return v___x_2481_;
}
else
{
lean_object* v_fileName_2482_; lean_object* v_fileMap_2483_; lean_object* v_options_2484_; lean_object* v_currRecDepth_2485_; lean_object* v_maxRecDepth_2486_; lean_object* v_ref_2487_; lean_object* v_currNamespace_2488_; lean_object* v_openDecls_2489_; lean_object* v_initHeartbeats_2490_; lean_object* v_maxHeartbeats_2491_; lean_object* v_quotContext_2492_; lean_object* v_currMacroScope_2493_; uint8_t v_diag_2494_; lean_object* v_cancelTk_x3f_2495_; uint8_t v_suppressElabErrors_2496_; lean_object* v_inheritedTraceOptions_2497_; lean_object* v_m_2498_; lean_object* v_ref_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v_fileName_2482_ = lean_ctor_get(v_a_2471_, 0);
v_fileMap_2483_ = lean_ctor_get(v_a_2471_, 1);
v_options_2484_ = lean_ctor_get(v_a_2471_, 2);
v_currRecDepth_2485_ = lean_ctor_get(v_a_2471_, 3);
v_maxRecDepth_2486_ = lean_ctor_get(v_a_2471_, 4);
v_ref_2487_ = lean_ctor_get(v_a_2471_, 5);
v_currNamespace_2488_ = lean_ctor_get(v_a_2471_, 6);
v_openDecls_2489_ = lean_ctor_get(v_a_2471_, 7);
v_initHeartbeats_2490_ = lean_ctor_get(v_a_2471_, 8);
v_maxHeartbeats_2491_ = lean_ctor_get(v_a_2471_, 9);
v_quotContext_2492_ = lean_ctor_get(v_a_2471_, 10);
v_currMacroScope_2493_ = lean_ctor_get(v_a_2471_, 11);
v_diag_2494_ = lean_ctor_get_uint8(v_a_2471_, sizeof(void*)*14);
v_cancelTk_x3f_2495_ = lean_ctor_get(v_a_2471_, 12);
v_suppressElabErrors_2496_ = lean_ctor_get_uint8(v_a_2471_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2497_ = lean_ctor_get(v_a_2471_, 13);
v_m_2498_ = lean_ctor_get(v_mi_2466_, 0);
lean_inc_ref(v_m_2498_);
lean_dec_ref(v_mi_2466_);
v_ref_2499_ = l_Lean_replaceRef(v_invClause_2462_, v_ref_2487_);
lean_inc_ref(v_inheritedTraceOptions_2497_);
lean_inc(v_cancelTk_x3f_2495_);
lean_inc(v_currMacroScope_2493_);
lean_inc(v_quotContext_2492_);
lean_inc(v_maxHeartbeats_2491_);
lean_inc(v_initHeartbeats_2490_);
lean_inc(v_openDecls_2489_);
lean_inc(v_currNamespace_2488_);
lean_inc(v_ref_2499_);
lean_inc(v_maxRecDepth_2486_);
lean_inc(v_currRecDepth_2485_);
lean_inc_ref(v_options_2484_);
lean_inc_ref(v_fileMap_2483_);
lean_inc_ref(v_fileName_2482_);
v___x_2500_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2500_, 0, v_fileName_2482_);
lean_ctor_set(v___x_2500_, 1, v_fileMap_2483_);
lean_ctor_set(v___x_2500_, 2, v_options_2484_);
lean_ctor_set(v___x_2500_, 3, v_currRecDepth_2485_);
lean_ctor_set(v___x_2500_, 4, v_maxRecDepth_2486_);
lean_ctor_set(v___x_2500_, 5, v_ref_2499_);
lean_ctor_set(v___x_2500_, 6, v_currNamespace_2488_);
lean_ctor_set(v___x_2500_, 7, v_openDecls_2489_);
lean_ctor_set(v___x_2500_, 8, v_initHeartbeats_2490_);
lean_ctor_set(v___x_2500_, 9, v_maxHeartbeats_2491_);
lean_ctor_set(v___x_2500_, 10, v_quotContext_2492_);
lean_ctor_set(v___x_2500_, 11, v_currMacroScope_2493_);
lean_ctor_set(v___x_2500_, 12, v_cancelTk_x3f_2495_);
lean_ctor_set(v___x_2500_, 13, v_inheritedTraceOptions_2497_);
lean_ctor_set_uint8(v___x_2500_, sizeof(void*)*14, v_diag_2494_);
lean_ctor_set_uint8(v___x_2500_, sizeof(void*)*14 + 1, v_suppressElabErrors_2496_);
v___x_2501_ = l_Lean_Elab_Term_exprToSyntax(v_m_2498_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v___x_2500_, v_a_2472_);
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v_a_2502_; lean_object* v___x_2503_; 
v_a_2502_ = lean_ctor_get(v___x_2501_, 0);
lean_inc(v_a_2502_);
lean_dec_ref_known(v___x_2501_, 1);
lean_inc(v_a_2472_);
lean_inc_ref(v___x_2500_);
lean_inc(v_a_2470_);
lean_inc_ref(v_a_2469_);
v___x_2503_ = lean_infer_type(v_xs_2464_, v_a_2469_, v_a_2470_, v___x_2500_, v_a_2472_);
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v_a_2504_; lean_object* v___x_2505_; 
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_a_2504_);
lean_dec_ref_known(v___x_2503_, 1);
v___x_2505_ = l_Lean_Elab_Term_exprToSyntax(v_a_2504_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v___x_2500_, v_a_2472_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_a_2506_; lean_object* v___x_2507_; 
v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_a_2506_);
lean_dec_ref_known(v___x_2505_, 1);
v___x_2507_ = l_Lean_Elab_Term_exprToSyntax(v_00_u03b1_2465_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v___x_2500_, v_a_2472_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_a_2508_; uint8_t v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
lean_inc(v_a_2508_);
lean_dec_ref_known(v___x_2507_, 1);
v___x_2509_ = 0;
v___x_2510_ = l_Lean_SourceInfo_fromRef(v_ref_2499_, v___x_2509_);
lean_dec(v_ref_2499_);
v___x_2511_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__0));
lean_inc(v___y_2476_);
v___x_2512_ = l_Lean_mkIdent(v___y_2476_);
v___x_2513_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
lean_inc(v___x_2510_);
v___x_2514_ = l_Lean_Syntax_node3(v___x_2510_, v___x_2513_, v_a_2502_, v_a_2506_, v_a_2508_);
v___x_2515_ = l_Lean_Syntax_node2(v___x_2510_, v___x_2511_, v___x_2512_, v___x_2514_);
v___x_2516_ = l_Lean_Elab_Term_elabType(v___x_2515_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v___x_2500_, v_a_2472_);
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v_a_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v_a_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_a_2517_);
lean_dec_ref_known(v___x_2516_, 1);
v___x_2518_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__3, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__3);
v___x_2519_ = l_Lean_Elab_Term_mkInstMVar(v_a_2517_, v___x_2518_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v___x_2500_, v_a_2472_);
lean_dec_ref_known(v___x_2500_, 14);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2527_; 
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2527_ == 0)
{
lean_object* v_unused_2528_; 
v_unused_2528_ = lean_ctor_get(v___x_2519_, 0);
lean_dec(v_unused_2528_);
v___x_2521_ = v___x_2519_;
v_isShared_2522_ = v_isSharedCheck_2527_;
goto v_resetjp_2520_;
}
else
{
lean_dec(v___x_2519_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2527_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2523_; lean_object* v___x_2525_; 
v___x_2523_ = lean_box(0);
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 0, v___x_2523_);
v___x_2525_ = v___x_2521_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v___x_2523_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
else
{
lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2536_; 
v_a_2529_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2531_ = v___x_2519_;
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___x_2519_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2534_; 
if (v_isShared_2532_ == 0)
{
v___x_2534_ = v___x_2531_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_a_2529_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
else
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
lean_dec_ref_known(v___x_2500_, 14);
v_a_2537_ = lean_ctor_get(v___x_2516_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2539_ = v___x_2516_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2516_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
if (v_isShared_2540_ == 0)
{
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2537_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
lean_dec(v_a_2506_);
lean_dec(v_a_2502_);
lean_dec_ref_known(v___x_2500_, 14);
lean_dec(v_ref_2499_);
v_a_2545_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2507_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2507_);
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
lean_dec(v_a_2502_);
lean_dec_ref_known(v___x_2500_, 14);
lean_dec(v_ref_2499_);
lean_dec_ref(v_00_u03b1_2465_);
v_a_2553_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___x_2505_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2505_);
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
else
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2568_; 
lean_dec(v_a_2502_);
lean_dec_ref_known(v___x_2500_, 14);
lean_dec(v_ref_2499_);
lean_dec_ref(v_00_u03b1_2465_);
v_a_2561_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2563_ = v___x_2503_;
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___x_2503_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2566_; 
if (v_isShared_2564_ == 0)
{
v___x_2566_ = v___x_2563_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2561_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
else
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
lean_dec_ref_known(v___x_2500_, 14);
lean_dec(v_ref_2499_);
lean_dec_ref(v_00_u03b1_2465_);
lean_dec_ref(v_xs_2464_);
v_a_2569_ = lean_ctor_get(v___x_2501_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2571_ = v___x_2501_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2501_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2574_; 
if (v_isShared_2572_ == 0)
{
v___x_2574_ = v___x_2571_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___boxed(lean_object* v_invClause_2581_, lean_object* v_h_x3f_2582_, lean_object* v_xs_2583_, lean_object* v_00_u03b1_2584_, lean_object* v_mi_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_){
_start:
{
lean_object* v_res_2593_; 
v_res_2593_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg(v_invClause_2581_, v_h_x3f_2582_, v_xs_2583_, v_00_u03b1_2584_, v_mi_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_);
lean_dec(v_a_2591_);
lean_dec_ref(v_a_2590_);
lean_dec(v_a_2589_);
lean_dec_ref(v_a_2588_);
lean_dec(v_a_2587_);
lean_dec_ref(v_a_2586_);
lean_dec(v_h_x3f_2582_);
lean_dec(v_invClause_2581_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn(lean_object* v_invClause_2594_, lean_object* v_h_x3f_2595_, lean_object* v_xs_2596_, lean_object* v_00_u03b1_2597_, lean_object* v_mi_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_){
_start:
{
lean_object* v___x_2607_; 
v___x_2607_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg(v_invClause_2594_, v_h_x3f_2595_, v_xs_2596_, v_00_u03b1_2597_, v_mi_2598_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___boxed(lean_object* v_invClause_2608_, lean_object* v_h_x3f_2609_, lean_object* v_xs_2610_, lean_object* v_00_u03b1_2611_, lean_object* v_mi_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn(v_invClause_2608_, v_h_x3f_2609_, v_xs_2610_, v_00_u03b1_2611_, v_mi_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_);
lean_dec(v_a_2619_);
lean_dec_ref(v_a_2618_);
lean_dec(v_a_2617_);
lean_dec_ref(v_a_2616_);
lean_dec(v_a_2615_);
lean_dec_ref(v_a_2614_);
lean_dec_ref(v_a_2613_);
lean_dec(v_h_x3f_2609_);
lean_dec(v_invClause_2608_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f_spec__0___redArg(lean_object* v_e_2622_, lean_object* v___y_2623_){
_start:
{
uint8_t v___x_2625_; 
v___x_2625_ = l_Lean_Expr_hasMVar(v_e_2622_);
if (v___x_2625_ == 0)
{
lean_object* v___x_2626_; 
v___x_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2626_, 0, v_e_2622_);
return v___x_2626_;
}
else
{
lean_object* v___x_2627_; lean_object* v_mctx_2628_; lean_object* v___x_2629_; lean_object* v_fst_2630_; lean_object* v_snd_2631_; lean_object* v___x_2632_; lean_object* v_cache_2633_; lean_object* v_zetaDeltaFVarIds_2634_; lean_object* v_postponed_2635_; lean_object* v_diag_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2645_; 
v___x_2627_ = lean_st_ref_get(v___y_2623_);
v_mctx_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc_ref(v_mctx_2628_);
lean_dec(v___x_2627_);
v___x_2629_ = l_Lean_instantiateMVarsCore(v_mctx_2628_, v_e_2622_);
v_fst_2630_ = lean_ctor_get(v___x_2629_, 0);
lean_inc(v_fst_2630_);
v_snd_2631_ = lean_ctor_get(v___x_2629_, 1);
lean_inc(v_snd_2631_);
lean_dec_ref(v___x_2629_);
v___x_2632_ = lean_st_ref_take(v___y_2623_);
v_cache_2633_ = lean_ctor_get(v___x_2632_, 1);
v_zetaDeltaFVarIds_2634_ = lean_ctor_get(v___x_2632_, 2);
v_postponed_2635_ = lean_ctor_get(v___x_2632_, 3);
v_diag_2636_ = lean_ctor_get(v___x_2632_, 4);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2645_ == 0)
{
lean_object* v_unused_2646_; 
v_unused_2646_ = lean_ctor_get(v___x_2632_, 0);
lean_dec(v_unused_2646_);
v___x_2638_ = v___x_2632_;
v_isShared_2639_ = v_isSharedCheck_2645_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_diag_2636_);
lean_inc(v_postponed_2635_);
lean_inc(v_zetaDeltaFVarIds_2634_);
lean_inc(v_cache_2633_);
lean_dec(v___x_2632_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2645_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2641_; 
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 0, v_snd_2631_);
v___x_2641_ = v___x_2638_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_snd_2631_);
lean_ctor_set(v_reuseFailAlloc_2644_, 1, v_cache_2633_);
lean_ctor_set(v_reuseFailAlloc_2644_, 2, v_zetaDeltaFVarIds_2634_);
lean_ctor_set(v_reuseFailAlloc_2644_, 3, v_postponed_2635_);
lean_ctor_set(v_reuseFailAlloc_2644_, 4, v_diag_2636_);
v___x_2641_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2642_ = lean_st_ref_put(v___y_2623_, v___x_2641_);
v___x_2643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2643_, 0, v_fst_2630_);
return v___x_2643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f_spec__0___redArg___boxed(lean_object* v_e_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v_res_2650_; 
v_res_2650_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f_spec__0___redArg(v_e_2647_, v___y_2648_);
lean_dec(v___y_2648_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f_spec__0(lean_object* v_e_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v___x_2660_; 
v___x_2660_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f_spec__0___redArg(v_e_2651_, v___y_2656_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f_spec__0___boxed(lean_object* v_e_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f_spec__0(v_e_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec_ref(v___y_2662_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f(lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_){
_start:
{
lean_object* v___x_2685_; lean_object* v_env_2686_; lean_object* v___x_2687_; uint8_t v___x_2688_; uint8_t v___x_2689_; 
v___x_2685_ = lean_st_ref_get(v_a_2683_);
v_env_2686_ = lean_ctor_get(v___x_2685_, 0);
lean_inc_ref(v_env_2686_);
lean_dec(v___x_2685_);
v___x_2687_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___closed__2));
v___x_2688_ = 1;
v___x_2689_ = l_Lean_Environment_contains(v_env_2686_, v___x_2687_, v___x_2688_);
if (v___x_2689_ == 0)
{
lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2690_ = lean_box(0);
v___x_2691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2691_, 0, v___x_2690_);
return v___x_2691_;
}
else
{
lean_object* v___x_2692_; 
v___x_2692_ = l_Lean_Meta_mkConstWithFreshMVarLevels(v___x_2687_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2693_; lean_object* v___x_2694_; 
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
lean_inc_n(v_a_2693_, 2);
lean_dec_ref_known(v___x_2692_, 1);
lean_inc(v_a_2683_);
lean_inc_ref(v_a_2682_);
lean_inc(v_a_2681_);
lean_inc_ref(v_a_2680_);
v___x_2694_ = lean_infer_type(v_a_2693_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; uint8_t v___x_2696_; lean_object* v___x_2697_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
lean_inc(v_a_2695_);
lean_dec_ref_known(v___x_2694_, 1);
v___x_2696_ = 0;
v___x_2697_ = l_Lean_Meta_forallMetaTelescope(v_a_2695_, v___x_2696_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2778_; 
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2700_ = v___x_2697_;
v_isShared_2701_ = v_isSharedCheck_2778_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2697_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2778_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v_fst_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; uint8_t v___x_2705_; 
v_fst_2702_ = lean_ctor_get(v_a_2698_, 0);
lean_inc(v_fst_2702_);
lean_dec(v_a_2698_);
v___x_2703_ = lean_unsigned_to_nat(0u);
v___x_2704_ = lean_array_get_size(v_fst_2702_);
v___x_2705_ = lean_nat_dec_lt(v___x_2703_, v___x_2704_);
if (v___x_2705_ == 0)
{
lean_object* v___x_2706_; lean_object* v___x_2708_; 
lean_dec(v_fst_2702_);
lean_dec(v_a_2693_);
v___x_2706_ = lean_box(0);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 0, v___x_2706_);
v___x_2708_ = v___x_2700_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v___x_2706_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
else
{
lean_object* v_monadInfo_2710_; lean_object* v_m_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
lean_del_object(v___x_2700_);
v_monadInfo_2710_ = lean_ctor_get(v_a_2677_, 0);
v_m_2711_ = lean_ctor_get(v_monadInfo_2710_, 0);
v___x_2712_ = lean_array_fget_borrowed(v_fst_2702_, v___x_2703_);
lean_inc_ref(v_m_2711_);
lean_inc(v___x_2712_);
v___x_2713_ = l_Lean_Meta_isExprDefEq(v___x_2712_, v_m_2711_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_);
if (lean_obj_tag(v___x_2713_) == 0)
{
lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2769_; 
v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2716_ = v___x_2713_;
v_isShared_2717_ = v_isSharedCheck_2769_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___x_2713_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2769_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
uint8_t v___x_2718_; 
v___x_2718_ = lean_unbox(v_a_2714_);
lean_dec(v_a_2714_);
if (v___x_2718_ == 0)
{
lean_object* v___x_2719_; lean_object* v___x_2721_; 
lean_dec(v_fst_2702_);
lean_dec(v_a_2693_);
v___x_2719_ = lean_box(0);
if (v_isShared_2717_ == 0)
{
lean_ctor_set(v___x_2716_, 0, v___x_2719_);
v___x_2721_ = v___x_2716_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v___x_2719_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
else
{
lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
lean_del_object(v___x_2716_);
v___x_2723_ = l_Lean_mkAppN(v_a_2693_, v_fst_2702_);
v___x_2724_ = lean_box(0);
v___x_2725_ = l_Lean_Meta_trySynthInstance(v___x_2723_, v___x_2724_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2760_; 
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2728_ = v___x_2725_;
v_isShared_2729_ = v_isSharedCheck_2760_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___x_2725_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2760_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
if (lean_obj_tag(v_a_2726_) == 1)
{
lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2755_; 
v_isSharedCheck_2755_ = !lean_is_exclusive(v_a_2726_);
if (v_isSharedCheck_2755_ == 0)
{
lean_object* v_unused_2756_; 
v_unused_2756_ = lean_ctor_get(v_a_2726_, 0);
lean_dec(v_unused_2756_);
v___x_2731_ = v_a_2726_;
v_isShared_2732_ = v_isSharedCheck_2755_;
goto v_resetjp_2730_;
}
else
{
lean_dec(v_a_2726_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2755_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v___x_2733_; uint8_t v___x_2734_; 
v___x_2733_ = lean_unsigned_to_nat(1u);
v___x_2734_ = lean_nat_dec_lt(v___x_2733_, v___x_2704_);
if (v___x_2734_ == 0)
{
lean_object* v___x_2736_; 
lean_del_object(v___x_2731_);
lean_dec(v_fst_2702_);
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 0, v___x_2724_);
v___x_2736_ = v___x_2728_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v___x_2724_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
else
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2754_; 
lean_del_object(v___x_2728_);
v___x_2738_ = lean_array_fget(v_fst_2702_, v___x_2733_);
lean_dec(v_fst_2702_);
v___x_2739_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f_spec__0___redArg(v___x_2738_, v_a_2681_);
v_a_2740_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2742_ = v___x_2739_;
v_isShared_2743_ = v_isSharedCheck_2754_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_dec(v___x_2739_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2754_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
uint8_t v___x_2744_; 
v___x_2744_ = l_Lean_Expr_hasExprMVar(v_a_2740_);
if (v___x_2744_ == 0)
{
lean_object* v___x_2746_; 
if (v_isShared_2732_ == 0)
{
lean_ctor_set(v___x_2731_, 0, v_a_2740_);
v___x_2746_ = v___x_2731_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2740_);
v___x_2746_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
lean_object* v___x_2748_; 
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 0, v___x_2746_);
v___x_2748_ = v___x_2742_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v___x_2746_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
else
{
lean_object* v___x_2752_; 
lean_dec(v_a_2740_);
lean_del_object(v___x_2731_);
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 0, v___x_2724_);
v___x_2752_ = v___x_2742_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v___x_2724_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
}
}
}
else
{
lean_object* v___x_2758_; 
lean_dec(v_a_2726_);
lean_dec(v_fst_2702_);
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 0, v___x_2724_);
v___x_2758_ = v___x_2728_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v___x_2724_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
}
else
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
lean_dec(v_fst_2702_);
v_a_2761_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2763_ = v___x_2725_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2725_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2766_; 
if (v_isShared_2764_ == 0)
{
v___x_2766_ = v___x_2763_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2761_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
}
}
else
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2777_; 
lean_dec(v_fst_2702_);
lean_dec(v_a_2693_);
v_a_2770_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2772_ = v___x_2713_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2713_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2770_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
}
}
}
else
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2786_; 
lean_dec(v_a_2693_);
v_a_2779_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2781_ = v___x_2697_;
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2697_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2784_; 
if (v_isShared_2782_ == 0)
{
v___x_2784_ = v___x_2781_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2779_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
}
else
{
lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2794_; 
lean_dec(v_a_2693_);
v_a_2787_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2789_ = v___x_2694_;
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v___x_2694_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2787_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
}
else
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
v_a_2795_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v___x_2692_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2692_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2795_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f___boxed(lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_){
_start:
{
lean_object* v_res_2811_; 
v_res_2811_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f(v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_);
lean_dec(v_a_2809_);
lean_dec_ref(v_a_2808_);
lean_dec(v_a_2807_);
lean_dec_ref(v_a_2806_);
lean_dec(v_a_2805_);
lean_dec_ref(v_a_2804_);
lean_dec_ref(v_a_2803_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0_spec__1(lean_object* v_msgData_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
lean_object* v___x_2818_; lean_object* v_env_2819_; lean_object* v___x_2820_; lean_object* v_mctx_2821_; lean_object* v_lctx_2822_; lean_object* v_options_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2818_ = lean_st_ref_get(v___y_2816_);
v_env_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc_ref(v_env_2819_);
lean_dec(v___x_2818_);
v___x_2820_ = lean_st_ref_get(v___y_2814_);
v_mctx_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc_ref(v_mctx_2821_);
lean_dec(v___x_2820_);
v_lctx_2822_ = lean_ctor_get(v___y_2813_, 2);
v_options_2823_ = lean_ctor_get(v___y_2815_, 2);
lean_inc_ref(v_options_2823_);
lean_inc_ref(v_lctx_2822_);
v___x_2824_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2824_, 0, v_env_2819_);
lean_ctor_set(v___x_2824_, 1, v_mctx_2821_);
lean_ctor_set(v___x_2824_, 2, v_lctx_2822_);
lean_ctor_set(v___x_2824_, 3, v_options_2823_);
v___x_2825_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2824_);
lean_ctor_set(v___x_2825_, 1, v_msgData_2812_);
v___x_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2825_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0_spec__1(v_msgData_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0___redArg(lean_object* v_msg_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v_ref_2840_; lean_object* v___x_2841_; lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2850_; 
v_ref_2840_ = lean_ctor_get(v___y_2837_, 5);
v___x_2841_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0_spec__1(v_msg_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_);
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2844_ = v___x_2841_;
v_isShared_2845_ = v_isSharedCheck_2850_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2841_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2850_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2846_; lean_object* v___x_2848_; 
lean_inc(v_ref_2840_);
v___x_2846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2846_, 0, v_ref_2840_);
lean_ctor_set(v___x_2846_, 1, v_a_2842_);
if (v_isShared_2845_ == 0)
{
lean_ctor_set_tag(v___x_2844_, 1);
lean_ctor_set(v___x_2844_, 0, v___x_2846_);
v___x_2848_ = v___x_2844_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v___x_2846_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0___redArg___boxed(lean_object* v_msg_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0___redArg(v_msg_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0___redArg(lean_object* v_ref_2858_, lean_object* v_msg_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
lean_object* v_fileName_2868_; lean_object* v_fileMap_2869_; lean_object* v_options_2870_; lean_object* v_currRecDepth_2871_; lean_object* v_maxRecDepth_2872_; lean_object* v_ref_2873_; lean_object* v_currNamespace_2874_; lean_object* v_openDecls_2875_; lean_object* v_initHeartbeats_2876_; lean_object* v_maxHeartbeats_2877_; lean_object* v_quotContext_2878_; lean_object* v_currMacroScope_2879_; uint8_t v_diag_2880_; lean_object* v_cancelTk_x3f_2881_; uint8_t v_suppressElabErrors_2882_; lean_object* v_inheritedTraceOptions_2883_; lean_object* v_ref_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v_fileName_2868_ = lean_ctor_get(v___y_2865_, 0);
v_fileMap_2869_ = lean_ctor_get(v___y_2865_, 1);
v_options_2870_ = lean_ctor_get(v___y_2865_, 2);
v_currRecDepth_2871_ = lean_ctor_get(v___y_2865_, 3);
v_maxRecDepth_2872_ = lean_ctor_get(v___y_2865_, 4);
v_ref_2873_ = lean_ctor_get(v___y_2865_, 5);
v_currNamespace_2874_ = lean_ctor_get(v___y_2865_, 6);
v_openDecls_2875_ = lean_ctor_get(v___y_2865_, 7);
v_initHeartbeats_2876_ = lean_ctor_get(v___y_2865_, 8);
v_maxHeartbeats_2877_ = lean_ctor_get(v___y_2865_, 9);
v_quotContext_2878_ = lean_ctor_get(v___y_2865_, 10);
v_currMacroScope_2879_ = lean_ctor_get(v___y_2865_, 11);
v_diag_2880_ = lean_ctor_get_uint8(v___y_2865_, sizeof(void*)*14);
v_cancelTk_x3f_2881_ = lean_ctor_get(v___y_2865_, 12);
v_suppressElabErrors_2882_ = lean_ctor_get_uint8(v___y_2865_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2883_ = lean_ctor_get(v___y_2865_, 13);
v_ref_2884_ = l_Lean_replaceRef(v_ref_2858_, v_ref_2873_);
lean_inc_ref(v_inheritedTraceOptions_2883_);
lean_inc(v_cancelTk_x3f_2881_);
lean_inc(v_currMacroScope_2879_);
lean_inc(v_quotContext_2878_);
lean_inc(v_maxHeartbeats_2877_);
lean_inc(v_initHeartbeats_2876_);
lean_inc(v_openDecls_2875_);
lean_inc(v_currNamespace_2874_);
lean_inc(v_maxRecDepth_2872_);
lean_inc(v_currRecDepth_2871_);
lean_inc_ref(v_options_2870_);
lean_inc_ref(v_fileMap_2869_);
lean_inc_ref(v_fileName_2868_);
v___x_2885_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2885_, 0, v_fileName_2868_);
lean_ctor_set(v___x_2885_, 1, v_fileMap_2869_);
lean_ctor_set(v___x_2885_, 2, v_options_2870_);
lean_ctor_set(v___x_2885_, 3, v_currRecDepth_2871_);
lean_ctor_set(v___x_2885_, 4, v_maxRecDepth_2872_);
lean_ctor_set(v___x_2885_, 5, v_ref_2884_);
lean_ctor_set(v___x_2885_, 6, v_currNamespace_2874_);
lean_ctor_set(v___x_2885_, 7, v_openDecls_2875_);
lean_ctor_set(v___x_2885_, 8, v_initHeartbeats_2876_);
lean_ctor_set(v___x_2885_, 9, v_maxHeartbeats_2877_);
lean_ctor_set(v___x_2885_, 10, v_quotContext_2878_);
lean_ctor_set(v___x_2885_, 11, v_currMacroScope_2879_);
lean_ctor_set(v___x_2885_, 12, v_cancelTk_x3f_2881_);
lean_ctor_set(v___x_2885_, 13, v_inheritedTraceOptions_2883_);
lean_ctor_set_uint8(v___x_2885_, sizeof(void*)*14, v_diag_2880_);
lean_ctor_set_uint8(v___x_2885_, sizeof(void*)*14 + 1, v_suppressElabErrors_2882_);
v___x_2886_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0___redArg(v_msg_2859_, v___y_2863_, v___y_2864_, v___x_2885_, v___y_2866_);
lean_dec_ref_known(v___x_2885_, 14);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0___redArg___boxed(lean_object* v_ref_2887_, lean_object* v_msg_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_){
_start:
{
lean_object* v_res_2897_; 
v_res_2897_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0___redArg(v_ref_2887_, v_msg_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
lean_dec(v___y_2893_);
lean_dec_ref(v___y_2892_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v_ref_2887_);
return v_res_2897_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__1(void){
_start:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2899_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__0));
v___x_2900_ = l_Lean_stringToMessageData(v___x_2899_);
return v___x_2900_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__3(void){
_start:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2902_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__2));
v___x_2903_ = l_Lean_stringToMessageData(v___x_2902_);
return v___x_2903_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__5(void){
_start:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2905_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__4));
v___x_2906_ = l_Lean_stringToMessageData(v___x_2905_);
return v___x_2906_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__7(void){
_start:
{
lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2908_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__6));
v___x_2909_ = l_Lean_stringToMessageData(v___x_2908_);
return v___x_2909_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__9(void){
_start:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2911_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__8));
v___x_2912_ = l_Lean_stringToMessageData(v___x_2911_);
return v___x_2912_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__11(void){
_start:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2914_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__10));
v___x_2915_ = l_Lean_stringToMessageData(v___x_2914_);
return v___x_2915_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__13(void){
_start:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; 
v___x_2917_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__12));
v___x_2918_ = l_Lean_stringToMessageData(v___x_2917_);
return v___x_2918_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__15(void){
_start:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2920_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__14));
v___x_2921_ = l_Lean_stringToMessageData(v___x_2920_);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders(lean_object* v_ref_2922_, lean_object* v_what_2923_, lean_object* v_binders_2924_, lean_object* v_pred_x3f_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_){
_start:
{
lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___x_2949_; uint8_t v___x_2950_; 
v___x_2949_ = lean_unsigned_to_nat(0u);
v___x_2950_ = lean_nat_dec_eq(v_binders_2924_, v___x_2949_);
if (v___x_2950_ == 0)
{
if (lean_obj_tag(v_pred_x3f_2925_) == 1)
{
lean_object* v_val_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2980_; 
v_val_2951_ = lean_ctor_get(v_pred_x3f_2925_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v_pred_x3f_2925_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2953_ = v_pred_x3f_2925_;
v_isShared_2954_ = v_isSharedCheck_2980_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_val_2951_);
lean_dec(v_pred_x3f_2925_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2980_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v_arity_2955_; uint8_t v___x_2956_; 
v_arity_2955_ = l_Lean_Expr_getForallArity(v_val_2951_);
v___x_2956_ = lean_nat_dec_lt(v_arity_2955_, v_binders_2924_);
if (v___x_2956_ == 0)
{
lean_object* v___x_2957_; lean_object* v___x_2959_; 
lean_dec(v_arity_2955_);
lean_dec(v_binders_2924_);
lean_dec_ref(v_what_2923_);
v___x_2957_ = lean_box(0);
if (v_isShared_2954_ == 0)
{
lean_ctor_set_tag(v___x_2953_, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2957_);
v___x_2959_ = v___x_2953_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v___x_2957_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
return v___x_2959_;
}
}
else
{
lean_object* v___x_2961_; lean_object* v___y_2963_; uint8_t v___x_2973_; 
v___x_2961_ = lean_unsigned_to_nat(1u);
v___x_2973_ = lean_nat_dec_eq(v_arity_2955_, v___x_2961_);
if (v___x_2973_ == 0)
{
lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2974_ = l_Nat_reprFast(v_arity_2955_);
v___x_2975_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2974_);
v___x_2976_ = l_Lean_MessageData_ofFormat(v___x_2975_);
v___x_2977_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__13, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__13_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__13);
v___x_2978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2976_);
lean_ctor_set(v___x_2978_, 1, v___x_2977_);
v___y_2963_ = v___x_2978_;
goto v___jp_2962_;
}
else
{
lean_object* v___x_2979_; 
lean_dec(v_arity_2955_);
v___x_2979_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__15, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__15_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__15);
v___y_2963_ = v___x_2979_;
goto v___jp_2962_;
}
v___jp_2962_:
{
uint8_t v___x_2964_; 
v___x_2964_ = lean_nat_dec_eq(v_binders_2924_, v___x_2961_);
if (v___x_2964_ == 0)
{
lean_object* v___x_2965_; lean_object* v___x_2967_; 
v___x_2965_ = l_Nat_reprFast(v_binders_2924_);
if (v_isShared_2954_ == 0)
{
lean_ctor_set_tag(v___x_2953_, 3);
lean_ctor_set(v___x_2953_, 0, v___x_2965_);
v___x_2967_ = v___x_2953_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v___x_2965_);
v___x_2967_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2968_ = l_Lean_MessageData_ofFormat(v___x_2967_);
v___x_2969_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__9, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__9_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__9);
v___x_2970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2968_);
lean_ctor_set(v___x_2970_, 1, v___x_2969_);
v___y_2935_ = v___y_2963_;
v___y_2936_ = v___x_2970_;
goto v___jp_2934_;
}
}
else
{
lean_object* v___x_2972_; 
lean_del_object(v___x_2953_);
lean_dec(v_binders_2924_);
v___x_2972_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__11, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__11_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__11);
v___y_2935_ = v___y_2963_;
v___y_2936_ = v___x_2972_;
goto v___jp_2934_;
}
}
}
}
}
else
{
lean_object* v___x_2981_; lean_object* v___x_2982_; 
lean_dec(v_pred_x3f_2925_);
lean_dec(v_binders_2924_);
lean_dec_ref(v_what_2923_);
v___x_2981_ = lean_box(0);
v___x_2982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2982_, 0, v___x_2981_);
return v___x_2982_;
}
}
else
{
lean_object* v___x_2983_; lean_object* v___x_2984_; 
lean_dec(v_pred_x3f_2925_);
lean_dec(v_binders_2924_);
lean_dec_ref(v_what_2923_);
v___x_2983_ = lean_box(0);
v___x_2984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2983_);
return v___x_2984_;
}
v___jp_2934_:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2937_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__1, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__1);
v___x_2938_ = l_Lean_stringToMessageData(v_what_2923_);
v___x_2939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2939_, 0, v___x_2937_);
lean_ctor_set(v___x_2939_, 1, v___x_2938_);
v___x_2940_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__3, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__3);
v___x_2941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2939_);
lean_ctor_set(v___x_2941_, 1, v___x_2940_);
v___x_2942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
lean_ctor_set(v___x_2942_, 1, v___y_2935_);
v___x_2943_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__5, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__5_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__5);
v___x_2944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2942_);
lean_ctor_set(v___x_2944_, 1, v___x_2943_);
v___x_2945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2944_);
lean_ctor_set(v___x_2945_, 1, v___y_2936_);
v___x_2946_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__7, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__7_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__7);
v___x_2947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2945_);
lean_ctor_set(v___x_2947_, 1, v___x_2946_);
v___x_2948_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0___redArg(v_ref_2922_, v___x_2947_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_);
return v___x_2948_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___boxed(lean_object* v_ref_2985_, lean_object* v_what_2986_, lean_object* v_binders_2987_, lean_object* v_pred_x3f_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_){
_start:
{
lean_object* v_res_2997_; 
v_res_2997_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders(v_ref_2985_, v_what_2986_, v_binders_2987_, v_pred_x3f_2988_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_);
lean_dec(v_a_2995_);
lean_dec_ref(v_a_2994_);
lean_dec(v_a_2993_);
lean_dec_ref(v_a_2992_);
lean_dec(v_a_2991_);
lean_dec_ref(v_a_2990_);
lean_dec_ref(v_a_2989_);
lean_dec(v_ref_2985_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0(lean_object* v_00_u03b1_2998_, lean_object* v_ref_2999_, lean_object* v_msg_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_){
_start:
{
lean_object* v___x_3009_; 
v___x_3009_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0___redArg(v_ref_2999_, v_msg_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0___boxed(lean_object* v_00_u03b1_3010_, lean_object* v_ref_3011_, lean_object* v_msg_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0(v_00_u03b1_3010_, v_ref_3011_, v_msg_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
lean_dec(v___y_3019_);
lean_dec_ref(v___y_3018_);
lean_dec(v___y_3017_);
lean_dec_ref(v___y_3016_);
lean_dec(v___y_3015_);
lean_dec_ref(v___y_3014_);
lean_dec_ref(v___y_3013_);
lean_dec(v_ref_3011_);
return v_res_3021_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0(lean_object* v_00_u03b1_3022_, lean_object* v_msg_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_){
_start:
{
lean_object* v___x_3032_; 
v___x_3032_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0___redArg(v_msg_3023_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3033_, lean_object* v_msg_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_){
_start:
{
lean_object* v_res_3043_; 
v_res_3043_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0(v_00_u03b1_3033_, v_msg_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3040_);
lean_dec(v___y_3039_);
lean_dec_ref(v___y_3038_);
lean_dec(v___y_3037_);
lean_dec_ref(v___y_3036_);
lean_dec_ref(v___y_3035_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___lam__0(uint8_t v___x_3044_, lean_object* v_____do__lift_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_){
_start:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3054_ = l_Lean_SourceInfo_fromRef(v_____do__lift_3045_, v___x_3044_);
v___x_3055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___lam__0___boxed(lean_object* v___x_3056_, lean_object* v_____do__lift_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_){
_start:
{
uint8_t v___x_14253__boxed_3066_; lean_object* v_res_3067_; 
v___x_14253__boxed_3066_ = lean_unbox(v___x_3056_);
v_res_3067_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___lam__0(v___x_14253__boxed_3066_, v_____do__lift_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec(v_____do__lift_3057_);
return v_res_3067_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__1___redArg(lean_object* v___x_3075_, lean_object* v_as_3076_, size_t v_i_3077_, size_t v_stop_3078_, lean_object* v_b_3079_, lean_object* v___y_3080_){
_start:
{
uint8_t v___x_3082_; 
v___x_3082_ = lean_usize_dec_eq(v_i_3077_, v_stop_3078_);
if (v___x_3082_ == 0)
{
lean_object* v_ref_3083_; lean_object* v___x_3084_; uint8_t v___x_3085_; size_t v___x_3086_; size_t v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v_ref_3083_ = lean_ctor_get(v___y_3080_, 5);
v___x_3084_ = lean_unsigned_to_nat(0u);
v___x_3085_ = lean_nat_dec_eq(v___x_3075_, v___x_3084_);
v___x_3086_ = ((size_t)1ULL);
v___x_3087_ = lean_usize_sub(v_i_3077_, v___x_3086_);
v___x_3088_ = lean_array_uget_borrowed(v_as_3076_, v___x_3087_);
v___x_3089_ = l_Lean_SourceInfo_fromRef(v_ref_3083_, v___x_3085_);
v___x_3090_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__1___redArg___closed__1));
v___x_3091_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__1___redArg___closed__2));
lean_inc(v___x_3089_);
v___x_3092_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3089_);
lean_ctor_set(v___x_3092_, 1, v___x_3091_);
lean_inc(v___x_3088_);
v___x_3093_ = l_Lean_Syntax_node3(v___x_3089_, v___x_3090_, v___x_3088_, v___x_3092_, v_b_3079_);
v_i_3077_ = v___x_3087_;
v_b_3079_ = v___x_3093_;
goto _start;
}
else
{
lean_object* v___x_3095_; 
v___x_3095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3095_, 0, v_b_3079_);
return v___x_3095_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__1___redArg___boxed(lean_object* v___x_3096_, lean_object* v_as_3097_, lean_object* v_i_3098_, lean_object* v_stop_3099_, lean_object* v_b_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_){
_start:
{
size_t v_i_boxed_3103_; size_t v_stop_boxed_3104_; lean_object* v_res_3105_; 
v_i_boxed_3103_ = lean_unbox_usize(v_i_3098_);
lean_dec(v_i_3098_);
v_stop_boxed_3104_ = lean_unbox_usize(v_stop_3099_);
lean_dec(v_stop_3099_);
v_res_3105_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__1___redArg(v___x_3096_, v_as_3097_, v_i_boxed_3103_, v_stop_boxed_3104_, v_b_3100_, v___y_3101_);
lean_dec_ref(v___y_3101_);
lean_dec_ref(v_as_3097_);
lean_dec(v___x_3096_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__0___redArg(lean_object* v___x_3106_, size_t v_sz_3107_, size_t v_i_3108_, lean_object* v_b_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
uint8_t v___x_3117_; 
v___x_3117_ = lean_usize_dec_lt(v_i_3108_, v_sz_3107_);
if (v___x_3117_ == 0)
{
lean_object* v___x_3118_; 
lean_dec(v___x_3106_);
v___x_3118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3118_, 0, v_b_3109_);
return v___x_3118_;
}
else
{
lean_object* v_snd_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3167_; 
v_snd_3119_ = lean_ctor_get(v_b_3109_, 1);
v_isSharedCheck_3167_ = !lean_is_exclusive(v_b_3109_);
if (v_isSharedCheck_3167_ == 0)
{
lean_object* v_unused_3168_; 
v_unused_3168_ = lean_ctor_get(v_b_3109_, 0);
lean_dec(v_unused_3168_);
v___x_3121_ = v_b_3109_;
v_isShared_3122_ = v_isSharedCheck_3167_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_snd_3119_);
lean_dec(v_b_3109_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3167_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v_snd_3123_; 
v_snd_3123_ = lean_ctor_get(v_snd_3119_, 1);
lean_inc(v_snd_3123_);
if (lean_obj_tag(v_snd_3123_) == 7)
{
lean_object* v_fst_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3151_; 
v_fst_3124_ = lean_ctor_get(v_snd_3119_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v_snd_3119_);
if (v_isSharedCheck_3151_ == 0)
{
lean_object* v_unused_3152_; 
v_unused_3152_ = lean_ctor_get(v_snd_3119_, 1);
lean_dec(v_unused_3152_);
v___x_3126_ = v_snd_3119_;
v_isShared_3127_ = v_isSharedCheck_3151_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_fst_3124_);
lean_dec(v_snd_3119_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3151_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v_binderType_3128_; lean_object* v_body_3129_; lean_object* v___x_3130_; 
v_binderType_3128_ = lean_ctor_get(v_snd_3123_, 1);
lean_inc_ref(v_binderType_3128_);
v_body_3129_ = lean_ctor_get(v_snd_3123_, 2);
lean_inc_ref(v_body_3129_);
lean_dec_ref_known(v_snd_3123_, 3);
v___x_3130_ = l_Lean_Elab_Term_exprToSyntax(v_binderType_3128_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v_a_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3135_; 
v_a_3131_ = lean_ctor_get(v___x_3130_, 0);
lean_inc(v_a_3131_);
lean_dec_ref_known(v___x_3130_, 1);
v___x_3132_ = lean_box(0);
v___x_3133_ = lean_array_push(v_fst_3124_, v_a_3131_);
if (v_isShared_3127_ == 0)
{
lean_ctor_set(v___x_3126_, 1, v_body_3129_);
lean_ctor_set(v___x_3126_, 0, v___x_3133_);
v___x_3135_ = v___x_3126_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v___x_3133_);
lean_ctor_set(v_reuseFailAlloc_3142_, 1, v_body_3129_);
v___x_3135_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
lean_object* v___x_3137_; 
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 1, v___x_3135_);
lean_ctor_set(v___x_3121_, 0, v___x_3132_);
v___x_3137_ = v___x_3121_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v___x_3132_);
lean_ctor_set(v_reuseFailAlloc_3141_, 1, v___x_3135_);
v___x_3137_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
size_t v___x_3138_; size_t v___x_3139_; 
v___x_3138_ = ((size_t)1ULL);
v___x_3139_ = lean_usize_add(v_i_3108_, v___x_3138_);
v_i_3108_ = v___x_3139_;
v_b_3109_ = v___x_3137_;
goto _start;
}
}
}
else
{
lean_object* v_a_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3150_; 
lean_dec_ref(v_body_3129_);
lean_del_object(v___x_3126_);
lean_dec(v_fst_3124_);
lean_del_object(v___x_3121_);
lean_dec(v___x_3106_);
v_a_3143_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3145_ = v___x_3130_;
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_a_3143_);
lean_dec(v___x_3130_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3148_; 
if (v_isShared_3146_ == 0)
{
v___x_3148_ = v___x_3145_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3143_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
}
}
}
else
{
lean_object* v_fst_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3165_; 
v_fst_3153_ = lean_ctor_get(v_snd_3119_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v_snd_3119_);
if (v_isSharedCheck_3165_ == 0)
{
lean_object* v_unused_3166_; 
v_unused_3166_ = lean_ctor_get(v_snd_3119_, 1);
lean_dec(v_unused_3166_);
v___x_3155_ = v_snd_3119_;
v_isShared_3156_ = v_isSharedCheck_3165_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_fst_3153_);
lean_dec(v_snd_3119_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3165_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3157_; lean_object* v___x_3159_; 
v___x_3157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3106_);
if (v_isShared_3156_ == 0)
{
v___x_3159_ = v___x_3155_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_fst_3153_);
lean_ctor_set(v_reuseFailAlloc_3164_, 1, v_snd_3123_);
v___x_3159_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
lean_object* v___x_3161_; 
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 1, v___x_3159_);
lean_ctor_set(v___x_3121_, 0, v___x_3157_);
v___x_3161_ = v___x_3121_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v___x_3157_);
lean_ctor_set(v_reuseFailAlloc_3163_, 1, v___x_3159_);
v___x_3161_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
lean_object* v___x_3162_; 
v___x_3162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3161_);
return v___x_3162_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__0___redArg___boxed(lean_object* v___x_3169_, lean_object* v_sz_3170_, lean_object* v_i_3171_, lean_object* v_b_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
size_t v_sz_boxed_3180_; size_t v_i_boxed_3181_; lean_object* v_res_3182_; 
v_sz_boxed_3180_ = lean_unbox_usize(v_sz_3170_);
lean_dec(v_sz_3170_);
v_i_boxed_3181_ = lean_unbox_usize(v_i_3171_);
lean_dec(v_i_3171_);
v_res_3182_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__0___redArg(v___x_3169_, v_sz_boxed_3180_, v_i_boxed_3181_, v_b_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun(lean_object* v_binders_3232_, lean_object* v_body_3233_, lean_object* v_pred_x3f_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_){
_start:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; uint8_t v___x_3245_; 
v___x_3243_ = lean_array_get_size(v_binders_3232_);
v___x_3244_ = lean_unsigned_to_nat(0u);
v___x_3245_ = lean_nat_dec_eq(v___x_3243_, v___x_3244_);
if (v___x_3245_ == 0)
{
lean_object* v_ref_3246_; lean_object* v_quotContext_3247_; lean_object* v_currMacroScope_3248_; lean_object* v___x_3249_; lean_object* v_a_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3345_; 
v_ref_3246_ = lean_ctor_get(v_a_3240_, 5);
v_quotContext_3247_ = lean_ctor_get(v_a_3240_, 10);
v_currMacroScope_3248_ = lean_ctor_get(v_a_3240_, 11);
v___x_3249_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___lam__0(v___x_3245_, v_ref_3246_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_);
v_a_3250_ = lean_ctor_get(v___x_3249_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3252_ = v___x_3249_;
v_isShared_3253_ = v_isSharedCheck_3345_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_a_3250_);
lean_dec(v___x_3249_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3345_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v_a_3268_; 
v___x_3254_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__0));
v___x_3255_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__1));
lean_inc_n(v_a_3250_, 5);
v___x_3256_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3256_, 0, v_a_3250_);
lean_ctor_set(v___x_3256_, 1, v___x_3254_);
v___x_3257_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__3));
v___x_3258_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_3259_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_3260_ = l_Array_append___redArg(v___x_3259_, v_binders_3232_);
v___x_3261_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3261_, 0, v_a_3250_);
lean_ctor_set(v___x_3261_, 1, v___x_3258_);
lean_ctor_set(v___x_3261_, 2, v___x_3260_);
v___x_3262_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3262_, 0, v_a_3250_);
lean_ctor_set(v___x_3262_, 1, v___x_3258_);
lean_ctor_set(v___x_3262_, 2, v___x_3259_);
v___x_3263_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_3264_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3264_, 0, v_a_3250_);
lean_ctor_set(v___x_3264_, 1, v___x_3263_);
v___x_3265_ = l_Lean_Syntax_node4(v_a_3250_, v___x_3257_, v___x_3261_, v___x_3262_, v___x_3264_, v_body_3233_);
v___x_3266_ = l_Lean_Syntax_node2(v_a_3250_, v___x_3255_, v___x_3256_, v___x_3265_);
if (lean_obj_tag(v_pred_x3f_3234_) == 1)
{
lean_object* v_val_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; size_t v_sz_3301_; size_t v___x_3302_; lean_object* v___x_3303_; 
lean_del_object(v___x_3252_);
v_val_3296_ = lean_ctor_get(v_pred_x3f_3234_, 0);
v___x_3297_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_3298_ = lean_box(0);
lean_inc(v_val_3296_);
v___x_3299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3297_);
lean_ctor_set(v___x_3299_, 1, v_val_3296_);
v___x_3300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3298_);
lean_ctor_set(v___x_3300_, 1, v___x_3299_);
v_sz_3301_ = lean_array_size(v_binders_3232_);
v___x_3302_ = ((size_t)0ULL);
lean_inc(v___x_3266_);
v___x_3303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__0___redArg(v___x_3266_, v_sz_3301_, v___x_3302_, v___x_3300_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_);
if (lean_obj_tag(v___x_3303_) == 0)
{
lean_object* v_a_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3333_; 
v_a_3304_ = lean_ctor_get(v___x_3303_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3303_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3306_ = v___x_3303_;
v_isShared_3307_ = v_isSharedCheck_3333_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_a_3304_);
lean_dec(v___x_3303_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3333_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
lean_object* v_fst_3308_; 
v_fst_3308_ = lean_ctor_get(v_a_3304_, 0);
if (lean_obj_tag(v_fst_3308_) == 0)
{
lean_object* v_snd_3309_; lean_object* v___x_3310_; lean_object* v_a_3311_; lean_object* v_fst_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3327_; 
lean_del_object(v___x_3306_);
v_snd_3309_ = lean_ctor_get(v_a_3304_, 1);
lean_inc(v_snd_3309_);
lean_dec(v_a_3304_);
v___x_3310_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___lam__0(v___x_3245_, v_ref_3246_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_);
v_a_3311_ = lean_ctor_get(v___x_3310_, 0);
lean_inc(v_a_3311_);
lean_dec_ref(v___x_3310_);
v_fst_3312_ = lean_ctor_get(v_snd_3309_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v_snd_3309_);
if (v_isSharedCheck_3327_ == 0)
{
lean_object* v_unused_3328_; 
v_unused_3328_ = lean_ctor_get(v_snd_3309_, 1);
lean_dec(v_unused_3328_);
v___x_3314_ = v_snd_3309_;
v_isShared_3315_ = v_isSharedCheck_3327_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_fst_3312_);
lean_dec(v_snd_3309_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3327_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3319_; 
v___x_3316_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
v___x_3317_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15));
lean_inc(v_a_3311_);
if (v_isShared_3315_ == 0)
{
lean_ctor_set_tag(v___x_3314_, 2);
lean_ctor_set(v___x_3314_, 1, v___x_3317_);
lean_ctor_set(v___x_3314_, 0, v_a_3311_);
v___x_3319_ = v___x_3314_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_a_3311_);
lean_ctor_set(v_reuseFailAlloc_3326_, 1, v___x_3317_);
v___x_3319_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
lean_object* v___x_3320_; lean_object* v___x_3321_; uint8_t v___x_3322_; 
v___x_3320_ = l_Lean_Syntax_node1(v_a_3311_, v___x_3316_, v___x_3319_);
v___x_3321_ = lean_array_get_size(v_fst_3312_);
v___x_3322_ = lean_nat_dec_lt(v___x_3244_, v___x_3321_);
if (v___x_3322_ == 0)
{
lean_dec(v_fst_3312_);
v_a_3268_ = v___x_3320_;
goto v___jp_3267_;
}
else
{
size_t v___x_3323_; lean_object* v___x_3324_; 
v___x_3323_ = lean_usize_of_nat(v___x_3321_);
v___x_3324_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__1___redArg(v___x_3243_, v_fst_3312_, v___x_3323_, v___x_3302_, v___x_3320_, v_a_3240_);
lean_dec(v_fst_3312_);
if (lean_obj_tag(v___x_3324_) == 0)
{
lean_object* v_a_3325_; 
v_a_3325_ = lean_ctor_get(v___x_3324_, 0);
lean_inc(v_a_3325_);
lean_dec_ref_known(v___x_3324_, 1);
v_a_3268_ = v_a_3325_;
goto v___jp_3267_;
}
else
{
lean_dec(v___x_3266_);
return v___x_3324_;
}
}
}
}
}
else
{
lean_object* v_val_3329_; lean_object* v___x_3331_; 
lean_inc_ref(v_fst_3308_);
lean_dec(v_a_3304_);
lean_dec(v___x_3266_);
v_val_3329_ = lean_ctor_get(v_fst_3308_, 0);
lean_inc(v_val_3329_);
lean_dec_ref_known(v_fst_3308_, 1);
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 0, v_val_3329_);
v___x_3331_ = v___x_3306_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_val_3329_);
v___x_3331_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
return v___x_3331_;
}
}
}
}
else
{
lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3341_; 
lean_dec(v___x_3266_);
v_a_3334_ = lean_ctor_get(v___x_3303_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3303_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3336_ = v___x_3303_;
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3303_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3339_; 
if (v_isShared_3337_ == 0)
{
v___x_3339_ = v___x_3336_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_a_3334_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
}
else
{
lean_object* v___x_3343_; 
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 0, v___x_3266_);
v___x_3343_ = v___x_3252_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v___x_3266_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
v___jp_3267_:
{
lean_object* v___x_3269_; lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3295_; 
v___x_3269_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___lam__0(v___x_3245_, v_ref_3246_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_);
v_a_3270_ = lean_ctor_get(v___x_3269_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3272_ = v___x_3269_;
v_isShared_3273_ = v_isSharedCheck_3295_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3269_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3295_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3293_; 
v___x_3274_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__5));
v___x_3275_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__6));
v___x_3276_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__61));
lean_inc_n(v_a_3270_, 7);
v___x_3277_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3277_, 0, v_a_3270_);
lean_ctor_set(v___x_3277_, 1, v___x_3276_);
v___x_3278_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__63));
v___x_3279_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65);
v___x_3280_ = lean_box(0);
lean_inc(v_currMacroScope_3248_);
lean_inc(v_quotContext_3247_);
v___x_3281_ = l_Lean_addMacroScope(v_quotContext_3247_, v___x_3280_, v_currMacroScope_3248_);
v___x_3282_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__15));
v___x_3283_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3283_, 0, v_a_3270_);
lean_ctor_set(v___x_3283_, 1, v___x_3279_);
lean_ctor_set(v___x_3283_, 2, v___x_3281_);
lean_ctor_set(v___x_3283_, 3, v___x_3282_);
v___x_3284_ = l_Lean_Syntax_node1(v_a_3270_, v___x_3278_, v___x_3283_);
v___x_3285_ = l_Lean_Syntax_node2(v_a_3270_, v___x_3275_, v___x_3277_, v___x_3284_);
v___x_3286_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__8));
v___x_3287_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3287_, 0, v_a_3270_);
lean_ctor_set(v___x_3287_, 1, v___x_3286_);
v___x_3288_ = l_Lean_Syntax_node1(v_a_3270_, v___x_3258_, v_a_3268_);
v___x_3289_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__72));
v___x_3290_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3290_, 0, v_a_3270_);
lean_ctor_set(v___x_3290_, 1, v___x_3289_);
v___x_3291_ = l_Lean_Syntax_node5(v_a_3270_, v___x_3274_, v___x_3285_, v___x_3266_, v___x_3287_, v___x_3288_, v___x_3290_);
if (v_isShared_3273_ == 0)
{
lean_ctor_set(v___x_3272_, 0, v___x_3291_);
v___x_3293_ = v___x_3272_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v___x_3291_);
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
else
{
lean_object* v___x_3346_; 
v___x_3346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3346_, 0, v_body_3233_);
return v___x_3346_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___boxed(lean_object* v_binders_3347_, lean_object* v_body_3348_, lean_object* v_pred_x3f_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_){
_start:
{
lean_object* v_res_3358_; 
v_res_3358_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun(v_binders_3347_, v_body_3348_, v_pred_x3f_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_);
lean_dec(v_a_3356_);
lean_dec_ref(v_a_3355_);
lean_dec(v_a_3354_);
lean_dec_ref(v_a_3353_);
lean_dec(v_a_3352_);
lean_dec_ref(v_a_3351_);
lean_dec_ref(v_a_3350_);
lean_dec(v_pred_x3f_3349_);
lean_dec_ref(v_binders_3347_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__0(lean_object* v___x_3359_, lean_object* v_as_3360_, size_t v_sz_3361_, size_t v_i_3362_, lean_object* v_b_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_){
_start:
{
lean_object* v___x_3372_; 
v___x_3372_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__0___redArg(v___x_3359_, v_sz_3361_, v_i_3362_, v_b_3363_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
return v___x_3372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__0___boxed(lean_object* v___x_3373_, lean_object* v_as_3374_, lean_object* v_sz_3375_, lean_object* v_i_3376_, lean_object* v_b_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_){
_start:
{
size_t v_sz_boxed_3386_; size_t v_i_boxed_3387_; lean_object* v_res_3388_; 
v_sz_boxed_3386_ = lean_unbox_usize(v_sz_3375_);
lean_dec(v_sz_3375_);
v_i_boxed_3387_ = lean_unbox_usize(v_i_3376_);
lean_dec(v_i_3376_);
v_res_3388_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__0(v___x_3373_, v_as_3374_, v_sz_boxed_3386_, v_i_boxed_3387_, v_b_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
lean_dec(v___y_3382_);
lean_dec_ref(v___y_3381_);
lean_dec(v___y_3380_);
lean_dec_ref(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec_ref(v_as_3374_);
return v_res_3388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__1(lean_object* v___x_3389_, lean_object* v_as_3390_, size_t v_i_3391_, size_t v_stop_3392_, lean_object* v_b_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
lean_object* v___x_3402_; 
v___x_3402_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__1___redArg(v___x_3389_, v_as_3390_, v_i_3391_, v_stop_3392_, v_b_3393_, v___y_3399_);
return v___x_3402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__1___boxed(lean_object* v___x_3403_, lean_object* v_as_3404_, lean_object* v_i_3405_, lean_object* v_stop_3406_, lean_object* v_b_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_){
_start:
{
size_t v_i_boxed_3416_; size_t v_stop_boxed_3417_; lean_object* v_res_3418_; 
v_i_boxed_3416_ = lean_unbox_usize(v_i_3405_);
lean_dec(v_i_3405_);
v_stop_boxed_3417_ = lean_unbox_usize(v_stop_3406_);
lean_dec(v_stop_3406_);
v_res_3418_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun_spec__1(v___x_3403_, v_as_3404_, v_i_boxed_3416_, v_stop_boxed_3417_, v_b_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_);
lean_dec(v___y_3414_);
lean_dec_ref(v___y_3413_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec_ref(v_as_3404_);
lean_dec(v___x_3403_);
return v_res_3418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___lam__0(lean_object* v_____do__lift_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_){
_start:
{
uint8_t v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; 
v___x_3428_ = 0;
v___x_3429_ = l_Lean_SourceInfo_fromRef(v_____do__lift_3419_, v___x_3428_);
v___x_3430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3429_);
return v___x_3430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___lam__0___boxed(lean_object* v_____do__lift_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_){
_start:
{
lean_object* v_res_3440_; 
v_res_3440_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___lam__0(v_____do__lift_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
lean_dec(v___y_3436_);
lean_dec_ref(v___y_3435_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
lean_dec_ref(v___y_3432_);
lean_dec(v_____do__lift_3431_);
return v_res_3440_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat_spec__0___redArg(lean_object* v_as_3441_, size_t v_sz_3442_, size_t v_i_3443_, lean_object* v_b_3444_){
_start:
{
uint8_t v___x_3446_; 
v___x_3446_ = lean_usize_dec_lt(v_i_3443_, v_sz_3442_);
if (v___x_3446_ == 0)
{
lean_object* v___x_3447_; 
v___x_3447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3447_, 0, v_b_3444_);
return v___x_3447_;
}
else
{
lean_object* v_a_3448_; lean_object* v_ident_3449_; lean_object* v___x_3450_; size_t v___x_3451_; size_t v___x_3452_; 
v_a_3448_ = lean_array_uget_borrowed(v_as_3441_, v_i_3443_);
v_ident_3449_ = lean_ctor_get(v_a_3448_, 0);
lean_inc(v_ident_3449_);
v___x_3450_ = lean_array_push(v_b_3444_, v_ident_3449_);
v___x_3451_ = ((size_t)1ULL);
v___x_3452_ = lean_usize_add(v_i_3443_, v___x_3451_);
v_i_3443_ = v___x_3452_;
v_b_3444_ = v___x_3450_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat_spec__0___redArg___boxed(lean_object* v_as_3454_, lean_object* v_sz_3455_, lean_object* v_i_3456_, lean_object* v_b_3457_, lean_object* v___y_3458_){
_start:
{
size_t v_sz_boxed_3459_; size_t v_i_boxed_3460_; lean_object* v_res_3461_; 
v_sz_boxed_3459_ = lean_unbox_usize(v_sz_3455_);
lean_dec(v_sz_3455_);
v_i_boxed_3460_ = lean_unbox_usize(v_i_3456_);
lean_dec(v_i_3456_);
v_res_3461_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat_spec__0___redArg(v_as_3454_, v_sz_boxed_3459_, v_i_boxed_3460_, v_b_3457_);
lean_dec_ref(v_as_3454_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat(lean_object* v_loopMutVars_3470_, uint8_t v_returnsEarly_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_){
_start:
{
lean_object* v_ref_3480_; lean_object* v_binders_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___x_3527_; lean_object* v_a_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v_binders_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___x_3559_; 
v_ref_3480_ = lean_ctor_get(v_a_3477_, 5);
v___x_3527_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___lam__0(v_ref_3480_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_);
v_a_3528_ = lean_ctor_get(v___x_3527_, 0);
lean_inc_n(v_a_3528_, 2);
lean_dec_ref(v___x_3527_);
v___x_3529_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
v___x_3530_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15));
v___x_3531_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3531_, 0, v_a_3528_);
lean_ctor_set(v___x_3531_, 1, v___x_3530_);
v___x_3532_ = l_Lean_Syntax_node1(v_a_3528_, v___x_3529_, v___x_3531_);
v___x_3559_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
if (v_returnsEarly_3471_ == 0)
{
v_binders_3534_ = v___x_3559_;
v___y_3535_ = v_a_3472_;
v___y_3536_ = v_a_3473_;
v___y_3537_ = v_a_3474_;
v___y_3538_ = v_a_3475_;
v___y_3539_ = v_a_3476_;
v___y_3540_ = v_a_3477_;
v___y_3541_ = v_a_3478_;
goto v___jp_3533_;
}
else
{
lean_object* v___x_3560_; 
lean_inc(v___x_3532_);
v___x_3560_ = lean_array_push(v___x_3559_, v___x_3532_);
v_binders_3534_ = v___x_3560_;
v___y_3535_ = v_a_3472_;
v___y_3536_ = v_a_3473_;
v___y_3537_ = v_a_3474_;
v___y_3538_ = v_a_3475_;
v___y_3539_ = v_a_3476_;
v___y_3540_ = v_a_3477_;
v___y_3541_ = v_a_3478_;
goto v___jp_3533_;
}
v___jp_3481_:
{
lean_object* v___x_3490_; lean_object* v___x_3491_; uint8_t v___x_3492_; 
v___x_3490_ = lean_array_get_size(v_binders_3482_);
v___x_3491_ = lean_unsigned_to_nat(0u);
v___x_3492_ = lean_nat_dec_eq(v___x_3490_, v___x_3491_);
if (v___x_3492_ == 0)
{
lean_object* v___x_3493_; uint8_t v___x_3494_; 
v___x_3493_ = lean_unsigned_to_nat(1u);
v___x_3494_ = lean_nat_dec_eq(v___x_3490_, v___x_3493_);
if (v___x_3494_ == 0)
{
lean_object* v_ref_3495_; lean_object* v___x_3496_; lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3516_; 
v_ref_3495_ = lean_ctor_get(v___y_3488_, 5);
v___x_3496_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___lam__0(v_ref_3495_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_);
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3516_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3499_ = v___x_3496_;
v_isShared_3500_ = v_isSharedCheck_3516_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3496_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3516_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3514_; 
v___x_3501_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__1));
v___x_3502_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__2));
lean_inc_n(v_a_3497_, 3);
v___x_3503_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3503_, 0, v_a_3497_);
lean_ctor_set(v___x_3503_, 1, v___x_3502_);
v___x_3504_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_3505_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_3506_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__5));
v___x_3507_ = l_Lean_Syntax_SepArray_ofElems(v___x_3506_, v_binders_3482_);
lean_dec_ref(v_binders_3482_);
v___x_3508_ = l_Array_append___redArg(v___x_3505_, v___x_3507_);
lean_dec_ref(v___x_3507_);
v___x_3509_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3509_, 0, v_a_3497_);
lean_ctor_set(v___x_3509_, 1, v___x_3504_);
lean_ctor_set(v___x_3509_, 2, v___x_3508_);
v___x_3510_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___closed__3));
v___x_3511_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3511_, 0, v_a_3497_);
lean_ctor_set(v___x_3511_, 1, v___x_3510_);
v___x_3512_ = l_Lean_Syntax_node3(v_a_3497_, v___x_3501_, v___x_3503_, v___x_3509_, v___x_3511_);
if (v_isShared_3500_ == 0)
{
lean_ctor_set(v___x_3499_, 0, v___x_3512_);
v___x_3514_ = v___x_3499_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v___x_3512_);
v___x_3514_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
return v___x_3514_;
}
}
}
else
{
lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3517_ = lean_array_fget(v_binders_3482_, v___x_3491_);
lean_dec_ref(v_binders_3482_);
v___x_3518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3517_);
return v___x_3518_;
}
}
else
{
lean_object* v_ref_3519_; uint8_t v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; 
lean_dec_ref(v_binders_3482_);
v_ref_3519_ = lean_ctor_get(v___y_3488_, 5);
v___x_3520_ = 0;
v___x_3521_ = l_Lean_SourceInfo_fromRef(v_ref_3519_, v___x_3520_);
v___x_3522_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
v___x_3523_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15));
lean_inc(v___x_3521_);
v___x_3524_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3521_);
lean_ctor_set(v___x_3524_, 1, v___x_3523_);
v___x_3525_ = l_Lean_Syntax_node1(v___x_3521_, v___x_3522_, v___x_3524_);
v___x_3526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3525_);
return v___x_3526_;
}
}
v___jp_3533_:
{
size_t v_sz_3542_; size_t v___x_3543_; lean_object* v___x_3544_; 
v_sz_3542_ = lean_array_size(v_loopMutVars_3470_);
v___x_3543_ = ((size_t)0ULL);
v___x_3544_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat_spec__0___redArg(v_loopMutVars_3470_, v_sz_3542_, v___x_3543_, v_binders_3534_);
if (lean_obj_tag(v___x_3544_) == 0)
{
if (v_returnsEarly_3471_ == 0)
{
lean_object* v_a_3545_; 
lean_dec(v___x_3532_);
v_a_3545_ = lean_ctor_get(v___x_3544_, 0);
lean_inc(v_a_3545_);
lean_dec_ref_known(v___x_3544_, 1);
v_binders_3482_ = v_a_3545_;
v___y_3483_ = v___y_3535_;
v___y_3484_ = v___y_3536_;
v___y_3485_ = v___y_3537_;
v___y_3486_ = v___y_3538_;
v___y_3487_ = v___y_3539_;
v___y_3488_ = v___y_3540_;
v___y_3489_ = v___y_3541_;
goto v___jp_3481_;
}
else
{
lean_object* v_a_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; uint8_t v___x_3549_; 
v_a_3546_ = lean_ctor_get(v___x_3544_, 0);
lean_inc(v_a_3546_);
lean_dec_ref_known(v___x_3544_, 1);
v___x_3547_ = lean_array_get_size(v_loopMutVars_3470_);
v___x_3548_ = lean_unsigned_to_nat(0u);
v___x_3549_ = lean_nat_dec_eq(v___x_3547_, v___x_3548_);
if (v___x_3549_ == 0)
{
lean_dec(v___x_3532_);
v_binders_3482_ = v_a_3546_;
v___y_3483_ = v___y_3535_;
v___y_3484_ = v___y_3536_;
v___y_3485_ = v___y_3537_;
v___y_3486_ = v___y_3538_;
v___y_3487_ = v___y_3539_;
v___y_3488_ = v___y_3540_;
v___y_3489_ = v___y_3541_;
goto v___jp_3481_;
}
else
{
lean_object* v___x_3550_; 
v___x_3550_ = lean_array_push(v_a_3546_, v___x_3532_);
v_binders_3482_ = v___x_3550_;
v___y_3483_ = v___y_3535_;
v___y_3484_ = v___y_3536_;
v___y_3485_ = v___y_3537_;
v___y_3486_ = v___y_3538_;
v___y_3487_ = v___y_3539_;
v___y_3488_ = v___y_3540_;
v___y_3489_ = v___y_3541_;
goto v___jp_3481_;
}
}
}
else
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3558_; 
lean_dec(v___x_3532_);
v_a_3551_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3553_ = v___x_3544_;
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3544_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3556_; 
if (v_isShared_3554_ == 0)
{
v___x_3556_ = v___x_3553_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_a_3551_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat___boxed(lean_object* v_loopMutVars_3561_, lean_object* v_returnsEarly_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_){
_start:
{
uint8_t v_returnsEarly_boxed_3571_; lean_object* v_res_3572_; 
v_returnsEarly_boxed_3571_ = lean_unbox(v_returnsEarly_3562_);
v_res_3572_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat(v_loopMutVars_3561_, v_returnsEarly_boxed_3571_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_);
lean_dec(v_a_3569_);
lean_dec_ref(v_a_3568_);
lean_dec(v_a_3567_);
lean_dec_ref(v_a_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
lean_dec_ref(v_a_3563_);
lean_dec_ref(v_loopMutVars_3561_);
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat_spec__0(lean_object* v_as_3573_, size_t v_sz_3574_, size_t v_i_3575_, lean_object* v_b_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_){
_start:
{
lean_object* v___x_3585_; 
v___x_3585_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat_spec__0___redArg(v_as_3573_, v_sz_3574_, v_i_3575_, v_b_3576_);
return v___x_3585_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat_spec__0___boxed(lean_object* v_as_3586_, lean_object* v_sz_3587_, lean_object* v_i_3588_, lean_object* v_b_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_){
_start:
{
size_t v_sz_boxed_3598_; size_t v_i_boxed_3599_; lean_object* v_res_3600_; 
v_sz_boxed_3598_ = lean_unbox_usize(v_sz_3587_);
lean_dec(v_sz_3587_);
v_i_boxed_3599_ = lean_unbox_usize(v_i_3588_);
lean_dec(v_i_3588_);
v_res_3600_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat_spec__0(v_as_3586_, v_sz_boxed_3598_, v_i_boxed_3599_, v_b_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec(v___y_3594_);
lean_dec_ref(v___y_3593_);
lean_dec(v___y_3592_);
lean_dec_ref(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec_ref(v_as_3586_);
return v_res_3600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkStateFun___redArg(lean_object* v_g_3601_, lean_object* v_e_3602_, lean_object* v_a_3603_){
_start:
{
lean_object* v_ref_3605_; lean_object* v_statePat_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; uint8_t v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; 
v_ref_3605_ = lean_ctor_get(v_a_3603_, 5);
v_statePat_3606_ = lean_ctor_get(v_g_3601_, 4);
lean_inc(v_statePat_3606_);
lean_dec_ref(v_g_3601_);
v___x_3607_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__0));
v___x_3608_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__1));
v___x_3609_ = 0;
v___x_3610_ = l_Lean_SourceInfo_fromRef(v_ref_3605_, v___x_3609_);
lean_inc_n(v___x_3610_, 5);
v___x_3611_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3610_);
lean_ctor_set(v___x_3611_, 1, v___x_3607_);
v___x_3612_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__3));
v___x_3613_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_3614_ = l_Lean_Syntax_node1(v___x_3610_, v___x_3613_, v_statePat_3606_);
v___x_3615_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_3616_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3616_, 0, v___x_3610_);
lean_ctor_set(v___x_3616_, 1, v___x_3613_);
lean_ctor_set(v___x_3616_, 2, v___x_3615_);
v___x_3617_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_3618_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3610_);
lean_ctor_set(v___x_3618_, 1, v___x_3617_);
v___x_3619_ = l_Lean_Syntax_node4(v___x_3610_, v___x_3612_, v___x_3614_, v___x_3616_, v___x_3618_, v_e_3602_);
v___x_3620_ = l_Lean_Syntax_node2(v___x_3610_, v___x_3608_, v___x_3611_, v___x_3619_);
v___x_3621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3621_, 0, v___x_3620_);
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkStateFun___redArg___boxed(lean_object* v_g_3622_, lean_object* v_e_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_){
_start:
{
lean_object* v_res_3626_; 
v_res_3626_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkStateFun___redArg(v_g_3622_, v_e_3623_, v_a_3624_);
lean_dec_ref(v_a_3624_);
return v_res_3626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkStateFun(lean_object* v_g_3627_, lean_object* v_e_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_){
_start:
{
lean_object* v___x_3637_; 
v___x_3637_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkStateFun___redArg(v_g_3627_, v_e_3628_, v_a_3634_);
return v___x_3637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkStateFun___boxed(lean_object* v_g_3638_, lean_object* v_e_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_){
_start:
{
lean_object* v_res_3648_; 
v_res_3648_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkStateFun(v_g_3638_, v_e_3639_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_, v_a_3646_);
lean_dec(v_a_3646_);
lean_dec_ref(v_a_3645_);
lean_dec(v_a_3644_);
lean_dec_ref(v_a_3643_);
lean_dec(v_a_3642_);
lean_dec_ref(v_a_3641_);
lean_dec_ref(v_a_3640_);
return v_res_3648_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__7(void){
_start:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3664_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__6));
v___x_3665_ = l_String_toRawSubstring_x27(v___x_3664_);
return v___x_3665_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__12(void){
_start:
{
lean_object* v___x_3675_; lean_object* v___x_3676_; 
v___x_3675_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__11));
v___x_3676_ = l_String_toRawSubstring_x27(v___x_3675_);
return v___x_3676_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__18(void){
_start:
{
lean_object* v___x_3687_; lean_object* v___x_3688_; 
v___x_3687_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__17));
v___x_3688_ = l_Lean_stringToMessageData(v___x_3687_);
return v___x_3688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall(lean_object* v_g_3689_, lean_object* v_ref_3690_, lean_object* v_gadget_3691_, lean_object* v_annotations_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_, lean_object* v_a_3699_){
_start:
{
lean_object* v___y_3702_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v___x_3783_; lean_object* v_env_3784_; uint8_t v___x_3785_; uint8_t v___x_3786_; 
v___x_3783_ = lean_st_ref_get(v_a_3699_);
v_env_3784_ = lean_ctor_get(v___x_3783_, 0);
lean_inc_ref(v_env_3784_);
lean_dec(v___x_3783_);
v___x_3785_ = 1;
lean_inc(v_gadget_3691_);
v___x_3786_ = l_Lean_Environment_contains(v_env_3784_, v_gadget_3691_, v___x_3785_);
if (v___x_3786_ == 0)
{
lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v_a_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3796_; 
lean_dec(v_gadget_3691_);
lean_dec_ref(v_g_3689_);
v___x_3787_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__18, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__18_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__18);
v___x_3788_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0___redArg(v_ref_3690_, v___x_3787_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_, v_a_3699_);
v_a_3789_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3796_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3791_ = v___x_3788_;
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_a_3789_);
lean_dec(v___x_3788_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v___x_3794_; 
if (v_isShared_3792_ == 0)
{
v___x_3794_ = v___x_3791_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_a_3789_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
}
else
{
v___y_3702_ = v_a_3693_;
v___y_3703_ = v_a_3694_;
v___y_3704_ = v_a_3695_;
v___y_3705_ = v_a_3696_;
v___y_3706_ = v_a_3697_;
v___y_3707_ = v_a_3698_;
v___y_3708_ = v_a_3699_;
goto v___jp_3701_;
}
v___jp_3701_:
{
lean_object* v_xs_3709_; lean_object* v_init_3710_; lean_object* v_body_3711_; lean_object* v_00_u03c3_3712_; lean_object* v___x_3713_; 
v_xs_3709_ = lean_ctor_get(v_g_3689_, 0);
lean_inc_ref(v_xs_3709_);
v_init_3710_ = lean_ctor_get(v_g_3689_, 1);
lean_inc_ref(v_init_3710_);
v_body_3711_ = lean_ctor_get(v_g_3689_, 2);
lean_inc_ref(v_body_3711_);
v_00_u03c3_3712_ = lean_ctor_get(v_g_3689_, 3);
lean_inc_ref(v_00_u03c3_3712_);
lean_dec_ref(v_g_3689_);
v___x_3713_ = l_Lean_Elab_Term_exprToSyntax(v_xs_3709_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v_a_3714_; lean_object* v___x_3715_; 
v_a_3714_ = lean_ctor_get(v___x_3713_, 0);
lean_inc(v_a_3714_);
lean_dec_ref_known(v___x_3713_, 1);
v___x_3715_ = l_Lean_Elab_Term_exprToSyntax(v_init_3710_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_object* v_a_3716_; lean_object* v___x_3717_; 
v_a_3716_ = lean_ctor_get(v___x_3715_, 0);
lean_inc(v_a_3716_);
lean_dec_ref_known(v___x_3715_, 1);
v___x_3717_ = l_Lean_Elab_Term_exprToSyntax(v_body_3711_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; lean_object* v_ref_3719_; lean_object* v_quotContext_3720_; lean_object* v_currMacroScope_3721_; uint8_t v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v_monadInfo_3743_; lean_object* v_m_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; uint8_t v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_a_3718_);
lean_dec_ref_known(v___x_3717_, 1);
v_ref_3719_ = lean_ctor_get(v___y_3707_, 5);
v_quotContext_3720_ = lean_ctor_get(v___y_3707_, 10);
v_currMacroScope_3721_ = lean_ctor_get(v___y_3707_, 11);
v___x_3722_ = 0;
v___x_3723_ = l_Lean_SourceInfo_fromRef(v_ref_3719_, v___x_3722_);
v___x_3724_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__0));
v___x_3725_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__1));
lean_inc_n(v___x_3723_, 9);
v___x_3726_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3726_, 0, v___x_3723_);
lean_ctor_set(v___x_3726_, 1, v___x_3724_);
v___x_3727_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__4));
v___x_3728_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__5));
v___x_3729_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3723_);
lean_ctor_set(v___x_3729_, 1, v___x_3728_);
v___x_3730_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_3731_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__7, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__7_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__7);
v___x_3732_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__8));
lean_inc_n(v_currMacroScope_3721_, 2);
lean_inc_n(v_quotContext_3720_, 2);
v___x_3733_ = l_Lean_addMacroScope(v_quotContext_3720_, v___x_3732_, v_currMacroScope_3721_);
v___x_3734_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__10));
v___x_3735_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3723_);
lean_ctor_set(v___x_3735_, 1, v___x_3731_);
lean_ctor_set(v___x_3735_, 2, v___x_3733_);
lean_ctor_set(v___x_3735_, 3, v___x_3734_);
v___x_3736_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__12, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__12_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__12);
v___x_3737_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__14));
v___x_3738_ = l_Lean_addMacroScope(v_quotContext_3720_, v___x_3737_, v_currMacroScope_3721_);
v___x_3739_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___closed__16));
v___x_3740_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3723_);
lean_ctor_set(v___x_3740_, 1, v___x_3736_);
lean_ctor_set(v___x_3740_, 2, v___x_3738_);
lean_ctor_set(v___x_3740_, 3, v___x_3739_);
v___x_3741_ = l_Lean_Syntax_node2(v___x_3723_, v___x_3730_, v___x_3735_, v___x_3740_);
v___x_3742_ = l_Lean_Syntax_node2(v___x_3723_, v___x_3727_, v___x_3729_, v___x_3741_);
v_monadInfo_3743_ = lean_ctor_get(v___y_3702_, 0);
v_m_3744_ = lean_ctor_get(v_monadInfo_3743_, 0);
v___x_3745_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__5));
v___x_3746_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3746_, 0, v___x_3723_);
lean_ctor_set(v___x_3746_, 1, v___x_3745_);
v___x_3747_ = l_Array_mkArray3___redArg(v_a_3714_, v_a_3716_, v_a_3718_);
v___x_3748_ = l_Array_append___redArg(v___x_3747_, v_annotations_3692_);
v___x_3749_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3723_);
lean_ctor_set(v___x_3749_, 1, v___x_3730_);
lean_ctor_set(v___x_3749_, 2, v___x_3748_);
v___x_3750_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg___closed__0));
v___x_3751_ = l_Lean_mkIdent(v_gadget_3691_);
v___x_3752_ = l_Lean_Syntax_node2(v___x_3723_, v___x_3750_, v___x_3751_, v___x_3749_);
v___x_3753_ = l_Lean_Syntax_node4(v___x_3723_, v___x_3725_, v___x_3726_, v___x_3742_, v___x_3746_, v___x_3752_);
lean_inc_ref(v_m_3744_);
v___x_3754_ = l_Lean_Expr_app___override(v_m_3744_, v_00_u03c3_3712_);
v___x_3755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3754_);
v___x_3756_ = 1;
v___x_3757_ = lean_box(0);
v___x_3758_ = l_Lean_Elab_Term_elabTermEnsuringType(v___x_3753_, v___x_3755_, v___x_3756_, v___x_3756_, v___x_3757_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
return v___x_3758_;
}
else
{
lean_object* v_a_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3766_; 
lean_dec(v_a_3716_);
lean_dec(v_a_3714_);
lean_dec_ref(v_00_u03c3_3712_);
lean_dec(v_gadget_3691_);
v_a_3759_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3761_ = v___x_3717_;
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_a_3759_);
lean_dec(v___x_3717_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
lean_object* v___x_3764_; 
if (v_isShared_3762_ == 0)
{
v___x_3764_ = v___x_3761_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v_a_3759_);
v___x_3764_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
return v___x_3764_;
}
}
}
}
else
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3774_; 
lean_dec(v_a_3714_);
lean_dec_ref(v_00_u03c3_3712_);
lean_dec_ref(v_body_3711_);
lean_dec(v_gadget_3691_);
v_a_3767_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3769_ = v___x_3715_;
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3715_);
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
else
{
lean_object* v_a_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3782_; 
lean_dec_ref(v_00_u03c3_3712_);
lean_dec_ref(v_body_3711_);
lean_dec_ref(v_init_3710_);
lean_dec(v_gadget_3691_);
v_a_3775_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3777_ = v___x_3713_;
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_a_3775_);
lean_dec(v___x_3713_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___x_3780_; 
if (v_isShared_3778_ == 0)
{
v___x_3780_ = v___x_3777_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_a_3775_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall___boxed(lean_object* v_g_3797_, lean_object* v_ref_3798_, lean_object* v_gadget_3799_, lean_object* v_annotations_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_){
_start:
{
lean_object* v_res_3809_; 
v_res_3809_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall(v_g_3797_, v_ref_3798_, v_gadget_3799_, v_annotations_3800_, v_a_3801_, v_a_3802_, v_a_3803_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_);
lean_dec(v_a_3807_);
lean_dec_ref(v_a_3806_);
lean_dec(v_a_3805_);
lean_dec_ref(v_a_3804_);
lean_dec(v_a_3803_);
lean_dec_ref(v_a_3802_);
lean_dec_ref(v_a_3801_);
lean_dec_ref(v_annotations_3800_);
lean_dec(v_ref_3798_);
return v_res_3809_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; 
v___x_3810_ = lean_box(0);
v___x_3811_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3811_);
lean_ctor_set(v___x_3812_, 1, v___x_3810_);
return v___x_3812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg(){
_start:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; 
v___x_3814_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg___closed__0);
v___x_3815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3814_);
return v___x_3815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg___boxed(lean_object* v___y_3816_){
_start:
{
lean_object* v_res_3817_; 
v_res_3817_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg();
return v_res_3817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0(lean_object* v_00_u03b1_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_){
_start:
{
lean_object* v___x_3827_; 
v___x_3827_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg();
return v___x_3827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___boxed(lean_object* v_00_u03b1_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
lean_object* v_res_3837_; 
v_res_3837_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0(v_00_u03b1_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
lean_dec_ref(v___y_3829_);
return v_res_3837_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__3(void){
_start:
{
lean_object* v___x_3845_; lean_object* v___x_3846_; 
v___x_3845_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__2));
v___x_3846_ = l_Lean_stringToMessageData(v___x_3845_);
return v___x_3846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant(lean_object* v_invClause_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_){
_start:
{
lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___x_3882_; uint8_t v___x_3883_; 
v___x_3882_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__19));
lean_inc(v_invClause_3847_);
v___x_3883_ = l_Lean_Syntax_isOfKind(v_invClause_3847_, v___x_3882_);
if (v___x_3883_ == 0)
{
v___y_3857_ = v_a_3848_;
v___y_3858_ = v_a_3849_;
v___y_3859_ = v_a_3850_;
v___y_3860_ = v_a_3851_;
v___y_3861_ = v_a_3852_;
v___y_3862_ = v_a_3853_;
v___y_3863_ = v_a_3854_;
goto v___jp_3856_;
}
else
{
lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; uint8_t v___x_3887_; 
v___x_3884_ = lean_unsigned_to_nat(1u);
v___x_3885_ = l_Lean_Syntax_getArg(v_invClause_3847_, v___x_3884_);
v___x_3886_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__3));
lean_inc(v___x_3885_);
v___x_3887_ = l_Lean_Syntax_isOfKind(v___x_3885_, v___x_3886_);
if (v___x_3887_ == 0)
{
lean_dec(v___x_3885_);
v___y_3857_ = v_a_3848_;
v___y_3858_ = v_a_3849_;
v___y_3859_ = v_a_3850_;
v___y_3860_ = v_a_3851_;
v___y_3861_ = v_a_3852_;
v___y_3862_ = v_a_3853_;
v___y_3863_ = v_a_3854_;
goto v___jp_3856_;
}
else
{
lean_object* v___x_3888_; uint8_t v___x_3889_; 
v___x_3888_ = l_Lean_Syntax_getArg(v___x_3885_, v___x_3884_);
lean_dec(v___x_3885_);
lean_inc(v___x_3888_);
v___x_3889_ = l_Lean_Syntax_matchesNull(v___x_3888_, v___x_3884_);
if (v___x_3889_ == 0)
{
lean_dec(v___x_3888_);
v___y_3857_ = v_a_3848_;
v___y_3858_ = v_a_3849_;
v___y_3859_ = v_a_3850_;
v___y_3860_ = v_a_3851_;
v___y_3861_ = v_a_3852_;
v___y_3862_ = v_a_3853_;
v___y_3863_ = v_a_3854_;
goto v___jp_3856_;
}
else
{
lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; uint8_t v___x_3893_; 
v___x_3890_ = lean_unsigned_to_nat(0u);
v___x_3891_ = l_Lean_Syntax_getArg(v___x_3888_, v___x_3890_);
lean_dec(v___x_3888_);
v___x_3892_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__1));
lean_inc(v___x_3891_);
v___x_3893_ = l_Lean_Syntax_isOfKind(v___x_3891_, v___x_3892_);
if (v___x_3893_ == 0)
{
lean_dec(v___x_3891_);
v___y_3857_ = v_a_3848_;
v___y_3858_ = v_a_3849_;
v___y_3859_ = v_a_3850_;
v___y_3860_ = v_a_3851_;
v___y_3861_ = v_a_3852_;
v___y_3862_ = v_a_3853_;
v___y_3863_ = v_a_3854_;
goto v___jp_3856_;
}
else
{
lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v_a_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3904_; 
lean_dec(v_invClause_3847_);
v___x_3894_ = l_Lean_Syntax_getArg(v___x_3891_, v___x_3884_);
lean_dec(v___x_3891_);
v___x_3895_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__3, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___closed__3);
v___x_3896_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0___redArg(v___x_3894_, v___x_3895_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_);
lean_dec(v___x_3894_);
v_a_3897_ = lean_ctor_get(v___x_3896_, 0);
v_isSharedCheck_3904_ = !lean_is_exclusive(v___x_3896_);
if (v_isSharedCheck_3904_ == 0)
{
v___x_3899_ = v___x_3896_;
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_a_3897_);
lean_dec(v___x_3896_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3904_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3902_; 
if (v_isShared_3900_ == 0)
{
v___x_3902_ = v___x_3899_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v_a_3897_);
v___x_3902_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
return v___x_3902_;
}
}
}
}
}
}
v___jp_3856_:
{
lean_object* v___x_3864_; uint8_t v___x_3865_; 
v___x_3864_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__19));
lean_inc(v_invClause_3847_);
v___x_3865_ = l_Lean_Syntax_isOfKind(v_invClause_3847_, v___x_3864_);
if (v___x_3865_ == 0)
{
lean_object* v___x_3866_; 
lean_dec(v_invClause_3847_);
v___x_3866_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg();
return v___x_3866_;
}
else
{
lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; uint8_t v___x_3870_; 
v___x_3867_ = lean_unsigned_to_nat(1u);
v___x_3868_ = l_Lean_Syntax_getArg(v_invClause_3847_, v___x_3867_);
lean_dec(v_invClause_3847_);
v___x_3869_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__3));
lean_inc(v___x_3868_);
v___x_3870_ = l_Lean_Syntax_isOfKind(v___x_3868_, v___x_3869_);
if (v___x_3870_ == 0)
{
lean_object* v___x_3871_; 
lean_dec(v___x_3868_);
v___x_3871_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg();
return v___x_3871_;
}
else
{
lean_object* v___x_3872_; lean_object* v___x_3873_; uint8_t v___x_3874_; 
v___x_3872_ = lean_unsigned_to_nat(0u);
v___x_3873_ = l_Lean_Syntax_getArg(v___x_3868_, v___x_3867_);
v___x_3874_ = l_Lean_Syntax_matchesNull(v___x_3873_, v___x_3872_);
if (v___x_3874_ == 0)
{
lean_object* v___x_3875_; 
lean_dec(v___x_3868_);
v___x_3875_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg();
return v___x_3875_;
}
else
{
lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v_body_3878_; lean_object* v_binders_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; 
v___x_3876_ = l_Lean_Syntax_getArg(v___x_3868_, v___x_3872_);
v___x_3877_ = lean_unsigned_to_nat(3u);
v_body_3878_ = l_Lean_Syntax_getArg(v___x_3868_, v___x_3877_);
lean_dec(v___x_3868_);
v_binders_3879_ = l_Lean_Syntax_getArgs(v___x_3876_);
lean_dec(v___x_3876_);
v___x_3880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3880_, 0, v_binders_3879_);
lean_ctor_set(v___x_3880_, 1, v_body_3878_);
v___x_3881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3880_);
return v___x_3881_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant___boxed(lean_object* v_invClause_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_){
_start:
{
lean_object* v_res_3914_; 
v_res_3914_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant(v_invClause_3905_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_);
lean_dec(v_a_3912_);
lean_dec_ref(v_a_3911_);
lean_dec(v_a_3910_);
lean_dec_ref(v_a_3909_);
lean_dec(v_a_3908_);
lean_dec_ref(v_a_3907_);
lean_dec_ref(v_a_3906_);
return v_res_3914_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__7(void){
_start:
{
lean_object* v___x_3930_; lean_object* v___x_3931_; 
v___x_3930_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__6));
v___x_3931_ = l_Lean_stringToMessageData(v___x_3930_);
return v___x_3931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant(lean_object* v_g_3932_, lean_object* v_invClause_3933_, lean_object* v_h_x3f_3934_, lean_object* v_00_u03b1_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_){
_start:
{
lean_object* v___y_3945_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3952_; lean_object* v___y_3953_; lean_object* v___x_3958_; 
lean_inc(v_invClause_3933_);
v___x_3958_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant(v_invClause_3933_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_);
if (lean_obj_tag(v___x_3958_) == 0)
{
lean_object* v_a_3959_; lean_object* v_fst_3960_; lean_object* v_snd_3961_; lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_4060_; 
v_a_3959_ = lean_ctor_get(v___x_3958_, 0);
lean_inc(v_a_3959_);
lean_dec_ref_known(v___x_3958_, 1);
v_fst_3960_ = lean_ctor_get(v_a_3959_, 0);
v_snd_3961_ = lean_ctor_get(v_a_3959_, 1);
v_isSharedCheck_4060_ = !lean_is_exclusive(v_a_3959_);
if (v_isSharedCheck_4060_ == 0)
{
v___x_3963_ = v_a_3959_;
v_isShared_3964_ = v_isSharedCheck_4060_;
goto v_resetjp_3962_;
}
else
{
lean_inc(v_snd_3961_);
lean_inc(v_fst_3960_);
lean_dec(v_a_3959_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_4060_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_4032_; 
if (lean_obj_tag(v_h_x3f_3934_) == 0)
{
lean_object* v___x_4057_; 
v___x_4057_ = lean_box(0);
v___y_4032_ = v___x_4057_;
goto v___jp_4031_;
}
else
{
lean_object* v_val_4058_; lean_object* v___x_4059_; 
v_val_4058_ = lean_ctor_get(v_h_x3f_3934_, 0);
lean_inc(v_val_4058_);
v___x_4059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4059_, 0, v_val_4058_);
v___y_4032_ = v___x_4059_;
goto v___jp_4031_;
}
v___jp_3965_:
{
lean_object* v___x_3973_; 
v___x_3973_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f(v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_);
if (lean_obj_tag(v___x_3973_) == 0)
{
lean_object* v_a_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; 
v_a_3974_ = lean_ctor_get(v___x_3973_, 0);
lean_inc_n(v_a_3974_, 2);
lean_dec_ref_known(v___x_3973_, 1);
v___x_3975_ = lean_unsigned_to_nat(2u);
v___x_3976_ = lean_unsigned_to_nat(0u);
v___x_3977_ = l_Array_extract___redArg(v_fst_3960_, v___x_3976_, v___x_3975_);
v___x_3978_ = lean_array_get_size(v_fst_3960_);
v___x_3979_ = l_Array_extract___redArg(v_fst_3960_, v___x_3975_, v___x_3978_);
lean_dec(v_fst_3960_);
v___x_3980_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__0));
v___x_3981_ = lean_array_get_size(v___x_3979_);
v___x_3982_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders(v_invClause_3933_, v___x_3980_, v___x_3981_, v_a_3974_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_);
if (lean_obj_tag(v___x_3982_) == 0)
{
lean_object* v___x_3983_; 
lean_dec_ref_known(v___x_3982_, 1);
v___x_3983_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun(v___x_3979_, v_snd_3961_, v_a_3974_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_);
lean_dec(v_a_3974_);
lean_dec_ref(v___x_3979_);
if (lean_obj_tag(v___x_3983_) == 0)
{
lean_object* v_a_3984_; lean_object* v___x_3985_; lean_object* v_a_3986_; lean_object* v_ref_3987_; uint8_t v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3993_; 
v_a_3984_ = lean_ctor_get(v___x_3983_, 0);
lean_inc(v_a_3984_);
lean_dec_ref_known(v___x_3983_, 1);
lean_inc_ref(v_g_3932_);
v___x_3985_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkStateFun___redArg(v_g_3932_, v_a_3984_, v___y_3971_);
v_a_3986_ = lean_ctor_get(v___x_3985_, 0);
lean_inc(v_a_3986_);
lean_dec_ref(v___x_3985_);
v_ref_3987_ = lean_ctor_get(v___y_3971_, 5);
v___x_3988_ = 0;
v___x_3989_ = l_Lean_SourceInfo_fromRef(v_ref_3987_, v___x_3988_);
v___x_3990_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__0));
v___x_3991_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__1));
lean_inc(v___x_3989_);
if (v_isShared_3964_ == 0)
{
lean_ctor_set_tag(v___x_3963_, 2);
lean_ctor_set(v___x_3963_, 1, v___x_3990_);
lean_ctor_set(v___x_3963_, 0, v___x_3989_);
v___x_3993_ = v___x_3963_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v___x_3989_);
lean_ctor_set(v_reuseFailAlloc_4006_, 1, v___x_3990_);
v___x_3993_ = v_reuseFailAlloc_4006_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; 
v___x_3994_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__3));
v___x_3995_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_3996_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_3997_ = l_Array_append___redArg(v___x_3996_, v___x_3977_);
lean_dec_ref(v___x_3977_);
lean_inc_n(v___x_3989_, 4);
v___x_3998_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3989_);
lean_ctor_set(v___x_3998_, 1, v___x_3995_);
lean_ctor_set(v___x_3998_, 2, v___x_3997_);
v___x_3999_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3989_);
lean_ctor_set(v___x_3999_, 1, v___x_3995_);
lean_ctor_set(v___x_3999_, 2, v___x_3996_);
v___x_4000_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_4001_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4001_, 0, v___x_3989_);
lean_ctor_set(v___x_4001_, 1, v___x_4000_);
v___x_4002_ = l_Lean_Syntax_node4(v___x_3989_, v___x_3994_, v___x_3998_, v___x_3999_, v___x_4001_, v_a_3986_);
v___x_4003_ = l_Lean_Syntax_node2(v___x_3989_, v___x_3991_, v___x_3993_, v___x_4002_);
if (lean_obj_tag(v_h_x3f_3934_) == 0)
{
lean_object* v___x_4004_; 
v___x_4004_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__3));
v___y_3945_ = v___y_3967_;
v___y_3946_ = v___y_3969_;
v___y_3947_ = v___y_3971_;
v___y_3948_ = v___y_3968_;
v___y_3949_ = v___y_3966_;
v___y_3950_ = v___y_3972_;
v___y_3951_ = v___x_4003_;
v___y_3952_ = v___y_3970_;
v___y_3953_ = v___x_4004_;
goto v___jp_3944_;
}
else
{
lean_object* v___x_4005_; 
v___x_4005_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__5));
v___y_3945_ = v___y_3967_;
v___y_3946_ = v___y_3969_;
v___y_3947_ = v___y_3971_;
v___y_3948_ = v___y_3968_;
v___y_3949_ = v___y_3966_;
v___y_3950_ = v___y_3972_;
v___y_3951_ = v___x_4003_;
v___y_3952_ = v___y_3970_;
v___y_3953_ = v___x_4005_;
goto v___jp_3944_;
}
}
}
else
{
lean_object* v_a_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4014_; 
lean_dec_ref(v___x_3977_);
lean_del_object(v___x_3963_);
lean_dec(v_invClause_3933_);
lean_dec_ref(v_g_3932_);
v_a_4007_ = lean_ctor_get(v___x_3983_, 0);
v_isSharedCheck_4014_ = !lean_is_exclusive(v___x_3983_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_4009_ = v___x_3983_;
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_a_4007_);
lean_dec(v___x_3983_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4012_; 
if (v_isShared_4010_ == 0)
{
v___x_4012_ = v___x_4009_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v_a_4007_);
v___x_4012_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
return v___x_4012_;
}
}
}
}
else
{
lean_object* v_a_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4022_; 
lean_dec_ref(v___x_3979_);
lean_dec_ref(v___x_3977_);
lean_dec(v_a_3974_);
lean_del_object(v___x_3963_);
lean_dec(v_snd_3961_);
lean_dec(v_invClause_3933_);
lean_dec_ref(v_g_3932_);
v_a_4015_ = lean_ctor_get(v___x_3982_, 0);
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_3982_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_4017_ = v___x_3982_;
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_a_4015_);
lean_dec(v___x_3982_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v___x_4020_; 
if (v_isShared_4018_ == 0)
{
v___x_4020_ = v___x_4017_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v_a_4015_);
v___x_4020_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
return v___x_4020_;
}
}
}
}
else
{
lean_object* v_a_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4030_; 
lean_del_object(v___x_3963_);
lean_dec(v_snd_3961_);
lean_dec(v_fst_3960_);
lean_dec(v_invClause_3933_);
lean_dec_ref(v_g_3932_);
v_a_4023_ = lean_ctor_get(v___x_3973_, 0);
v_isSharedCheck_4030_ = !lean_is_exclusive(v___x_3973_);
if (v_isSharedCheck_4030_ == 0)
{
v___x_4025_ = v___x_3973_;
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_a_4023_);
lean_dec(v___x_3973_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v___x_4028_; 
if (v_isShared_4026_ == 0)
{
v___x_4028_ = v___x_4025_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v_a_4023_);
v___x_4028_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
return v___x_4028_;
}
}
}
}
v___jp_4031_:
{
lean_object* v_xs_4033_; lean_object* v_monadInfo_4034_; lean_object* v___x_4035_; 
v_xs_4033_ = lean_ctor_get(v_g_3932_, 0);
v_monadInfo_4034_ = lean_ctor_get(v_a_3936_, 0);
lean_inc_ref(v_monadInfo_4034_);
lean_inc_ref(v_xs_4033_);
v___x_4035_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkPureForIn___redArg(v_invClause_3933_, v___y_4032_, v_xs_4033_, v_00_u03b1_3935_, v_monadInfo_4034_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_);
lean_dec(v___y_4032_);
if (lean_obj_tag(v___x_4035_) == 0)
{
lean_object* v___x_4036_; lean_object* v___x_4037_; uint8_t v___x_4038_; 
lean_dec_ref_known(v___x_4035_, 1);
v___x_4036_ = lean_unsigned_to_nat(2u);
v___x_4037_ = lean_array_get_size(v_fst_3960_);
v___x_4038_ = lean_nat_dec_le(v___x_4036_, v___x_4037_);
if (v___x_4038_ == 0)
{
lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v_a_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4048_; 
lean_del_object(v___x_3963_);
lean_dec(v_snd_3961_);
lean_dec(v_fst_3960_);
lean_dec_ref(v_g_3932_);
v___x_4039_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__7, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__7_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__7);
v___x_4040_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0___redArg(v_invClause_3933_, v___x_4039_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_);
lean_dec(v_invClause_3933_);
v_a_4041_ = lean_ctor_get(v___x_4040_, 0);
v_isSharedCheck_4048_ = !lean_is_exclusive(v___x_4040_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4043_ = v___x_4040_;
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_a_4041_);
lean_dec(v___x_4040_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4046_; 
if (v_isShared_4044_ == 0)
{
v___x_4046_ = v___x_4043_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_a_4041_);
v___x_4046_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
return v___x_4046_;
}
}
}
else
{
v___y_3966_ = v_a_3936_;
v___y_3967_ = v_a_3937_;
v___y_3968_ = v_a_3938_;
v___y_3969_ = v_a_3939_;
v___y_3970_ = v_a_3940_;
v___y_3971_ = v_a_3941_;
v___y_3972_ = v_a_3942_;
goto v___jp_3965_;
}
}
else
{
lean_object* v_a_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4056_; 
lean_del_object(v___x_3963_);
lean_dec(v_snd_3961_);
lean_dec(v_fst_3960_);
lean_dec(v_invClause_3933_);
lean_dec_ref(v_g_3932_);
v_a_4049_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4056_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4056_ == 0)
{
v___x_4051_ = v___x_4035_;
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_a_4049_);
lean_dec(v___x_4035_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v___x_4054_; 
if (v_isShared_4052_ == 0)
{
v___x_4054_ = v___x_4051_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_a_4049_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
}
}
}
}
else
{
lean_object* v_a_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4068_; 
lean_dec_ref(v_00_u03b1_3935_);
lean_dec(v_invClause_3933_);
lean_dec_ref(v_g_3932_);
v_a_4061_ = lean_ctor_get(v___x_3958_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_3958_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4063_ = v___x_3958_;
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_a_4061_);
lean_dec(v___x_3958_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v___x_4066_; 
if (v_isShared_4064_ == 0)
{
v___x_4066_ = v___x_4063_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_a_4061_);
v___x_4066_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
return v___x_4066_;
}
}
}
v___jp_3944_:
{
lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; 
v___x_3954_ = lean_unsigned_to_nat(1u);
v___x_3955_ = lean_mk_empty_array_with_capacity(v___x_3954_);
v___x_3956_ = lean_array_push(v___x_3955_, v___y_3951_);
lean_inc(v___y_3953_);
v___x_3957_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall(v_g_3932_, v_invClause_3933_, v___y_3953_, v___x_3956_, v___y_3949_, v___y_3945_, v___y_3948_, v___y_3946_, v___y_3952_, v___y_3947_, v___y_3950_);
lean_dec_ref(v___x_3956_);
lean_dec(v_invClause_3933_);
return v___x_3957_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___boxed(lean_object* v_g_4069_, lean_object* v_invClause_4070_, lean_object* v_h_x3f_4071_, lean_object* v_00_u03b1_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_){
_start:
{
lean_object* v_res_4081_; 
v_res_4081_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant(v_g_4069_, v_invClause_4070_, v_h_x3f_4071_, v_00_u03b1_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_, v_a_4078_, v_a_4079_);
lean_dec(v_a_4079_);
lean_dec_ref(v_a_4078_);
lean_dec(v_a_4077_);
lean_dec_ref(v_a_4076_);
lean_dec(v_a_4075_);
lean_dec_ref(v_a_4074_);
lean_dec_ref(v_a_4073_);
lean_dec(v_h_x3f_4071_);
return v_res_4081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__0(lean_object* v_val_4083_, lean_object* v_a_4084_, lean_object* v_g_4085_, lean_object* v_____x_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_){
_start:
{
lean_object* v_fst_4095_; lean_object* v_snd_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4133_; 
v_fst_4095_ = lean_ctor_get(v_____x_4086_, 0);
v_snd_4096_ = lean_ctor_get(v_____x_4086_, 1);
v_isSharedCheck_4133_ = !lean_is_exclusive(v_____x_4086_);
if (v_isSharedCheck_4133_ == 0)
{
v___x_4098_ = v_____x_4086_;
v_isShared_4099_ = v_isSharedCheck_4133_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_snd_4096_);
lean_inc(v_fst_4095_);
lean_dec(v_____x_4086_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4133_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; 
v___x_4100_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__0___closed__0));
v___x_4101_ = lean_array_get_size(v_fst_4095_);
lean_inc(v_a_4084_);
v___x_4102_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders(v_val_4083_, v___x_4100_, v___x_4101_, v_a_4084_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_);
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_object* v___x_4103_; 
lean_dec_ref_known(v___x_4102_, 1);
v___x_4103_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun(v_fst_4095_, v_snd_4096_, v_a_4084_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_);
lean_dec(v_a_4084_);
lean_dec(v_fst_4095_);
if (lean_obj_tag(v___x_4103_) == 0)
{
lean_object* v_a_4104_; lean_object* v___x_4105_; lean_object* v_a_4106_; lean_object* v___x_4108_; uint8_t v_isShared_4109_; uint8_t v_isSharedCheck_4116_; 
v_a_4104_ = lean_ctor_get(v___x_4103_, 0);
lean_inc(v_a_4104_);
lean_dec_ref_known(v___x_4103_, 1);
v___x_4105_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkStateFun___redArg(v_g_4085_, v_a_4104_, v___y_4092_);
v_a_4106_ = lean_ctor_get(v___x_4105_, 0);
v_isSharedCheck_4116_ = !lean_is_exclusive(v___x_4105_);
if (v_isSharedCheck_4116_ == 0)
{
v___x_4108_ = v___x_4105_;
v_isShared_4109_ = v_isSharedCheck_4116_;
goto v_resetjp_4107_;
}
else
{
lean_inc(v_a_4106_);
lean_dec(v___x_4105_);
v___x_4108_ = lean_box(0);
v_isShared_4109_ = v_isSharedCheck_4116_;
goto v_resetjp_4107_;
}
v_resetjp_4107_:
{
lean_object* v___x_4111_; 
if (v_isShared_4099_ == 0)
{
lean_ctor_set(v___x_4098_, 1, v_a_4106_);
lean_ctor_set(v___x_4098_, 0, v_val_4083_);
v___x_4111_ = v___x_4098_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v_val_4083_);
lean_ctor_set(v_reuseFailAlloc_4115_, 1, v_a_4106_);
v___x_4111_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
lean_object* v___x_4113_; 
if (v_isShared_4109_ == 0)
{
lean_ctor_set(v___x_4108_, 0, v___x_4111_);
v___x_4113_ = v___x_4108_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v___x_4111_);
v___x_4113_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
return v___x_4113_;
}
}
}
}
else
{
lean_object* v_a_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4124_; 
lean_del_object(v___x_4098_);
lean_dec_ref(v_g_4085_);
lean_dec(v_val_4083_);
v_a_4117_ = lean_ctor_get(v___x_4103_, 0);
v_isSharedCheck_4124_ = !lean_is_exclusive(v___x_4103_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4119_ = v___x_4103_;
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_a_4117_);
lean_dec(v___x_4103_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
lean_object* v___x_4122_; 
if (v_isShared_4120_ == 0)
{
v___x_4122_ = v___x_4119_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_a_4117_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
return v___x_4122_;
}
}
}
}
else
{
lean_object* v_a_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4132_; 
lean_del_object(v___x_4098_);
lean_dec(v_snd_4096_);
lean_dec(v_fst_4095_);
lean_dec_ref(v_g_4085_);
lean_dec(v_a_4084_);
lean_dec(v_val_4083_);
v_a_4125_ = lean_ctor_get(v___x_4102_, 0);
v_isSharedCheck_4132_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4132_ == 0)
{
v___x_4127_ = v___x_4102_;
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_a_4125_);
lean_dec(v___x_4102_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
lean_object* v___x_4130_; 
if (v_isShared_4128_ == 0)
{
v___x_4130_ = v___x_4127_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_a_4125_);
v___x_4130_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
return v___x_4130_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__0___boxed(lean_object* v_val_4134_, lean_object* v_a_4135_, lean_object* v_g_4136_, lean_object* v_____x_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__0(v_val_4134_, v_a_4135_, v_g_4136_, v_____x_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_);
lean_dec(v___y_4144_);
lean_dec_ref(v___y_4143_);
lean_dec(v___y_4142_);
lean_dec_ref(v___y_4141_);
lean_dec(v___y_4140_);
lean_dec_ref(v___y_4139_);
lean_dec_ref(v___y_4138_);
return v_res_4146_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__3(void){
_start:
{
lean_object* v___x_4154_; lean_object* v___x_4155_; 
v___x_4154_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__2));
v___x_4155_ = l_Lean_mkIdent(v___x_4154_);
return v___x_4155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1(lean_object* v___x_4156_, lean_object* v___x_4157_, lean_object* v___x_4158_, lean_object* v_g_4159_, uint8_t v___x_4160_, lean_object* v___x_4161_, lean_object* v_val_4162_, lean_object* v_invBody_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_){
_start:
{
lean_object* v_ref_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v_statePat_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; 
v_ref_4172_ = lean_ctor_get(v___y_4169_, 5);
v___x_4173_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__0));
lean_inc_ref_n(v___x_4158_, 2);
lean_inc_ref_n(v___x_4157_, 2);
lean_inc_ref_n(v___x_4156_, 2);
v___x_4174_ = l_Lean_Name_mkStr4(v___x_4156_, v___x_4157_, v___x_4158_, v___x_4173_);
v_statePat_4175_ = lean_ctor_get(v_g_4159_, 4);
lean_inc(v_statePat_4175_);
lean_dec_ref(v_g_4159_);
v___x_4176_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__0));
v___x_4177_ = l_Lean_Name_mkStr4(v___x_4156_, v___x_4157_, v___x_4158_, v___x_4176_);
v___x_4178_ = l_Lean_SourceInfo_fromRef(v_ref_4172_, v___x_4160_);
v___x_4179_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__3, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___closed__3);
v___x_4180_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
lean_inc_n(v___x_4178_, 7);
v___x_4181_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4181_, 0, v___x_4178_);
lean_ctor_set(v___x_4181_, 1, v___x_4176_);
v___x_4182_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__2));
v___x_4183_ = l_Lean_Name_mkStr4(v___x_4156_, v___x_4157_, v___x_4158_, v___x_4182_);
v___x_4184_ = l_Lean_Syntax_node2(v___x_4178_, v___x_4180_, v___x_4161_, v_statePat_4175_);
v___x_4185_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
v___x_4186_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4186_, 0, v___x_4178_);
lean_ctor_set(v___x_4186_, 1, v___x_4180_);
lean_ctor_set(v___x_4186_, 2, v___x_4185_);
v___x_4187_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_4188_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4188_, 0, v___x_4178_);
lean_ctor_set(v___x_4188_, 1, v___x_4187_);
v___x_4189_ = l_Lean_Syntax_node4(v___x_4178_, v___x_4183_, v___x_4184_, v___x_4186_, v___x_4188_, v_invBody_4163_);
v___x_4190_ = l_Lean_Syntax_node2(v___x_4178_, v___x_4177_, v___x_4181_, v___x_4189_);
v___x_4191_ = l_Lean_Syntax_node1(v___x_4178_, v___x_4180_, v___x_4190_);
v___x_4192_ = l_Lean_Syntax_node2(v___x_4178_, v___x_4174_, v___x_4179_, v___x_4191_);
v___x_4193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4193_, 0, v_val_4162_);
lean_ctor_set(v___x_4193_, 1, v___x_4192_);
v___x_4194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4194_, 0, v___x_4193_);
return v___x_4194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1___boxed(lean_object* v___x_4195_, lean_object* v___x_4196_, lean_object* v___x_4197_, lean_object* v_g_4198_, lean_object* v___x_4199_, lean_object* v___x_4200_, lean_object* v_val_4201_, lean_object* v_invBody_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_){
_start:
{
uint8_t v___x_16888__boxed_4211_; lean_object* v_res_4212_; 
v___x_16888__boxed_4211_ = lean_unbox(v___x_4199_);
v_res_4212_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1(v___x_4195_, v___x_4196_, v___x_4197_, v_g_4198_, v___x_16888__boxed_4211_, v___x_4200_, v_val_4201_, v_invBody_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
lean_dec(v___y_4209_);
lean_dec_ref(v___y_4208_);
lean_dec(v___y_4207_);
lean_dec_ref(v___y_4206_);
lean_dec(v___y_4205_);
lean_dec_ref(v___y_4204_);
lean_dec_ref(v___y_4203_);
return v_res_4212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget(lean_object* v_g_4239_, lean_object* v_inv_x3f_4240_, lean_object* v_dec_x3f_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_){
_start:
{
lean_object* v_fst_4251_; lean_object* v_fst_4252_; lean_object* v_snd_4253_; lean_object* v___y_4273_; lean_object* v_a_4274_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___x_4313_; 
v___x_4313_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f(v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_);
if (lean_obj_tag(v___x_4313_) == 0)
{
lean_object* v_a_4314_; lean_object* v_a_4316_; lean_object* v___y_4350_; 
v_a_4314_ = lean_ctor_get(v___x_4313_, 0);
lean_inc(v_a_4314_);
lean_dec_ref_known(v___x_4313_, 1);
if (lean_obj_tag(v_inv_x3f_4240_) == 0)
{
lean_object* v___x_4359_; 
v___x_4359_ = lean_box(0);
v_a_4316_ = v___x_4359_;
goto v___jp_4315_;
}
else
{
lean_object* v_val_4360_; lean_object* v___x_4361_; 
v_val_4360_ = lean_ctor_get(v_inv_x3f_4240_, 0);
lean_inc_n(v_val_4360_, 2);
lean_dec_ref_known(v_inv_x3f_4240_, 1);
v___x_4361_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant(v_val_4360_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_);
if (lean_obj_tag(v___x_4361_) == 0)
{
lean_object* v_a_4362_; lean_object* v_fst_4363_; lean_object* v_snd_4364_; lean_object* v___x_4366_; uint8_t v_isShared_4367_; uint8_t v_isSharedCheck_4442_; 
v_a_4362_ = lean_ctor_get(v___x_4361_, 0);
lean_inc(v_a_4362_);
lean_dec_ref_known(v___x_4361_, 1);
v_fst_4363_ = lean_ctor_get(v_a_4362_, 0);
v_snd_4364_ = lean_ctor_get(v_a_4362_, 1);
v_isSharedCheck_4442_ = !lean_is_exclusive(v_a_4362_);
if (v_isSharedCheck_4442_ == 0)
{
v___x_4366_ = v_a_4362_;
v_isShared_4367_ = v_isSharedCheck_4442_;
goto v_resetjp_4365_;
}
else
{
lean_inc(v_snd_4364_);
lean_inc(v_fst_4363_);
lean_dec(v_a_4362_);
v___x_4366_ = lean_box(0);
v_isShared_4367_ = v_isSharedCheck_4442_;
goto v_resetjp_4365_;
}
v_resetjp_4365_:
{
lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; 
v___x_4368_ = lean_unsigned_to_nat(1u);
v___x_4369_ = lean_array_get_size(v_fst_4363_);
v___x_4370_ = l_Array_extract___redArg(v_fst_4363_, v___x_4368_, v___x_4369_);
v___x_4371_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant___closed__0));
v___x_4372_ = lean_array_get_size(v___x_4370_);
lean_inc(v_a_4314_);
v___x_4373_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders(v_val_4360_, v___x_4371_, v___x_4372_, v_a_4314_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_);
if (lean_obj_tag(v___x_4373_) == 0)
{
lean_object* v___x_4374_; 
lean_dec_ref_known(v___x_4373_, 1);
v___x_4374_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun(v___x_4370_, v_snd_4364_, v_a_4314_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_);
lean_dec_ref(v___x_4370_);
if (lean_obj_tag(v___x_4374_) == 0)
{
lean_object* v_a_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; 
v_a_4375_ = lean_ctor_get(v___x_4374_, 0);
lean_inc(v_a_4375_);
lean_dec_ref_known(v___x_4374_, 1);
v___x_4376_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__7));
v___x_4377_ = l_Lean_Core_mkFreshUserName(v___x_4376_, v_a_4247_, v_a_4248_);
if (lean_obj_tag(v___x_4377_) == 0)
{
lean_object* v_a_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; uint8_t v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; uint8_t v___x_4388_; 
v_a_4378_ = lean_ctor_get(v___x_4377_, 0);
lean_inc(v_a_4378_);
lean_dec_ref_known(v___x_4377_, 1);
v___x_4379_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0));
v___x_4380_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1));
v___x_4381_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2));
v___x_4382_ = lean_box(0);
v___x_4383_ = lean_unsigned_to_nat(0u);
v___x_4384_ = lean_array_get(v___x_4382_, v_fst_4363_, v___x_4383_);
lean_dec(v_fst_4363_);
v___x_4385_ = 0;
v___x_4386_ = l_Lean_mkIdentFrom(v_val_4360_, v_a_4378_, v___x_4385_);
v___x_4387_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__10));
lean_inc(v___x_4384_);
v___x_4388_ = l_Lean_Syntax_isOfKind(v___x_4384_, v___x_4387_);
if (v___x_4388_ == 0)
{
lean_object* v_ref_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4394_; 
v_ref_4389_ = lean_ctor_get(v_a_4247_, 5);
v___x_4390_ = l_Lean_SourceInfo_fromRef(v_ref_4389_, v___x_4388_);
v___x_4391_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30));
v___x_4392_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__8));
lean_inc(v___x_4390_);
if (v_isShared_4367_ == 0)
{
lean_ctor_set_tag(v___x_4366_, 2);
lean_ctor_set(v___x_4366_, 1, v___x_4391_);
lean_ctor_set(v___x_4366_, 0, v___x_4390_);
v___x_4394_ = v___x_4366_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v___x_4390_);
lean_ctor_set(v_reuseFailAlloc_4416_, 1, v___x_4391_);
v___x_4394_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; 
v___x_4395_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13));
v___x_4396_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
lean_inc_n(v___x_4390_, 11);
v___x_4397_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4397_, 0, v___x_4390_);
lean_ctor_set(v___x_4397_, 1, v___x_4395_);
lean_ctor_set(v___x_4397_, 2, v___x_4396_);
v___x_4398_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__12));
lean_inc(v___x_4386_);
lean_inc_ref_n(v___x_4397_, 2);
v___x_4399_ = l_Lean_Syntax_node2(v___x_4390_, v___x_4398_, v___x_4397_, v___x_4386_);
v___x_4400_ = l_Lean_Syntax_node1(v___x_4390_, v___x_4395_, v___x_4399_);
v___x_4401_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39));
v___x_4402_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4402_, 0, v___x_4390_);
lean_ctor_set(v___x_4402_, 1, v___x_4401_);
v___x_4403_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__13));
v___x_4404_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__14));
v___x_4405_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42));
v___x_4406_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4406_, 0, v___x_4390_);
lean_ctor_set(v___x_4406_, 1, v___x_4405_);
v___x_4407_ = l_Lean_Syntax_node1(v___x_4390_, v___x_4395_, v___x_4384_);
v___x_4408_ = l_Lean_Syntax_node1(v___x_4390_, v___x_4395_, v___x_4407_);
v___x_4409_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50));
v___x_4410_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4410_, 0, v___x_4390_);
lean_ctor_set(v___x_4410_, 1, v___x_4409_);
v___x_4411_ = l_Lean_Syntax_node4(v___x_4390_, v___x_4404_, v___x_4406_, v___x_4408_, v___x_4410_, v_a_4375_);
v___x_4412_ = l_Lean_Syntax_node1(v___x_4390_, v___x_4395_, v___x_4411_);
v___x_4413_ = l_Lean_Syntax_node1(v___x_4390_, v___x_4403_, v___x_4412_);
v___x_4414_ = l_Lean_Syntax_node6(v___x_4390_, v___x_4392_, v___x_4394_, v___x_4397_, v___x_4397_, v___x_4400_, v___x_4402_, v___x_4413_);
lean_inc_ref(v_g_4239_);
v___x_4415_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1(v___x_4379_, v___x_4380_, v___x_4381_, v_g_4239_, v___x_4385_, v___x_4386_, v_val_4360_, v___x_4414_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_);
v___y_4350_ = v___x_4415_;
goto v___jp_4349_;
}
}
else
{
lean_object* v___x_4417_; 
lean_dec(v___x_4384_);
lean_del_object(v___x_4366_);
lean_inc_ref(v_g_4239_);
v___x_4417_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__1(v___x_4379_, v___x_4380_, v___x_4381_, v_g_4239_, v___x_4385_, v___x_4386_, v_val_4360_, v_a_4375_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_);
v___y_4350_ = v___x_4417_;
goto v___jp_4349_;
}
}
else
{
lean_object* v_a_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4425_; 
lean_dec(v_a_4375_);
lean_del_object(v___x_4366_);
lean_dec(v_fst_4363_);
lean_dec(v_val_4360_);
lean_dec(v_a_4314_);
lean_dec(v_dec_x3f_4241_);
lean_dec_ref(v_g_4239_);
v_a_4418_ = lean_ctor_get(v___x_4377_, 0);
v_isSharedCheck_4425_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4425_ == 0)
{
v___x_4420_ = v___x_4377_;
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
else
{
lean_inc(v_a_4418_);
lean_dec(v___x_4377_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v___x_4423_; 
if (v_isShared_4421_ == 0)
{
v___x_4423_ = v___x_4420_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4424_; 
v_reuseFailAlloc_4424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4424_, 0, v_a_4418_);
v___x_4423_ = v_reuseFailAlloc_4424_;
goto v_reusejp_4422_;
}
v_reusejp_4422_:
{
return v___x_4423_;
}
}
}
}
else
{
lean_object* v_a_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4433_; 
lean_del_object(v___x_4366_);
lean_dec(v_fst_4363_);
lean_dec(v_val_4360_);
lean_dec(v_a_4314_);
lean_dec(v_dec_x3f_4241_);
lean_dec_ref(v_g_4239_);
v_a_4426_ = lean_ctor_get(v___x_4374_, 0);
v_isSharedCheck_4433_ = !lean_is_exclusive(v___x_4374_);
if (v_isSharedCheck_4433_ == 0)
{
v___x_4428_ = v___x_4374_;
v_isShared_4429_ = v_isSharedCheck_4433_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_a_4426_);
lean_dec(v___x_4374_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4433_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v___x_4431_; 
if (v_isShared_4429_ == 0)
{
v___x_4431_ = v___x_4428_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v_a_4426_);
v___x_4431_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
return v___x_4431_;
}
}
}
}
else
{
lean_object* v_a_4434_; lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4441_; 
lean_dec_ref(v___x_4370_);
lean_del_object(v___x_4366_);
lean_dec(v_snd_4364_);
lean_dec(v_fst_4363_);
lean_dec(v_val_4360_);
lean_dec(v_a_4314_);
lean_dec(v_dec_x3f_4241_);
lean_dec_ref(v_g_4239_);
v_a_4434_ = lean_ctor_get(v___x_4373_, 0);
v_isSharedCheck_4441_ = !lean_is_exclusive(v___x_4373_);
if (v_isSharedCheck_4441_ == 0)
{
v___x_4436_ = v___x_4373_;
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
else
{
lean_inc(v_a_4434_);
lean_dec(v___x_4373_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
v_resetjp_4435_:
{
lean_object* v___x_4439_; 
if (v_isShared_4437_ == 0)
{
v___x_4439_ = v___x_4436_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v_a_4434_);
v___x_4439_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
return v___x_4439_;
}
}
}
}
}
else
{
lean_object* v_a_4443_; lean_object* v___x_4445_; uint8_t v_isShared_4446_; uint8_t v_isSharedCheck_4450_; 
lean_dec(v_val_4360_);
lean_dec(v_a_4314_);
lean_dec(v_dec_x3f_4241_);
lean_dec_ref(v_g_4239_);
v_a_4443_ = lean_ctor_get(v___x_4361_, 0);
v_isSharedCheck_4450_ = !lean_is_exclusive(v___x_4361_);
if (v_isSharedCheck_4450_ == 0)
{
v___x_4445_ = v___x_4361_;
v_isShared_4446_ = v_isSharedCheck_4450_;
goto v_resetjp_4444_;
}
else
{
lean_inc(v_a_4443_);
lean_dec(v___x_4361_);
v___x_4445_ = lean_box(0);
v_isShared_4446_ = v_isSharedCheck_4450_;
goto v_resetjp_4444_;
}
v_resetjp_4444_:
{
lean_object* v___x_4448_; 
if (v_isShared_4446_ == 0)
{
v___x_4448_ = v___x_4445_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4449_; 
v_reuseFailAlloc_4449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4449_, 0, v_a_4443_);
v___x_4448_ = v_reuseFailAlloc_4449_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
return v___x_4448_;
}
}
}
}
v___jp_4315_:
{
if (lean_obj_tag(v_dec_x3f_4241_) == 0)
{
lean_object* v___x_4317_; 
lean_dec(v_a_4314_);
v___x_4317_ = lean_box(0);
v___y_4273_ = v_a_4316_;
v_a_4274_ = v___x_4317_;
goto v___jp_4272_;
}
else
{
lean_object* v_val_4318_; lean_object* v___x_4319_; uint8_t v___x_4320_; 
v_val_4318_ = lean_ctor_get(v_dec_x3f_4241_, 0);
lean_inc_n(v_val_4318_, 2);
lean_dec_ref_known(v_dec_x3f_4241_, 1);
v___x_4319_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
v___x_4320_ = l_Lean_Syntax_isOfKind(v_val_4318_, v___x_4319_);
if (v___x_4320_ == 0)
{
lean_object* v___x_4321_; lean_object* v_a_4322_; lean_object* v___x_4324_; uint8_t v_isShared_4325_; uint8_t v_isSharedCheck_4329_; 
lean_dec(v_val_4318_);
lean_dec(v_a_4316_);
lean_dec(v_a_4314_);
lean_dec_ref(v_g_4239_);
v___x_4321_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg();
v_a_4322_ = lean_ctor_get(v___x_4321_, 0);
v_isSharedCheck_4329_ = !lean_is_exclusive(v___x_4321_);
if (v_isSharedCheck_4329_ == 0)
{
v___x_4324_ = v___x_4321_;
v_isShared_4325_ = v_isSharedCheck_4329_;
goto v_resetjp_4323_;
}
else
{
lean_inc(v_a_4322_);
lean_dec(v___x_4321_);
v___x_4324_ = lean_box(0);
v_isShared_4325_ = v_isSharedCheck_4329_;
goto v_resetjp_4323_;
}
v_resetjp_4323_:
{
lean_object* v___x_4327_; 
if (v_isShared_4325_ == 0)
{
v___x_4327_ = v___x_4324_;
goto v_reusejp_4326_;
}
else
{
lean_object* v_reuseFailAlloc_4328_; 
v_reuseFailAlloc_4328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4328_, 0, v_a_4322_);
v___x_4327_ = v_reuseFailAlloc_4328_;
goto v_reusejp_4326_;
}
v_reusejp_4326_:
{
return v___x_4327_;
}
}
}
else
{
lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; uint8_t v___x_4333_; 
v___x_4330_ = lean_unsigned_to_nat(1u);
v___x_4331_ = l_Lean_Syntax_getArg(v_val_4318_, v___x_4330_);
v___x_4332_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkAssertionFun___closed__3));
lean_inc(v___x_4331_);
v___x_4333_ = l_Lean_Syntax_isOfKind(v___x_4331_, v___x_4332_);
if (v___x_4333_ == 0)
{
lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; 
v___x_4334_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_4335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4335_, 0, v___x_4334_);
lean_ctor_set(v___x_4335_, 1, v___x_4331_);
lean_inc_ref(v_g_4239_);
v___x_4336_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__0(v_val_4318_, v_a_4314_, v_g_4239_, v___x_4335_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_);
v___y_4301_ = v_a_4316_;
v___y_4302_ = v___x_4336_;
goto v___jp_4300_;
}
else
{
lean_object* v___x_4337_; lean_object* v___x_4338_; uint8_t v___x_4339_; 
v___x_4337_ = lean_unsigned_to_nat(0u);
v___x_4338_ = l_Lean_Syntax_getArg(v___x_4331_, v___x_4330_);
v___x_4339_ = l_Lean_Syntax_matchesNull(v___x_4338_, v___x_4337_);
if (v___x_4339_ == 0)
{
lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; 
v___x_4340_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__9));
v___x_4341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4341_, 0, v___x_4340_);
lean_ctor_set(v___x_4341_, 1, v___x_4331_);
lean_inc_ref(v_g_4239_);
v___x_4342_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__0(v_val_4318_, v_a_4314_, v_g_4239_, v___x_4341_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_);
v___y_4301_ = v_a_4316_;
v___y_4302_ = v___x_4342_;
goto v___jp_4300_;
}
else
{
lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; 
v___x_4343_ = l_Lean_Syntax_getArg(v___x_4331_, v___x_4337_);
v___x_4344_ = lean_unsigned_to_nat(3u);
v___x_4345_ = l_Lean_Syntax_getArg(v___x_4331_, v___x_4344_);
lean_dec(v___x_4331_);
v___x_4346_ = l_Lean_Syntax_getArgs(v___x_4343_);
lean_dec(v___x_4343_);
v___x_4347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4347_, 0, v___x_4346_);
lean_ctor_set(v___x_4347_, 1, v___x_4345_);
lean_inc_ref(v_g_4239_);
v___x_4348_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___lam__0(v_val_4318_, v_a_4314_, v_g_4239_, v___x_4347_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_);
v___y_4301_ = v_a_4316_;
v___y_4302_ = v___x_4348_;
goto v___jp_4300_;
}
}
}
}
}
v___jp_4349_:
{
lean_object* v_a_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4358_; 
v_a_4351_ = lean_ctor_get(v___y_4350_, 0);
v_isSharedCheck_4358_ = !lean_is_exclusive(v___y_4350_);
if (v_isSharedCheck_4358_ == 0)
{
v___x_4353_ = v___y_4350_;
v_isShared_4354_ = v_isSharedCheck_4358_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_a_4351_);
lean_dec(v___y_4350_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4358_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
lean_object* v___x_4356_; 
if (v_isShared_4354_ == 0)
{
lean_ctor_set_tag(v___x_4353_, 1);
v___x_4356_ = v___x_4353_;
goto v_reusejp_4355_;
}
else
{
lean_object* v_reuseFailAlloc_4357_; 
v_reuseFailAlloc_4357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4357_, 0, v_a_4351_);
v___x_4356_ = v_reuseFailAlloc_4357_;
goto v_reusejp_4355_;
}
v_reusejp_4355_:
{
v_a_4316_ = v___x_4356_;
goto v___jp_4315_;
}
}
}
}
else
{
lean_dec(v_dec_x3f_4241_);
lean_dec(v_inv_x3f_4240_);
lean_dec_ref(v_g_4239_);
return v___x_4313_;
}
v___jp_4250_:
{
lean_object* v___x_4254_; 
lean_inc(v_fst_4252_);
v___x_4254_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_ForInApp_mkCall(v_g_4239_, v_fst_4251_, v_fst_4252_, v_snd_4253_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_);
lean_dec_ref(v_snd_4253_);
lean_dec(v_fst_4251_);
if (lean_obj_tag(v___x_4254_) == 0)
{
lean_object* v_a_4255_; lean_object* v___x_4257_; uint8_t v_isShared_4258_; uint8_t v_isSharedCheck_4263_; 
v_a_4255_ = lean_ctor_get(v___x_4254_, 0);
v_isSharedCheck_4263_ = !lean_is_exclusive(v___x_4254_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4257_ = v___x_4254_;
v_isShared_4258_ = v_isSharedCheck_4263_;
goto v_resetjp_4256_;
}
else
{
lean_inc(v_a_4255_);
lean_dec(v___x_4254_);
v___x_4257_ = lean_box(0);
v_isShared_4258_ = v_isSharedCheck_4263_;
goto v_resetjp_4256_;
}
v_resetjp_4256_:
{
lean_object* v___x_4259_; lean_object* v___x_4261_; 
v___x_4259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4259_, 0, v_a_4255_);
if (v_isShared_4258_ == 0)
{
lean_ctor_set(v___x_4257_, 0, v___x_4259_);
v___x_4261_ = v___x_4257_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v___x_4259_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
return v___x_4261_;
}
}
}
else
{
lean_object* v_a_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4271_; 
v_a_4264_ = lean_ctor_get(v___x_4254_, 0);
v_isSharedCheck_4271_ = !lean_is_exclusive(v___x_4254_);
if (v_isSharedCheck_4271_ == 0)
{
v___x_4266_ = v___x_4254_;
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_a_4264_);
lean_dec(v___x_4254_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4269_; 
if (v_isShared_4267_ == 0)
{
v___x_4269_ = v___x_4266_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v_a_4264_);
v___x_4269_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
return v___x_4269_;
}
}
}
}
v___jp_4272_:
{
if (lean_obj_tag(v___y_4273_) == 0)
{
if (lean_obj_tag(v_a_4274_) == 0)
{
lean_object* v___x_4275_; lean_object* v___x_4276_; 
lean_dec_ref(v_g_4239_);
v___x_4275_ = lean_box(0);
v___x_4276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4276_, 0, v___x_4275_);
return v___x_4276_;
}
else
{
lean_object* v_val_4277_; lean_object* v_fst_4278_; lean_object* v_snd_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; 
v_val_4277_ = lean_ctor_get(v_a_4274_, 0);
lean_inc(v_val_4277_);
lean_dec_ref_known(v_a_4274_, 1);
v_fst_4278_ = lean_ctor_get(v_val_4277_, 0);
lean_inc(v_fst_4278_);
v_snd_4279_ = lean_ctor_get(v_val_4277_, 1);
lean_inc(v_snd_4279_);
lean_dec(v_val_4277_);
v___x_4280_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__1));
v___x_4281_ = lean_unsigned_to_nat(1u);
v___x_4282_ = lean_mk_empty_array_with_capacity(v___x_4281_);
v___x_4283_ = lean_array_push(v___x_4282_, v_snd_4279_);
v_fst_4251_ = v_fst_4278_;
v_fst_4252_ = v___x_4280_;
v_snd_4253_ = v___x_4283_;
goto v___jp_4250_;
}
}
else
{
lean_object* v_val_4284_; 
v_val_4284_ = lean_ctor_get(v___y_4273_, 0);
lean_inc(v_val_4284_);
lean_dec_ref_known(v___y_4273_, 1);
if (lean_obj_tag(v_a_4274_) == 0)
{
lean_object* v_fst_4285_; lean_object* v_snd_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; 
v_fst_4285_ = lean_ctor_get(v_val_4284_, 0);
lean_inc(v_fst_4285_);
v_snd_4286_ = lean_ctor_get(v_val_4284_, 1);
lean_inc(v_snd_4286_);
lean_dec(v_val_4284_);
v___x_4287_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__3));
v___x_4288_ = lean_unsigned_to_nat(1u);
v___x_4289_ = lean_mk_empty_array_with_capacity(v___x_4288_);
v___x_4290_ = lean_array_push(v___x_4289_, v_snd_4286_);
v_fst_4251_ = v_fst_4285_;
v_fst_4252_ = v___x_4287_;
v_snd_4253_ = v___x_4290_;
goto v___jp_4250_;
}
else
{
lean_object* v_val_4291_; lean_object* v_fst_4292_; lean_object* v_snd_4293_; lean_object* v_snd_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; 
v_val_4291_ = lean_ctor_get(v_a_4274_, 0);
lean_inc(v_val_4291_);
lean_dec_ref_known(v_a_4274_, 1);
v_fst_4292_ = lean_ctor_get(v_val_4284_, 0);
lean_inc(v_fst_4292_);
v_snd_4293_ = lean_ctor_get(v_val_4284_, 1);
lean_inc(v_snd_4293_);
lean_dec(v_val_4284_);
v_snd_4294_ = lean_ctor_get(v_val_4291_, 1);
lean_inc(v_snd_4294_);
lean_dec(v_val_4291_);
v___x_4295_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___closed__5));
v___x_4296_ = lean_unsigned_to_nat(2u);
v___x_4297_ = lean_mk_empty_array_with_capacity(v___x_4296_);
v___x_4298_ = lean_array_push(v___x_4297_, v_snd_4293_);
v___x_4299_ = lean_array_push(v___x_4298_, v_snd_4294_);
v_fst_4251_ = v_fst_4292_;
v_fst_4252_ = v___x_4295_;
v_snd_4253_ = v___x_4299_;
goto v___jp_4250_;
}
}
}
v___jp_4300_:
{
if (lean_obj_tag(v___y_4302_) == 0)
{
lean_object* v_a_4303_; lean_object* v___x_4304_; 
v_a_4303_ = lean_ctor_get(v___y_4302_, 0);
lean_inc(v_a_4303_);
lean_dec_ref_known(v___y_4302_, 1);
v___x_4304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4304_, 0, v_a_4303_);
v___y_4273_ = v___y_4301_;
v_a_4274_ = v___x_4304_;
goto v___jp_4272_;
}
else
{
lean_object* v_a_4305_; lean_object* v___x_4307_; uint8_t v_isShared_4308_; uint8_t v_isSharedCheck_4312_; 
lean_dec(v___y_4301_);
lean_dec_ref(v_g_4239_);
v_a_4305_ = lean_ctor_get(v___y_4302_, 0);
v_isSharedCheck_4312_ = !lean_is_exclusive(v___y_4302_);
if (v_isSharedCheck_4312_ == 0)
{
v___x_4307_ = v___y_4302_;
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
else
{
lean_inc(v_a_4305_);
lean_dec(v___y_4302_);
v___x_4307_ = lean_box(0);
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
v_resetjp_4306_:
{
lean_object* v___x_4310_; 
if (v_isShared_4308_ == 0)
{
v___x_4310_ = v___x_4307_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v_a_4305_);
v___x_4310_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
return v___x_4310_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget___boxed(lean_object* v_g_4451_, lean_object* v_inv_x3f_4452_, lean_object* v_dec_x3f_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_){
_start:
{
lean_object* v_res_4462_; 
v_res_4462_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget(v_g_4451_, v_inv_x3f_4452_, v_dec_x3f_4453_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_);
lean_dec(v_a_4460_);
lean_dec_ref(v_a_4459_);
lean_dec(v_a_4458_);
lean_dec_ref(v_a_4457_);
lean_dec(v_a_4456_);
lean_dec_ref(v_a_4455_);
lean_dec_ref(v_a_4454_);
return v_res_4462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0(lean_object* v_k_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v_b_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_){
_start:
{
lean_object* v___x_4473_; 
lean_inc(v___y_4471_);
lean_inc_ref(v___y_4470_);
lean_inc(v___y_4469_);
lean_inc_ref(v___y_4468_);
lean_inc(v___y_4466_);
lean_inc_ref(v___y_4465_);
lean_inc_ref(v___y_4464_);
v___x_4473_ = lean_apply_9(v_k_4463_, v_b_4467_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_, lean_box(0));
return v___x_4473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0___boxed(lean_object* v_k_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v_b_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_){
_start:
{
lean_object* v_res_4484_; 
v_res_4484_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0(v_k_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v_b_4478_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_);
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
lean_dec(v___y_4477_);
lean_dec_ref(v___y_4476_);
lean_dec_ref(v___y_4475_);
return v_res_4484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(lean_object* v_name_4485_, uint8_t v_bi_4486_, lean_object* v_type_4487_, lean_object* v_k_4488_, uint8_t v_kind_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_){
_start:
{
lean_object* v___f_4498_; lean_object* v___x_4499_; 
lean_inc(v___y_4492_);
lean_inc_ref(v___y_4491_);
lean_inc_ref(v___y_4490_);
v___f_4498_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_4498_, 0, v_k_4488_);
lean_closure_set(v___f_4498_, 1, v___y_4490_);
lean_closure_set(v___f_4498_, 2, v___y_4491_);
lean_closure_set(v___f_4498_, 3, v___y_4492_);
v___x_4499_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4485_, v_bi_4486_, v_type_4487_, v___f_4498_, v_kind_4489_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_);
if (lean_obj_tag(v___x_4499_) == 0)
{
return v___x_4499_;
}
else
{
lean_object* v_a_4500_; lean_object* v___x_4502_; uint8_t v_isShared_4503_; uint8_t v_isSharedCheck_4507_; 
v_a_4500_ = lean_ctor_get(v___x_4499_, 0);
v_isSharedCheck_4507_ = !lean_is_exclusive(v___x_4499_);
if (v_isSharedCheck_4507_ == 0)
{
v___x_4502_ = v___x_4499_;
v_isShared_4503_ = v_isSharedCheck_4507_;
goto v_resetjp_4501_;
}
else
{
lean_inc(v_a_4500_);
lean_dec(v___x_4499_);
v___x_4502_ = lean_box(0);
v_isShared_4503_ = v_isSharedCheck_4507_;
goto v_resetjp_4501_;
}
v_resetjp_4501_:
{
lean_object* v___x_4505_; 
if (v_isShared_4503_ == 0)
{
v___x_4505_ = v___x_4502_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_a_4500_);
v___x_4505_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
return v___x_4505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___boxed(lean_object* v_name_4508_, lean_object* v_bi_4509_, lean_object* v_type_4510_, lean_object* v_k_4511_, lean_object* v_kind_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_){
_start:
{
uint8_t v_bi_boxed_4521_; uint8_t v_kind_boxed_4522_; lean_object* v_res_4523_; 
v_bi_boxed_4521_ = lean_unbox(v_bi_4509_);
v_kind_boxed_4522_ = lean_unbox(v_kind_4512_);
v_res_4523_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_name_4508_, v_bi_boxed_4521_, v_type_4510_, v_k_4511_, v_kind_boxed_4522_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
lean_dec(v___y_4519_);
lean_dec_ref(v___y_4518_);
lean_dec(v___y_4517_);
lean_dec_ref(v___y_4516_);
lean_dec(v___y_4515_);
lean_dec_ref(v___y_4514_);
lean_dec_ref(v___y_4513_);
return v_res_4523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3(lean_object* v_00_u03b1_4524_, lean_object* v_name_4525_, uint8_t v_bi_4526_, lean_object* v_type_4527_, lean_object* v_k_4528_, uint8_t v_kind_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_){
_start:
{
lean_object* v___x_4538_; 
v___x_4538_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_name_4525_, v_bi_4526_, v_type_4527_, v_k_4528_, v_kind_4529_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_);
return v___x_4538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___boxed(lean_object* v_00_u03b1_4539_, lean_object* v_name_4540_, lean_object* v_bi_4541_, lean_object* v_type_4542_, lean_object* v_k_4543_, lean_object* v_kind_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_){
_start:
{
uint8_t v_bi_boxed_4553_; uint8_t v_kind_boxed_4554_; lean_object* v_res_4555_; 
v_bi_boxed_4553_ = lean_unbox(v_bi_4541_);
v_kind_boxed_4554_ = lean_unbox(v_kind_4544_);
v_res_4555_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3(v_00_u03b1_4539_, v_name_4540_, v_bi_boxed_4553_, v_type_4542_, v_k_4543_, v_kind_boxed_4554_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_);
lean_dec(v___y_4551_);
lean_dec_ref(v___y_4550_);
lean_dec(v___y_4549_);
lean_dec_ref(v___y_4548_);
lean_dec(v___y_4547_);
lean_dec_ref(v___y_4546_);
lean_dec_ref(v___y_4545_);
return v_res_4555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__0(lean_object* v_a_4556_, lean_object* v_x_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_){
_start:
{
lean_object* v___x_4566_; 
v___x_4566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4566_, 0, v_a_4556_);
return v___x_4566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__0___boxed(lean_object* v_a_4567_, lean_object* v_x_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_){
_start:
{
lean_object* v_res_4577_; 
v_res_4577_ = l_Lean_Elab_Do_elabDoFor___lam__0(v_a_4567_, v_x_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_);
lean_dec(v___y_4575_);
lean_dec_ref(v___y_4574_);
lean_dec(v___y_4573_);
lean_dec_ref(v___y_4572_);
lean_dec(v___y_4571_);
lean_dec_ref(v___y_4570_);
lean_dec_ref(v___y_4569_);
lean_dec_ref(v_x_4568_);
return v_res_4577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__2(lean_object* v_a_4578_, lean_object* v___x_4579_, uint8_t v___x_4580_, lean_object* v_r_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_){
_start:
{
lean_object* v_k_4590_; lean_object* v___x_4591_; 
v_k_4590_ = lean_ctor_get(v_a_4578_, 1);
lean_inc_ref(v_k_4590_);
lean_dec_ref(v_a_4578_);
lean_inc(v___y_4588_);
lean_inc_ref(v___y_4587_);
lean_inc(v___y_4586_);
lean_inc_ref(v___y_4585_);
lean_inc(v___y_4584_);
lean_inc_ref(v___y_4583_);
lean_inc_ref(v___y_4582_);
lean_inc_ref(v_r_4581_);
v___x_4591_ = lean_apply_9(v_k_4590_, v_r_4581_, v___y_4582_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_, lean_box(0));
if (lean_obj_tag(v___x_4591_) == 0)
{
lean_object* v_a_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; uint8_t v___x_4595_; uint8_t v___x_4596_; lean_object* v___x_4597_; 
v_a_4592_ = lean_ctor_get(v___x_4591_, 0);
lean_inc(v_a_4592_);
lean_dec_ref_known(v___x_4591_, 1);
v___x_4593_ = lean_mk_empty_array_with_capacity(v___x_4579_);
v___x_4594_ = lean_array_push(v___x_4593_, v_r_4581_);
v___x_4595_ = 0;
v___x_4596_ = 1;
v___x_4597_ = l_Lean_Meta_mkLambdaFVars(v___x_4594_, v_a_4592_, v___x_4595_, v___x_4580_, v___x_4595_, v___x_4580_, v___x_4596_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_);
lean_dec_ref(v___x_4594_);
return v___x_4597_;
}
else
{
lean_dec_ref(v_r_4581_);
return v___x_4591_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__2___boxed(lean_object* v_a_4598_, lean_object* v___x_4599_, lean_object* v___x_4600_, lean_object* v_r_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_){
_start:
{
uint8_t v___x_88512__boxed_4610_; lean_object* v_res_4611_; 
v___x_88512__boxed_4610_ = lean_unbox(v___x_4600_);
v_res_4611_ = l_Lean_Elab_Do_elabDoFor___lam__2(v_a_4598_, v___x_4599_, v___x_88512__boxed_4610_, v_r_4601_, v___y_4602_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_);
lean_dec(v___y_4608_);
lean_dec_ref(v___y_4607_);
lean_dec(v___y_4606_);
lean_dec_ref(v___y_4605_);
lean_dec(v___y_4604_);
lean_dec_ref(v___y_4603_);
lean_dec_ref(v___y_4602_);
lean_dec(v___x_4599_);
return v_res_4611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__0(lean_object* v___x_4612_, lean_object* v_as_4613_, size_t v_sz_4614_, size_t v_i_4615_, lean_object* v_b_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_){
_start:
{
uint8_t v___x_4624_; 
v___x_4624_ = lean_usize_dec_lt(v_i_4615_, v_sz_4614_);
if (v___x_4624_ == 0)
{
lean_object* v___x_4625_; 
lean_dec_ref(v___x_4612_);
v___x_4625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4625_, 0, v_b_4616_);
return v___x_4625_;
}
else
{
lean_object* v_a_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; 
v_a_4626_ = lean_array_uget_borrowed(v_as_4613_, v_i_4615_);
v___x_4627_ = l_Lean_Elab_Do_MutVar_getId(v_a_4626_);
v___x_4628_ = l_Lean_Meta_getLocalDeclFromUserName(v___x_4627_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_);
if (lean_obj_tag(v___x_4628_) == 0)
{
lean_object* v_a_4629_; lean_object* v_ident_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; uint8_t v___x_4634_; lean_object* v___x_4635_; 
v_a_4629_ = lean_ctor_get(v___x_4628_, 0);
lean_inc_n(v_a_4629_, 2);
lean_dec_ref_known(v___x_4628_, 1);
v_ident_4630_ = lean_ctor_get(v_a_4626_, 0);
v___x_4631_ = l_Lean_LocalDecl_toExpr(v_a_4629_);
v___x_4632_ = lean_box(0);
v___x_4633_ = lean_box(0);
v___x_4634_ = 0;
lean_inc_ref(v___x_4631_);
lean_inc(v_ident_4630_);
v___x_4635_ = l_Lean_Elab_Term_addTermInfo_x27(v_ident_4630_, v___x_4631_, v___x_4632_, v___x_4632_, v___x_4633_, v___x_4634_, v___x_4634_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_);
if (lean_obj_tag(v___x_4635_) == 0)
{
lean_object* v___x_4636_; lean_object* v___x_4637_; 
lean_dec_ref_known(v___x_4635_, 1);
v___x_4636_ = l_Lean_LocalDecl_type(v_a_4629_);
lean_dec(v_a_4629_);
v___x_4637_ = l_Lean_Meta_getDecLevel(v___x_4636_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_);
if (lean_obj_tag(v___x_4637_) == 0)
{
lean_object* v_a_4638_; lean_object* v_u_4639_; lean_object* v___x_4640_; 
v_a_4638_ = lean_ctor_get(v___x_4637_, 0);
lean_inc(v_a_4638_);
lean_dec_ref_known(v___x_4637_, 1);
v_u_4639_ = lean_ctor_get(v___x_4612_, 1);
lean_inc(v_u_4639_);
v___x_4640_ = l_Lean_Meta_isLevelDefEq(v_a_4638_, v_u_4639_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_);
if (lean_obj_tag(v___x_4640_) == 0)
{
lean_object* v___x_4641_; size_t v___x_4642_; size_t v___x_4643_; 
lean_dec_ref_known(v___x_4640_, 1);
v___x_4641_ = lean_array_push(v_b_4616_, v___x_4631_);
v___x_4642_ = ((size_t)1ULL);
v___x_4643_ = lean_usize_add(v_i_4615_, v___x_4642_);
v_i_4615_ = v___x_4643_;
v_b_4616_ = v___x_4641_;
goto _start;
}
else
{
lean_object* v_a_4645_; lean_object* v___x_4647_; uint8_t v_isShared_4648_; uint8_t v_isSharedCheck_4652_; 
lean_dec_ref(v___x_4631_);
lean_dec_ref(v_b_4616_);
lean_dec_ref(v___x_4612_);
v_a_4645_ = lean_ctor_get(v___x_4640_, 0);
v_isSharedCheck_4652_ = !lean_is_exclusive(v___x_4640_);
if (v_isSharedCheck_4652_ == 0)
{
v___x_4647_ = v___x_4640_;
v_isShared_4648_ = v_isSharedCheck_4652_;
goto v_resetjp_4646_;
}
else
{
lean_inc(v_a_4645_);
lean_dec(v___x_4640_);
v___x_4647_ = lean_box(0);
v_isShared_4648_ = v_isSharedCheck_4652_;
goto v_resetjp_4646_;
}
v_resetjp_4646_:
{
lean_object* v___x_4650_; 
if (v_isShared_4648_ == 0)
{
v___x_4650_ = v___x_4647_;
goto v_reusejp_4649_;
}
else
{
lean_object* v_reuseFailAlloc_4651_; 
v_reuseFailAlloc_4651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4651_, 0, v_a_4645_);
v___x_4650_ = v_reuseFailAlloc_4651_;
goto v_reusejp_4649_;
}
v_reusejp_4649_:
{
return v___x_4650_;
}
}
}
}
else
{
lean_object* v_a_4653_; lean_object* v___x_4655_; uint8_t v_isShared_4656_; uint8_t v_isSharedCheck_4660_; 
lean_dec_ref(v___x_4631_);
lean_dec_ref(v_b_4616_);
lean_dec_ref(v___x_4612_);
v_a_4653_ = lean_ctor_get(v___x_4637_, 0);
v_isSharedCheck_4660_ = !lean_is_exclusive(v___x_4637_);
if (v_isSharedCheck_4660_ == 0)
{
v___x_4655_ = v___x_4637_;
v_isShared_4656_ = v_isSharedCheck_4660_;
goto v_resetjp_4654_;
}
else
{
lean_inc(v_a_4653_);
lean_dec(v___x_4637_);
v___x_4655_ = lean_box(0);
v_isShared_4656_ = v_isSharedCheck_4660_;
goto v_resetjp_4654_;
}
v_resetjp_4654_:
{
lean_object* v___x_4658_; 
if (v_isShared_4656_ == 0)
{
v___x_4658_ = v___x_4655_;
goto v_reusejp_4657_;
}
else
{
lean_object* v_reuseFailAlloc_4659_; 
v_reuseFailAlloc_4659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4659_, 0, v_a_4653_);
v___x_4658_ = v_reuseFailAlloc_4659_;
goto v_reusejp_4657_;
}
v_reusejp_4657_:
{
return v___x_4658_;
}
}
}
}
else
{
lean_object* v_a_4661_; lean_object* v___x_4663_; uint8_t v_isShared_4664_; uint8_t v_isSharedCheck_4668_; 
lean_dec_ref(v___x_4631_);
lean_dec(v_a_4629_);
lean_dec_ref(v_b_4616_);
lean_dec_ref(v___x_4612_);
v_a_4661_ = lean_ctor_get(v___x_4635_, 0);
v_isSharedCheck_4668_ = !lean_is_exclusive(v___x_4635_);
if (v_isSharedCheck_4668_ == 0)
{
v___x_4663_ = v___x_4635_;
v_isShared_4664_ = v_isSharedCheck_4668_;
goto v_resetjp_4662_;
}
else
{
lean_inc(v_a_4661_);
lean_dec(v___x_4635_);
v___x_4663_ = lean_box(0);
v_isShared_4664_ = v_isSharedCheck_4668_;
goto v_resetjp_4662_;
}
v_resetjp_4662_:
{
lean_object* v___x_4666_; 
if (v_isShared_4664_ == 0)
{
v___x_4666_ = v___x_4663_;
goto v_reusejp_4665_;
}
else
{
lean_object* v_reuseFailAlloc_4667_; 
v_reuseFailAlloc_4667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4667_, 0, v_a_4661_);
v___x_4666_ = v_reuseFailAlloc_4667_;
goto v_reusejp_4665_;
}
v_reusejp_4665_:
{
return v___x_4666_;
}
}
}
}
else
{
lean_object* v_a_4669_; lean_object* v___x_4671_; uint8_t v_isShared_4672_; uint8_t v_isSharedCheck_4676_; 
lean_dec_ref(v_b_4616_);
lean_dec_ref(v___x_4612_);
v_a_4669_ = lean_ctor_get(v___x_4628_, 0);
v_isSharedCheck_4676_ = !lean_is_exclusive(v___x_4628_);
if (v_isSharedCheck_4676_ == 0)
{
v___x_4671_ = v___x_4628_;
v_isShared_4672_ = v_isSharedCheck_4676_;
goto v_resetjp_4670_;
}
else
{
lean_inc(v_a_4669_);
lean_dec(v___x_4628_);
v___x_4671_ = lean_box(0);
v_isShared_4672_ = v_isSharedCheck_4676_;
goto v_resetjp_4670_;
}
v_resetjp_4670_:
{
lean_object* v___x_4674_; 
if (v_isShared_4672_ == 0)
{
v___x_4674_ = v___x_4671_;
goto v_reusejp_4673_;
}
else
{
lean_object* v_reuseFailAlloc_4675_; 
v_reuseFailAlloc_4675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4675_, 0, v_a_4669_);
v___x_4674_ = v_reuseFailAlloc_4675_;
goto v_reusejp_4673_;
}
v_reusejp_4673_:
{
return v___x_4674_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__0___boxed(lean_object* v___x_4677_, lean_object* v_as_4678_, lean_object* v_sz_4679_, lean_object* v_i_4680_, lean_object* v_b_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_){
_start:
{
size_t v_sz_boxed_4689_; size_t v_i_boxed_4690_; lean_object* v_res_4691_; 
v_sz_boxed_4689_ = lean_unbox_usize(v_sz_4679_);
lean_dec(v_sz_4679_);
v_i_boxed_4690_ = lean_unbox_usize(v_i_4680_);
lean_dec(v_i_4680_);
v_res_4691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__0(v___x_4677_, v_as_4678_, v_sz_boxed_4689_, v_i_boxed_4690_, v_b_4681_, v___y_4682_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_);
lean_dec(v___y_4687_);
lean_dec_ref(v___y_4686_);
lean_dec(v___y_4685_);
lean_dec_ref(v___y_4684_);
lean_dec(v___y_4683_);
lean_dec_ref(v___y_4682_);
lean_dec_ref(v_as_4678_);
return v_res_4691_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_4692_; lean_object* v___x_4693_; 
v___x_4692_ = lean_box(1);
v___x_4693_ = l_Lean_MessageData_ofFormat(v___x_4692_);
return v___x_4693_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_4697_; lean_object* v___x_4698_; 
v___x_4697_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3___closed__2));
v___x_4698_ = l_Lean_MessageData_ofFormat(v___x_4697_);
return v___x_4698_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3(lean_object* v_x_4699_, lean_object* v_x_4700_){
_start:
{
if (lean_obj_tag(v_x_4700_) == 0)
{
return v_x_4699_;
}
else
{
lean_object* v_head_4701_; lean_object* v_tail_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4724_; 
v_head_4701_ = lean_ctor_get(v_x_4700_, 0);
v_tail_4702_ = lean_ctor_get(v_x_4700_, 1);
v_isSharedCheck_4724_ = !lean_is_exclusive(v_x_4700_);
if (v_isSharedCheck_4724_ == 0)
{
v___x_4704_ = v_x_4700_;
v_isShared_4705_ = v_isSharedCheck_4724_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_tail_4702_);
lean_inc(v_head_4701_);
lean_dec(v_x_4700_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4724_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v_before_4706_; lean_object* v___x_4708_; uint8_t v_isShared_4709_; uint8_t v_isSharedCheck_4722_; 
v_before_4706_ = lean_ctor_get(v_head_4701_, 0);
v_isSharedCheck_4722_ = !lean_is_exclusive(v_head_4701_);
if (v_isSharedCheck_4722_ == 0)
{
lean_object* v_unused_4723_; 
v_unused_4723_ = lean_ctor_get(v_head_4701_, 1);
lean_dec(v_unused_4723_);
v___x_4708_ = v_head_4701_;
v_isShared_4709_ = v_isSharedCheck_4722_;
goto v_resetjp_4707_;
}
else
{
lean_inc(v_before_4706_);
lean_dec(v_head_4701_);
v___x_4708_ = lean_box(0);
v_isShared_4709_ = v_isSharedCheck_4722_;
goto v_resetjp_4707_;
}
v_resetjp_4707_:
{
lean_object* v___x_4710_; lean_object* v___x_4712_; 
v___x_4710_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_4709_ == 0)
{
lean_ctor_set_tag(v___x_4708_, 7);
lean_ctor_set(v___x_4708_, 1, v___x_4710_);
lean_ctor_set(v___x_4708_, 0, v_x_4699_);
v___x_4712_ = v___x_4708_;
goto v_reusejp_4711_;
}
else
{
lean_object* v_reuseFailAlloc_4721_; 
v_reuseFailAlloc_4721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4721_, 0, v_x_4699_);
lean_ctor_set(v_reuseFailAlloc_4721_, 1, v___x_4710_);
v___x_4712_ = v_reuseFailAlloc_4721_;
goto v_reusejp_4711_;
}
v_reusejp_4711_:
{
lean_object* v___x_4713_; lean_object* v___x_4715_; 
v___x_4713_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3___closed__3);
if (v_isShared_4705_ == 0)
{
lean_ctor_set_tag(v___x_4704_, 7);
lean_ctor_set(v___x_4704_, 1, v___x_4713_);
lean_ctor_set(v___x_4704_, 0, v___x_4712_);
v___x_4715_ = v___x_4704_;
goto v_reusejp_4714_;
}
else
{
lean_object* v_reuseFailAlloc_4720_; 
v_reuseFailAlloc_4720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4720_, 0, v___x_4712_);
lean_ctor_set(v_reuseFailAlloc_4720_, 1, v___x_4713_);
v___x_4715_ = v_reuseFailAlloc_4720_;
goto v_reusejp_4714_;
}
v_reusejp_4714_:
{
lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; 
v___x_4716_ = l_Lean_MessageData_ofSyntax(v_before_4706_);
v___x_4717_ = l_Lean_indentD(v___x_4716_);
v___x_4718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4718_, 0, v___x_4715_);
lean_ctor_set(v___x_4718_, 1, v___x_4717_);
v_x_4699_ = v___x_4718_;
v_x_4700_ = v_tail_4702_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__10(lean_object* v_opts_4725_, lean_object* v_opt_4726_){
_start:
{
lean_object* v_name_4727_; lean_object* v_defValue_4728_; lean_object* v_map_4729_; lean_object* v___x_4730_; 
v_name_4727_ = lean_ctor_get(v_opt_4726_, 0);
v_defValue_4728_ = lean_ctor_get(v_opt_4726_, 1);
v_map_4729_ = lean_ctor_get(v_opts_4725_, 0);
v___x_4730_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4729_, v_name_4727_);
if (lean_obj_tag(v___x_4730_) == 0)
{
uint8_t v___x_4731_; 
v___x_4731_ = lean_unbox(v_defValue_4728_);
return v___x_4731_;
}
else
{
lean_object* v_val_4732_; 
v_val_4732_ = lean_ctor_get(v___x_4730_, 0);
lean_inc(v_val_4732_);
lean_dec_ref_known(v___x_4730_, 1);
if (lean_obj_tag(v_val_4732_) == 1)
{
uint8_t v_v_4733_; 
v_v_4733_ = lean_ctor_get_uint8(v_val_4732_, 0);
lean_dec_ref_known(v_val_4732_, 0);
return v_v_4733_;
}
else
{
uint8_t v___x_4734_; 
lean_dec(v_val_4732_);
v___x_4734_ = lean_unbox(v_defValue_4728_);
return v___x_4734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__10___boxed(lean_object* v_opts_4735_, lean_object* v_opt_4736_){
_start:
{
uint8_t v_res_4737_; lean_object* v_r_4738_; 
v_res_4737_ = l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__10(v_opts_4735_, v_opt_4736_);
lean_dec_ref(v_opt_4736_);
lean_dec_ref(v_opts_4735_);
v_r_4738_ = lean_box(v_res_4737_);
return v_r_4738_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_4742_; lean_object* v___x_4743_; 
v___x_4742_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__1));
v___x_4743_ = l_Lean_MessageData_ofFormat(v___x_4742_);
return v___x_4743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg(lean_object* v_msgData_4744_, lean_object* v_macroStack_4745_, lean_object* v___y_4746_){
_start:
{
lean_object* v_options_4748_; lean_object* v___x_4749_; uint8_t v___x_4750_; 
v_options_4748_ = lean_ctor_get(v___y_4746_, 2);
v___x_4749_ = l_Lean_Elab_pp_macroStack;
v___x_4750_ = l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__10(v_options_4748_, v___x_4749_);
if (v___x_4750_ == 0)
{
lean_object* v___x_4751_; 
lean_dec(v_macroStack_4745_);
v___x_4751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4751_, 0, v_msgData_4744_);
return v___x_4751_;
}
else
{
if (lean_obj_tag(v_macroStack_4745_) == 0)
{
lean_object* v___x_4752_; 
v___x_4752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4752_, 0, v_msgData_4744_);
return v___x_4752_;
}
else
{
lean_object* v_head_4753_; lean_object* v_after_4754_; lean_object* v___x_4756_; uint8_t v_isShared_4757_; uint8_t v_isSharedCheck_4769_; 
v_head_4753_ = lean_ctor_get(v_macroStack_4745_, 0);
lean_inc(v_head_4753_);
v_after_4754_ = lean_ctor_get(v_head_4753_, 1);
v_isSharedCheck_4769_ = !lean_is_exclusive(v_head_4753_);
if (v_isSharedCheck_4769_ == 0)
{
lean_object* v_unused_4770_; 
v_unused_4770_ = lean_ctor_get(v_head_4753_, 0);
lean_dec(v_unused_4770_);
v___x_4756_ = v_head_4753_;
v_isShared_4757_ = v_isSharedCheck_4769_;
goto v_resetjp_4755_;
}
else
{
lean_inc(v_after_4754_);
lean_dec(v_head_4753_);
v___x_4756_ = lean_box(0);
v_isShared_4757_ = v_isSharedCheck_4769_;
goto v_resetjp_4755_;
}
v_resetjp_4755_:
{
lean_object* v___x_4758_; lean_object* v___x_4760_; 
v___x_4758_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_4757_ == 0)
{
lean_ctor_set_tag(v___x_4756_, 7);
lean_ctor_set(v___x_4756_, 1, v___x_4758_);
lean_ctor_set(v___x_4756_, 0, v_msgData_4744_);
v___x_4760_ = v___x_4756_;
goto v_reusejp_4759_;
}
else
{
lean_object* v_reuseFailAlloc_4768_; 
v_reuseFailAlloc_4768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4768_, 0, v_msgData_4744_);
lean_ctor_set(v_reuseFailAlloc_4768_, 1, v___x_4758_);
v___x_4760_ = v_reuseFailAlloc_4768_;
goto v_reusejp_4759_;
}
v_reusejp_4759_:
{
lean_object* v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v_msgData_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; 
v___x_4761_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___closed__2);
v___x_4762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4762_, 0, v___x_4760_);
lean_ctor_set(v___x_4762_, 1, v___x_4761_);
v___x_4763_ = l_Lean_MessageData_ofSyntax(v_after_4754_);
v___x_4764_ = l_Lean_indentD(v___x_4763_);
v_msgData_4765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_4765_, 0, v___x_4762_);
lean_ctor_set(v_msgData_4765_, 1, v___x_4764_);
v___x_4766_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1_spec__3(v_msgData_4765_, v_macroStack_4745_);
v___x_4767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4767_, 0, v___x_4766_);
return v___x_4767_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_4771_, lean_object* v_macroStack_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_){
_start:
{
lean_object* v_res_4775_; 
v_res_4775_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg(v_msgData_4771_, v_macroStack_4772_, v___y_4773_);
lean_dec_ref(v___y_4773_);
return v_res_4775_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___redArg(lean_object* v_msg_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_){
_start:
{
lean_object* v_ref_4784_; lean_object* v___x_4785_; lean_object* v_a_4786_; lean_object* v_macroStack_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v_a_4790_; lean_object* v___x_4792_; uint8_t v_isShared_4793_; uint8_t v_isSharedCheck_4798_; 
v_ref_4784_ = lean_ctor_get(v___y_4781_, 5);
v___x_4785_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0_spec__1(v_msg_4776_, v___y_4779_, v___y_4780_, v___y_4781_, v___y_4782_);
v_a_4786_ = lean_ctor_get(v___x_4785_, 0);
lean_inc(v_a_4786_);
lean_dec_ref(v___x_4785_);
v_macroStack_4787_ = lean_ctor_get(v___y_4777_, 1);
v___x_4788_ = l_Lean_Elab_getBetterRef(v_ref_4784_, v_macroStack_4787_);
lean_inc(v_macroStack_4787_);
v___x_4789_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg(v_a_4786_, v_macroStack_4787_, v___y_4781_);
v_a_4790_ = lean_ctor_get(v___x_4789_, 0);
v_isSharedCheck_4798_ = !lean_is_exclusive(v___x_4789_);
if (v_isSharedCheck_4798_ == 0)
{
v___x_4792_ = v___x_4789_;
v_isShared_4793_ = v_isSharedCheck_4798_;
goto v_resetjp_4791_;
}
else
{
lean_inc(v_a_4790_);
lean_dec(v___x_4789_);
v___x_4792_ = lean_box(0);
v_isShared_4793_ = v_isSharedCheck_4798_;
goto v_resetjp_4791_;
}
v_resetjp_4791_:
{
lean_object* v___x_4794_; lean_object* v___x_4796_; 
v___x_4794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4794_, 0, v___x_4788_);
lean_ctor_set(v___x_4794_, 1, v_a_4790_);
if (v_isShared_4793_ == 0)
{
lean_ctor_set_tag(v___x_4792_, 1);
lean_ctor_set(v___x_4792_, 0, v___x_4794_);
v___x_4796_ = v___x_4792_;
goto v_reusejp_4795_;
}
else
{
lean_object* v_reuseFailAlloc_4797_; 
v_reuseFailAlloc_4797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4797_, 0, v___x_4794_);
v___x_4796_ = v_reuseFailAlloc_4797_;
goto v_reusejp_4795_;
}
v_reusejp_4795_:
{
return v___x_4796_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___redArg___boxed(lean_object* v_msg_4799_, lean_object* v___y_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_){
_start:
{
lean_object* v_res_4807_; 
v_res_4807_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___redArg(v_msg_4799_, v___y_4800_, v___y_4801_, v___y_4802_, v___y_4803_, v___y_4804_, v___y_4805_);
lean_dec(v___y_4805_);
lean_dec_ref(v___y_4804_);
lean_dec(v___y_4803_);
lean_dec_ref(v___y_4802_);
lean_dec(v___y_4801_);
lean_dec_ref(v___y_4800_);
return v_res_4807_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__1___closed__3(void){
_start:
{
lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; 
v___x_4813_ = lean_box(0);
v___x_4814_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__1___closed__2));
v___x_4815_ = l_Lean_mkConst(v___x_4814_, v___x_4813_);
return v___x_4815_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__1___closed__5(void){
_start:
{
lean_object* v___x_4817_; lean_object* v___x_4818_; 
v___x_4817_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__1___closed__4));
v___x_4818_ = l_Lean_stringToMessageData(v___x_4817_);
return v___x_4818_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__1___closed__7(void){
_start:
{
lean_object* v___x_4820_; lean_object* v___x_4821_; 
v___x_4820_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__1___closed__6));
v___x_4821_ = l_Lean_stringToMessageData(v___x_4820_);
return v___x_4821_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___lam__1___closed__10(void){
_start:
{
lean_object* v___x_4825_; lean_object* v___x_4826_; 
v___x_4825_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__1___closed__9));
v___x_4826_ = l_Lean_MessageData_ofFormat(v___x_4825_);
return v___x_4826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__1(lean_object* v___y_4827_, lean_object* v_monadInfo_4828_, uint8_t v_returnsEarly_4829_, lean_object* v___x_4830_, lean_object* v_a_4831_, uint8_t v___x_4832_, lean_object* v_e_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_){
_start:
{
lean_object* v_defs_4842_; lean_object* v___y_4843_; lean_object* v___y_4844_; lean_object* v___y_4845_; lean_object* v___y_4846_; lean_object* v___y_4847_; lean_object* v___y_4848_; lean_object* v___x_4865_; lean_object* v_returnVar_4867_; lean_object* v___y_4868_; lean_object* v___y_4869_; lean_object* v___y_4870_; lean_object* v___y_4871_; lean_object* v___y_4872_; lean_object* v___y_4873_; lean_object* v___y_4900_; lean_object* v___y_4901_; 
v___x_4865_ = lean_mk_empty_array_with_capacity(v___x_4830_);
if (lean_obj_tag(v_e_4833_) == 0)
{
if (v___x_4832_ == 0)
{
goto v___jp_4914_;
}
else
{
goto v___jp_4875_;
}
}
else
{
goto v___jp_4914_;
}
v___jp_4841_:
{
size_t v_sz_4849_; size_t v___x_4850_; lean_object* v___x_4851_; 
v_sz_4849_ = lean_array_size(v___y_4827_);
v___x_4850_ = ((size_t)0ULL);
v___x_4851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__0(v_monadInfo_4828_, v___y_4827_, v_sz_4849_, v___x_4850_, v_defs_4842_, v___y_4843_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_, v___y_4848_);
if (lean_obj_tag(v___x_4851_) == 0)
{
if (v_returnsEarly_4829_ == 0)
{
return v___x_4851_;
}
else
{
lean_object* v_a_4852_; lean_object* v___x_4853_; uint8_t v___x_4854_; 
v_a_4852_ = lean_ctor_get(v___x_4851_, 0);
lean_inc(v_a_4852_);
v___x_4853_ = lean_array_get_size(v___y_4827_);
v___x_4854_ = lean_nat_dec_eq(v___x_4853_, v___x_4830_);
if (v___x_4854_ == 0)
{
lean_dec(v_a_4852_);
return v___x_4851_;
}
else
{
lean_object* v___x_4856_; uint8_t v_isShared_4857_; uint8_t v_isSharedCheck_4863_; 
v_isSharedCheck_4863_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_4863_ == 0)
{
lean_object* v_unused_4864_; 
v_unused_4864_ = lean_ctor_get(v___x_4851_, 0);
lean_dec(v_unused_4864_);
v___x_4856_ = v___x_4851_;
v_isShared_4857_ = v_isSharedCheck_4863_;
goto v_resetjp_4855_;
}
else
{
lean_dec(v___x_4851_);
v___x_4856_ = lean_box(0);
v_isShared_4857_ = v_isSharedCheck_4863_;
goto v_resetjp_4855_;
}
v_resetjp_4855_:
{
lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4861_; 
v___x_4858_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__1___closed__3, &l_Lean_Elab_Do_elabDoFor___lam__1___closed__3_once, _init_l_Lean_Elab_Do_elabDoFor___lam__1___closed__3);
v___x_4859_ = lean_array_push(v_a_4852_, v___x_4858_);
if (v_isShared_4857_ == 0)
{
lean_ctor_set(v___x_4856_, 0, v___x_4859_);
v___x_4861_ = v___x_4856_;
goto v_reusejp_4860_;
}
else
{
lean_object* v_reuseFailAlloc_4862_; 
v_reuseFailAlloc_4862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4862_, 0, v___x_4859_);
v___x_4861_ = v_reuseFailAlloc_4862_;
goto v_reusejp_4860_;
}
v_reusejp_4860_:
{
return v___x_4861_;
}
}
}
}
}
else
{
return v___x_4851_;
}
}
v___jp_4866_:
{
lean_object* v___x_4874_; 
v___x_4874_ = lean_array_push(v___x_4865_, v_returnVar_4867_);
v_defs_4842_ = v___x_4874_;
v___y_4843_ = v___y_4868_;
v___y_4844_ = v___y_4869_;
v___y_4845_ = v___y_4870_;
v___y_4846_ = v___y_4871_;
v___y_4847_ = v___y_4872_;
v___y_4848_ = v___y_4873_;
goto v___jp_4841_;
}
v___jp_4875_:
{
if (v_returnsEarly_4829_ == 0)
{
lean_dec(v_e_4833_);
lean_dec_ref(v_a_4831_);
v_defs_4842_ = v___x_4865_;
v___y_4843_ = v___y_4834_;
v___y_4844_ = v___y_4835_;
v___y_4845_ = v___y_4836_;
v___y_4846_ = v___y_4837_;
v___y_4847_ = v___y_4838_;
v___y_4848_ = v___y_4839_;
goto v___jp_4841_;
}
else
{
if (lean_obj_tag(v_e_4833_) == 0)
{
lean_object* v_resultType_4876_; lean_object* v___x_4877_; 
v_resultType_4876_ = lean_ctor_get(v_a_4831_, 0);
lean_inc_ref(v_resultType_4876_);
lean_dec_ref(v_a_4831_);
v___x_4877_ = l_Lean_Meta_mkNone(v_resultType_4876_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_);
if (lean_obj_tag(v___x_4877_) == 0)
{
lean_object* v_a_4878_; 
v_a_4878_ = lean_ctor_get(v___x_4877_, 0);
lean_inc(v_a_4878_);
lean_dec_ref_known(v___x_4877_, 1);
v_returnVar_4867_ = v_a_4878_;
v___y_4868_ = v___y_4834_;
v___y_4869_ = v___y_4835_;
v___y_4870_ = v___y_4836_;
v___y_4871_ = v___y_4837_;
v___y_4872_ = v___y_4838_;
v___y_4873_ = v___y_4839_;
goto v___jp_4866_;
}
else
{
lean_object* v_a_4879_; lean_object* v___x_4881_; uint8_t v_isShared_4882_; uint8_t v_isSharedCheck_4886_; 
lean_dec_ref(v___x_4865_);
lean_dec_ref(v_monadInfo_4828_);
v_a_4879_ = lean_ctor_get(v___x_4877_, 0);
v_isSharedCheck_4886_ = !lean_is_exclusive(v___x_4877_);
if (v_isSharedCheck_4886_ == 0)
{
v___x_4881_ = v___x_4877_;
v_isShared_4882_ = v_isSharedCheck_4886_;
goto v_resetjp_4880_;
}
else
{
lean_inc(v_a_4879_);
lean_dec(v___x_4877_);
v___x_4881_ = lean_box(0);
v_isShared_4882_ = v_isSharedCheck_4886_;
goto v_resetjp_4880_;
}
v_resetjp_4880_:
{
lean_object* v___x_4884_; 
if (v_isShared_4882_ == 0)
{
v___x_4884_ = v___x_4881_;
goto v_reusejp_4883_;
}
else
{
lean_object* v_reuseFailAlloc_4885_; 
v_reuseFailAlloc_4885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4885_, 0, v_a_4879_);
v___x_4884_ = v_reuseFailAlloc_4885_;
goto v_reusejp_4883_;
}
v_reusejp_4883_:
{
return v___x_4884_;
}
}
}
}
else
{
lean_object* v_val_4887_; lean_object* v_resultType_4888_; lean_object* v___x_4889_; 
v_val_4887_ = lean_ctor_get(v_e_4833_, 0);
lean_inc(v_val_4887_);
lean_dec_ref_known(v_e_4833_, 1);
v_resultType_4888_ = lean_ctor_get(v_a_4831_, 0);
lean_inc_ref(v_resultType_4888_);
lean_dec_ref(v_a_4831_);
v___x_4889_ = l_Lean_Meta_mkSome(v_resultType_4888_, v_val_4887_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_);
if (lean_obj_tag(v___x_4889_) == 0)
{
lean_object* v_a_4890_; 
v_a_4890_ = lean_ctor_get(v___x_4889_, 0);
lean_inc(v_a_4890_);
lean_dec_ref_known(v___x_4889_, 1);
v_returnVar_4867_ = v_a_4890_;
v___y_4868_ = v___y_4834_;
v___y_4869_ = v___y_4835_;
v___y_4870_ = v___y_4836_;
v___y_4871_ = v___y_4837_;
v___y_4872_ = v___y_4838_;
v___y_4873_ = v___y_4839_;
goto v___jp_4866_;
}
else
{
lean_object* v_a_4891_; lean_object* v___x_4893_; uint8_t v_isShared_4894_; uint8_t v_isSharedCheck_4898_; 
lean_dec_ref(v___x_4865_);
lean_dec_ref(v_monadInfo_4828_);
v_a_4891_ = lean_ctor_get(v___x_4889_, 0);
v_isSharedCheck_4898_ = !lean_is_exclusive(v___x_4889_);
if (v_isSharedCheck_4898_ == 0)
{
v___x_4893_ = v___x_4889_;
v_isShared_4894_ = v_isSharedCheck_4898_;
goto v_resetjp_4892_;
}
else
{
lean_inc(v_a_4891_);
lean_dec(v___x_4889_);
v___x_4893_ = lean_box(0);
v_isShared_4894_ = v_isSharedCheck_4898_;
goto v_resetjp_4892_;
}
v_resetjp_4892_:
{
lean_object* v___x_4896_; 
if (v_isShared_4894_ == 0)
{
v___x_4896_ = v___x_4893_;
goto v_reusejp_4895_;
}
else
{
lean_object* v_reuseFailAlloc_4897_; 
v_reuseFailAlloc_4897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4897_, 0, v_a_4891_);
v___x_4896_ = v_reuseFailAlloc_4897_;
goto v_reusejp_4895_;
}
v_reusejp_4895_:
{
return v___x_4896_;
}
}
}
}
}
}
v___jp_4899_:
{
lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v_a_4906_; lean_object* v___x_4908_; uint8_t v_isShared_4909_; uint8_t v_isSharedCheck_4913_; 
lean_inc_ref(v___y_4900_);
v___x_4902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4902_, 0, v___y_4900_);
lean_ctor_set(v___x_4902_, 1, v___y_4901_);
v___x_4903_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__1___closed__5, &l_Lean_Elab_Do_elabDoFor___lam__1___closed__5_once, _init_l_Lean_Elab_Do_elabDoFor___lam__1___closed__5);
v___x_4904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4904_, 0, v___x_4902_);
lean_ctor_set(v___x_4904_, 1, v___x_4903_);
v___x_4905_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___redArg(v___x_4904_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_);
v_a_4906_ = lean_ctor_get(v___x_4905_, 0);
v_isSharedCheck_4913_ = !lean_is_exclusive(v___x_4905_);
if (v_isSharedCheck_4913_ == 0)
{
v___x_4908_ = v___x_4905_;
v_isShared_4909_ = v_isSharedCheck_4913_;
goto v_resetjp_4907_;
}
else
{
lean_inc(v_a_4906_);
lean_dec(v___x_4905_);
v___x_4908_ = lean_box(0);
v_isShared_4909_ = v_isSharedCheck_4913_;
goto v_resetjp_4907_;
}
v_resetjp_4907_:
{
lean_object* v___x_4911_; 
if (v_isShared_4909_ == 0)
{
v___x_4911_ = v___x_4908_;
goto v_reusejp_4910_;
}
else
{
lean_object* v_reuseFailAlloc_4912_; 
v_reuseFailAlloc_4912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4912_, 0, v_a_4906_);
v___x_4911_ = v_reuseFailAlloc_4912_;
goto v_reusejp_4910_;
}
v_reusejp_4910_:
{
return v___x_4911_;
}
}
}
v___jp_4914_:
{
if (v_returnsEarly_4829_ == 0)
{
lean_object* v___x_4915_; 
lean_dec_ref(v___x_4865_);
lean_dec_ref(v_a_4831_);
lean_dec_ref(v_monadInfo_4828_);
v___x_4915_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__1___closed__7, &l_Lean_Elab_Do_elabDoFor___lam__1___closed__7_once, _init_l_Lean_Elab_Do_elabDoFor___lam__1___closed__7);
if (lean_obj_tag(v_e_4833_) == 0)
{
lean_object* v___x_4916_; 
v___x_4916_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___lam__1___closed__10, &l_Lean_Elab_Do_elabDoFor___lam__1___closed__10_once, _init_l_Lean_Elab_Do_elabDoFor___lam__1___closed__10);
v___y_4900_ = v___x_4915_;
v___y_4901_ = v___x_4916_;
goto v___jp_4899_;
}
else
{
lean_object* v_val_4917_; lean_object* v___x_4918_; 
v_val_4917_ = lean_ctor_get(v_e_4833_, 0);
lean_inc(v_val_4917_);
lean_dec_ref_known(v_e_4833_, 1);
v___x_4918_ = l_Lean_MessageData_ofExpr(v_val_4917_);
v___y_4900_ = v___x_4915_;
v___y_4901_ = v___x_4918_;
goto v___jp_4899_;
}
}
else
{
goto v___jp_4875_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__1___boxed(lean_object* v___y_4919_, lean_object* v_monadInfo_4920_, lean_object* v_returnsEarly_4921_, lean_object* v___x_4922_, lean_object* v_a_4923_, lean_object* v___x_4924_, lean_object* v_e_4925_, lean_object* v___y_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_){
_start:
{
uint8_t v_returnsEarly_boxed_4933_; uint8_t v___x_88918__boxed_4934_; lean_object* v_res_4935_; 
v_returnsEarly_boxed_4933_ = lean_unbox(v_returnsEarly_4921_);
v___x_88918__boxed_4934_ = lean_unbox(v___x_4924_);
v_res_4935_ = l_Lean_Elab_Do_elabDoFor___lam__1(v___y_4919_, v_monadInfo_4920_, v_returnsEarly_boxed_4933_, v___x_4922_, v_a_4923_, v___x_88918__boxed_4934_, v_e_4925_, v___y_4926_, v___y_4927_, v___y_4928_, v___y_4929_, v___y_4930_, v___y_4931_);
lean_dec(v___y_4931_);
lean_dec_ref(v___y_4930_);
lean_dec(v___y_4929_);
lean_dec_ref(v___y_4928_);
lean_dec(v___y_4927_);
lean_dec_ref(v___y_4926_);
lean_dec(v___x_4922_);
lean_dec_ref(v___y_4919_);
return v_res_4935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(lean_object* v_name_4936_, lean_object* v_type_4937_, lean_object* v_k_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_){
_start:
{
uint8_t v___x_4947_; uint8_t v___x_4948_; lean_object* v___x_4949_; 
v___x_4947_ = 0;
v___x_4948_ = 0;
v___x_4949_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_name_4936_, v___x_4947_, v_type_4937_, v_k_4938_, v___x_4948_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_, v___y_4944_, v___y_4945_);
return v___x_4949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg___boxed(lean_object* v_name_4950_, lean_object* v_type_4951_, lean_object* v_k_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_){
_start:
{
lean_object* v_res_4961_; 
v_res_4961_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v_name_4950_, v_type_4951_, v_k_4952_, v___y_4953_, v___y_4954_, v___y_4955_, v___y_4956_, v___y_4957_, v___y_4958_, v___y_4959_);
lean_dec(v___y_4959_);
lean_dec_ref(v___y_4958_);
lean_dec(v___y_4957_);
lean_dec_ref(v___y_4956_);
lean_dec(v___y_4955_);
lean_dec_ref(v___y_4954_);
lean_dec_ref(v___y_4953_);
return v_res_4961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__3(uint8_t v_returnsEarly_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_, lean_object* v_doBlockResultType_4982_, lean_object* v_a_4983_, lean_object* v_v_4984_, lean_object* v_u_4985_, lean_object* v___f_4986_, lean_object* v___y_4987_, lean_object* v___x_4988_, lean_object* v___x_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_){
_start:
{
lean_object* v_ret_4999_; lean_object* v___y_5000_; lean_object* v___y_5001_; lean_object* v___y_5002_; lean_object* v___y_5003_; lean_object* v___y_5004_; lean_object* v___y_5005_; lean_object* v___y_5006_; 
if (v_returnsEarly_4979_ == 0)
{
lean_object* v___x_5053_; 
lean_dec_ref(v___f_4986_);
lean_dec(v_u_4985_);
lean_dec(v_v_4984_);
lean_dec_ref(v_a_4983_);
lean_dec_ref(v_doBlockResultType_4982_);
lean_dec(v_a_4981_);
v___x_5053_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_a_4980_, v___y_4990_, v___y_4991_, v___y_4992_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_);
return v___x_5053_;
}
else
{
lean_object* v___x_5054_; 
v___x_5054_ = l_Lean_Meta_getFVarFromUserName(v_a_4981_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_);
if (lean_obj_tag(v___x_5054_) == 0)
{
lean_object* v_a_5055_; lean_object* v___x_5056_; uint8_t v___x_5057_; 
v_a_5055_ = lean_ctor_get(v___x_5054_, 0);
lean_inc(v_a_5055_);
lean_dec_ref_known(v___x_5054_, 1);
v___x_5056_ = lean_array_get_size(v___y_4987_);
v___x_5057_ = lean_nat_dec_eq(v___x_5056_, v___x_4988_);
if (v___x_5057_ == 0)
{
v_ret_4999_ = v_a_5055_;
v___y_5000_ = v___y_4990_;
v___y_5001_ = v___y_4991_;
v___y_5002_ = v___y_4992_;
v___y_5003_ = v___y_4993_;
v___y_5004_ = v___y_4994_;
v___y_5005_ = v___y_4995_;
v___y_5006_ = v___y_4996_;
goto v___jp_4998_;
}
else
{
lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; 
v___x_5058_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__3___closed__9));
v___x_5059_ = lean_mk_empty_array_with_capacity(v___x_4989_);
v___x_5060_ = lean_array_push(v___x_5059_, v_a_5055_);
v___x_5061_ = l_Lean_Meta_mkAppM(v___x_5058_, v___x_5060_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_);
if (lean_obj_tag(v___x_5061_) == 0)
{
lean_object* v_a_5062_; 
v_a_5062_ = lean_ctor_get(v___x_5061_, 0);
lean_inc(v_a_5062_);
lean_dec_ref_known(v___x_5061_, 1);
v_ret_4999_ = v_a_5062_;
v___y_5000_ = v___y_4990_;
v___y_5001_ = v___y_4991_;
v___y_5002_ = v___y_4992_;
v___y_5003_ = v___y_4993_;
v___y_5004_ = v___y_4994_;
v___y_5005_ = v___y_4995_;
v___y_5006_ = v___y_4996_;
goto v___jp_4998_;
}
else
{
lean_dec_ref(v___f_4986_);
lean_dec(v_u_4985_);
lean_dec(v_v_4984_);
lean_dec_ref(v_a_4983_);
lean_dec_ref(v_doBlockResultType_4982_);
lean_dec_ref(v_a_4980_);
return v___x_5061_;
}
}
}
else
{
lean_dec_ref(v___f_4986_);
lean_dec(v_u_4985_);
lean_dec(v_v_4984_);
lean_dec_ref(v_a_4983_);
lean_dec_ref(v_doBlockResultType_4982_);
lean_dec_ref(v_a_4980_);
return v___x_5054_;
}
}
v___jp_4998_:
{
lean_object* v___x_5007_; 
lean_inc(v___y_5006_);
lean_inc_ref(v___y_5005_);
lean_inc(v___y_5004_);
lean_inc_ref(v___y_5003_);
lean_inc_ref(v_ret_4999_);
v___x_5007_ = lean_infer_type(v_ret_4999_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
if (lean_obj_tag(v___x_5007_) == 0)
{
lean_object* v_a_5008_; lean_object* v___x_5009_; 
v_a_5008_ = lean_ctor_get(v___x_5007_, 0);
lean_inc(v_a_5008_);
lean_dec_ref_known(v___x_5007_, 1);
v___x_5009_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_4982_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
if (lean_obj_tag(v___x_5009_) == 0)
{
lean_object* v_a_5010_; lean_object* v___x_5011_; 
v_a_5010_ = lean_ctor_get(v___x_5009_, 0);
lean_inc(v_a_5010_);
lean_dec_ref_known(v___x_5009_, 1);
v___x_5011_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(v_a_4980_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
if (lean_obj_tag(v___x_5011_) == 0)
{
lean_object* v_a_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; 
v_a_5012_ = lean_ctor_get(v___x_5011_, 0);
lean_inc(v_a_5012_);
lean_dec_ref_known(v___x_5011_, 1);
v___x_5013_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__3___closed__1));
v___x_5014_ = l_Lean_Core_mkFreshUserName(v___x_5013_, v___y_5005_, v___y_5006_);
if (lean_obj_tag(v___x_5014_) == 0)
{
lean_object* v_a_5015_; lean_object* v_resultType_5016_; lean_object* v___x_5018_; uint8_t v_isShared_5019_; uint8_t v_isSharedCheck_5043_; 
v_a_5015_ = lean_ctor_get(v___x_5014_, 0);
lean_inc(v_a_5015_);
lean_dec_ref_known(v___x_5014_, 1);
v_resultType_5016_ = lean_ctor_get(v_a_4983_, 0);
v_isSharedCheck_5043_ = !lean_is_exclusive(v_a_4983_);
if (v_isSharedCheck_5043_ == 0)
{
lean_object* v_unused_5044_; 
v_unused_5044_ = lean_ctor_get(v_a_4983_, 1);
lean_dec(v_unused_5044_);
v___x_5018_ = v_a_4983_;
v_isShared_5019_ = v_isSharedCheck_5043_;
goto v_resetjp_5017_;
}
else
{
lean_inc(v_resultType_5016_);
lean_dec(v_a_4983_);
v___x_5018_ = lean_box(0);
v_isShared_5019_ = v_isSharedCheck_5043_;
goto v_resetjp_5017_;
}
v_resetjp_5017_:
{
lean_object* v___x_5020_; uint8_t v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5027_; 
v___x_5020_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__3___closed__2));
v___x_5021_ = 0;
v___x_5022_ = l_Lean_mkLambda(v___x_5020_, v___x_5021_, v_a_5008_, v_a_5010_);
v___x_5023_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__3___closed__6));
v___x_5024_ = l_Lean_Level_succ___override(v_v_4984_);
v___x_5025_ = lean_box(0);
if (v_isShared_5019_ == 0)
{
lean_ctor_set_tag(v___x_5018_, 1);
lean_ctor_set(v___x_5018_, 1, v___x_5025_);
lean_ctor_set(v___x_5018_, 0, v___x_5024_);
v___x_5027_ = v___x_5018_;
goto v_reusejp_5026_;
}
else
{
lean_object* v_reuseFailAlloc_5042_; 
v_reuseFailAlloc_5042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5042_, 0, v___x_5024_);
lean_ctor_set(v_reuseFailAlloc_5042_, 1, v___x_5025_);
v___x_5027_ = v_reuseFailAlloc_5042_;
goto v_reusejp_5026_;
}
v_reusejp_5026_:
{
lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; 
v___x_5028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5028_, 0, v_u_4985_);
lean_ctor_set(v___x_5028_, 1, v___x_5027_);
v___x_5029_ = l_Lean_mkConst(v___x_5023_, v___x_5028_);
lean_inc_ref(v_resultType_5016_);
v___x_5030_ = l_Lean_mkApp3(v___x_5029_, v_resultType_5016_, v___x_5022_, v_ret_4999_);
v___x_5031_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v_a_5015_, v_resultType_5016_, v___f_4986_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
if (lean_obj_tag(v___x_5031_) == 0)
{
lean_object* v_a_5032_; lean_object* v___x_5034_; uint8_t v_isShared_5035_; uint8_t v_isSharedCheck_5041_; 
v_a_5032_ = lean_ctor_get(v___x_5031_, 0);
v_isSharedCheck_5041_ = !lean_is_exclusive(v___x_5031_);
if (v_isSharedCheck_5041_ == 0)
{
v___x_5034_ = v___x_5031_;
v_isShared_5035_ = v_isSharedCheck_5041_;
goto v_resetjp_5033_;
}
else
{
lean_inc(v_a_5032_);
lean_dec(v___x_5031_);
v___x_5034_ = lean_box(0);
v_isShared_5035_ = v_isSharedCheck_5041_;
goto v_resetjp_5033_;
}
v_resetjp_5033_:
{
lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5039_; 
v___x_5036_ = l_Lean_mkSimpleThunk(v_a_5012_);
v___x_5037_ = l_Lean_mkAppB(v___x_5030_, v_a_5032_, v___x_5036_);
if (v_isShared_5035_ == 0)
{
lean_ctor_set(v___x_5034_, 0, v___x_5037_);
v___x_5039_ = v___x_5034_;
goto v_reusejp_5038_;
}
else
{
lean_object* v_reuseFailAlloc_5040_; 
v_reuseFailAlloc_5040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5040_, 0, v___x_5037_);
v___x_5039_ = v_reuseFailAlloc_5040_;
goto v_reusejp_5038_;
}
v_reusejp_5038_:
{
return v___x_5039_;
}
}
}
else
{
lean_dec_ref(v___x_5030_);
lean_dec(v_a_5012_);
return v___x_5031_;
}
}
}
}
else
{
lean_object* v_a_5045_; lean_object* v___x_5047_; uint8_t v_isShared_5048_; uint8_t v_isSharedCheck_5052_; 
lean_dec(v_a_5012_);
lean_dec(v_a_5010_);
lean_dec(v_a_5008_);
lean_dec_ref(v_ret_4999_);
lean_dec_ref(v___f_4986_);
lean_dec(v_u_4985_);
lean_dec(v_v_4984_);
lean_dec_ref(v_a_4983_);
v_a_5045_ = lean_ctor_get(v___x_5014_, 0);
v_isSharedCheck_5052_ = !lean_is_exclusive(v___x_5014_);
if (v_isSharedCheck_5052_ == 0)
{
v___x_5047_ = v___x_5014_;
v_isShared_5048_ = v_isSharedCheck_5052_;
goto v_resetjp_5046_;
}
else
{
lean_inc(v_a_5045_);
lean_dec(v___x_5014_);
v___x_5047_ = lean_box(0);
v_isShared_5048_ = v_isSharedCheck_5052_;
goto v_resetjp_5046_;
}
v_resetjp_5046_:
{
lean_object* v___x_5050_; 
if (v_isShared_5048_ == 0)
{
v___x_5050_ = v___x_5047_;
goto v_reusejp_5049_;
}
else
{
lean_object* v_reuseFailAlloc_5051_; 
v_reuseFailAlloc_5051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5051_, 0, v_a_5045_);
v___x_5050_ = v_reuseFailAlloc_5051_;
goto v_reusejp_5049_;
}
v_reusejp_5049_:
{
return v___x_5050_;
}
}
}
}
else
{
lean_dec(v_a_5010_);
lean_dec(v_a_5008_);
lean_dec_ref(v_ret_4999_);
lean_dec_ref(v___f_4986_);
lean_dec(v_u_4985_);
lean_dec(v_v_4984_);
lean_dec_ref(v_a_4983_);
return v___x_5011_;
}
}
else
{
lean_dec(v_a_5008_);
lean_dec_ref(v_ret_4999_);
lean_dec_ref(v___f_4986_);
lean_dec(v_u_4985_);
lean_dec(v_v_4984_);
lean_dec_ref(v_a_4983_);
lean_dec_ref(v_a_4980_);
return v___x_5009_;
}
}
else
{
lean_dec_ref(v_ret_4999_);
lean_dec_ref(v___f_4986_);
lean_dec(v_u_4985_);
lean_dec(v_v_4984_);
lean_dec_ref(v_a_4983_);
lean_dec_ref(v_doBlockResultType_4982_);
lean_dec_ref(v_a_4980_);
return v___x_5007_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__3___boxed(lean_object** _args){
lean_object* v_returnsEarly_5063_ = _args[0];
lean_object* v_a_5064_ = _args[1];
lean_object* v_a_5065_ = _args[2];
lean_object* v_doBlockResultType_5066_ = _args[3];
lean_object* v_a_5067_ = _args[4];
lean_object* v_v_5068_ = _args[5];
lean_object* v_u_5069_ = _args[6];
lean_object* v___f_5070_ = _args[7];
lean_object* v___y_5071_ = _args[8];
lean_object* v___x_5072_ = _args[9];
lean_object* v___x_5073_ = _args[10];
lean_object* v___y_5074_ = _args[11];
lean_object* v___y_5075_ = _args[12];
lean_object* v___y_5076_ = _args[13];
lean_object* v___y_5077_ = _args[14];
lean_object* v___y_5078_ = _args[15];
lean_object* v___y_5079_ = _args[16];
lean_object* v___y_5080_ = _args[17];
lean_object* v___y_5081_ = _args[18];
_start:
{
uint8_t v_returnsEarly_boxed_5082_; lean_object* v_res_5083_; 
v_returnsEarly_boxed_5082_ = lean_unbox(v_returnsEarly_5063_);
v_res_5083_ = l_Lean_Elab_Do_elabDoFor___lam__3(v_returnsEarly_boxed_5082_, v_a_5064_, v_a_5065_, v_doBlockResultType_5066_, v_a_5067_, v_v_5068_, v_u_5069_, v___f_5070_, v___y_5071_, v___x_5072_, v___x_5073_, v___y_5074_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_);
lean_dec(v___y_5080_);
lean_dec_ref(v___y_5079_);
lean_dec(v___y_5078_);
lean_dec_ref(v___y_5077_);
lean_dec(v___y_5076_);
lean_dec_ref(v___y_5075_);
lean_dec_ref(v___y_5074_);
lean_dec(v___x_5073_);
lean_dec(v___x_5072_);
lean_dec_ref(v___y_5071_);
return v_res_5083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__4(lean_object* v___y_5084_, lean_object* v___y_5085_, lean_object* v___x_5086_, uint8_t v___x_5087_, lean_object* v_postS_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_){
_start:
{
lean_object* v___x_5097_; lean_object* v___x_5098_; 
v___x_5097_ = l_Lean_Expr_fvarId_x21(v_postS_5088_);
v___x_5098_ = l_Lean_Elab_Do_bindMutVarsFromTuple(v___y_5084_, v___x_5097_, v___y_5085_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_);
if (lean_obj_tag(v___x_5098_) == 0)
{
lean_object* v_a_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; uint8_t v___x_5102_; uint8_t v___x_5103_; lean_object* v___x_5104_; 
v_a_5099_ = lean_ctor_get(v___x_5098_, 0);
lean_inc(v_a_5099_);
lean_dec_ref_known(v___x_5098_, 1);
v___x_5100_ = lean_mk_empty_array_with_capacity(v___x_5086_);
v___x_5101_ = lean_array_push(v___x_5100_, v_postS_5088_);
v___x_5102_ = 0;
v___x_5103_ = 1;
v___x_5104_ = l_Lean_Meta_mkLambdaFVars(v___x_5101_, v_a_5099_, v___x_5102_, v___x_5087_, v___x_5102_, v___x_5087_, v___x_5103_, v___y_5092_, v___y_5093_, v___y_5094_, v___y_5095_);
lean_dec_ref(v___x_5101_);
return v___x_5104_;
}
else
{
lean_dec_ref(v_postS_5088_);
return v___x_5098_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__4___boxed(lean_object* v___y_5105_, lean_object* v___y_5106_, lean_object* v___x_5107_, lean_object* v___x_5108_, lean_object* v_postS_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_){
_start:
{
uint8_t v___x_89378__boxed_5118_; lean_object* v_res_5119_; 
v___x_89378__boxed_5118_ = lean_unbox(v___x_5108_);
v_res_5119_ = l_Lean_Elab_Do_elabDoFor___lam__4(v___y_5105_, v___y_5106_, v___x_5107_, v___x_89378__boxed_5118_, v_postS_5109_, v___y_5110_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_);
lean_dec(v___y_5116_);
lean_dec_ref(v___y_5115_);
lean_dec(v___y_5114_);
lean_dec_ref(v___y_5113_);
lean_dec(v___y_5112_);
lean_dec_ref(v___y_5111_);
lean_dec_ref(v___y_5110_);
lean_dec(v___x_5107_);
return v_res_5119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__5(lean_object* v___f_5121_, lean_object* v_u_5122_, lean_object* v___x_5123_, lean_object* v___x_5124_, lean_object* v_snd_5125_, lean_object* v___x_5126_, lean_object* v_e_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_, lean_object* v___y_5133_, lean_object* v___y_5134_){
_start:
{
lean_object* v___x_5136_; lean_object* v___x_5137_; 
v___x_5136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5136_, 0, v_e_5127_);
lean_inc(v___y_5134_);
lean_inc_ref(v___y_5133_);
lean_inc(v___y_5132_);
lean_inc_ref(v___y_5131_);
lean_inc(v___y_5130_);
lean_inc_ref(v___y_5129_);
v___x_5137_ = lean_apply_8(v___f_5121_, v___x_5136_, v___y_5129_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_, lean_box(0));
if (lean_obj_tag(v___x_5137_) == 0)
{
lean_object* v_a_5138_; lean_object* v___x_5139_; 
v_a_5138_ = lean_ctor_get(v___x_5137_, 0);
lean_inc(v_a_5138_);
lean_dec_ref_known(v___x_5137_, 1);
v___x_5139_ = l_Lean_Meta_mkProdMkN(v_a_5138_, v_u_5122_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_);
if (lean_obj_tag(v___x_5139_) == 0)
{
lean_object* v_a_5140_; lean_object* v_fst_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; 
v_a_5140_ = lean_ctor_get(v___x_5139_, 0);
lean_inc(v_a_5140_);
lean_dec_ref_known(v___x_5139_, 1);
v_fst_5141_ = lean_ctor_get(v_a_5140_, 0);
lean_inc(v_fst_5141_);
lean_dec(v_a_5140_);
v___x_5142_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__5___closed__0));
v___x_5143_ = l_Lean_Name_mkStr2(v___x_5123_, v___x_5142_);
v___x_5144_ = l_Lean_mkConst(v___x_5143_, v___x_5124_);
v___x_5145_ = l_Lean_mkAppB(v___x_5144_, v_snd_5125_, v_fst_5141_);
v___x_5146_ = l_Lean_Elab_Do_mkPureApp(v___x_5126_, v___x_5145_, v___y_5128_, v___y_5129_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_);
return v___x_5146_;
}
else
{
lean_object* v_a_5147_; lean_object* v___x_5149_; uint8_t v_isShared_5150_; uint8_t v_isSharedCheck_5154_; 
lean_dec_ref(v___x_5126_);
lean_dec_ref(v_snd_5125_);
lean_dec(v___x_5124_);
lean_dec_ref(v___x_5123_);
v_a_5147_ = lean_ctor_get(v___x_5139_, 0);
v_isSharedCheck_5154_ = !lean_is_exclusive(v___x_5139_);
if (v_isSharedCheck_5154_ == 0)
{
v___x_5149_ = v___x_5139_;
v_isShared_5150_ = v_isSharedCheck_5154_;
goto v_resetjp_5148_;
}
else
{
lean_inc(v_a_5147_);
lean_dec(v___x_5139_);
v___x_5149_ = lean_box(0);
v_isShared_5150_ = v_isSharedCheck_5154_;
goto v_resetjp_5148_;
}
v_resetjp_5148_:
{
lean_object* v___x_5152_; 
if (v_isShared_5150_ == 0)
{
v___x_5152_ = v___x_5149_;
goto v_reusejp_5151_;
}
else
{
lean_object* v_reuseFailAlloc_5153_; 
v_reuseFailAlloc_5153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5153_, 0, v_a_5147_);
v___x_5152_ = v_reuseFailAlloc_5153_;
goto v_reusejp_5151_;
}
v_reusejp_5151_:
{
return v___x_5152_;
}
}
}
}
else
{
lean_object* v_a_5155_; lean_object* v___x_5157_; uint8_t v_isShared_5158_; uint8_t v_isSharedCheck_5162_; 
lean_dec_ref(v___x_5126_);
lean_dec_ref(v_snd_5125_);
lean_dec(v___x_5124_);
lean_dec_ref(v___x_5123_);
lean_dec(v_u_5122_);
v_a_5155_ = lean_ctor_get(v___x_5137_, 0);
v_isSharedCheck_5162_ = !lean_is_exclusive(v___x_5137_);
if (v_isSharedCheck_5162_ == 0)
{
v___x_5157_ = v___x_5137_;
v_isShared_5158_ = v_isSharedCheck_5162_;
goto v_resetjp_5156_;
}
else
{
lean_inc(v_a_5155_);
lean_dec(v___x_5137_);
v___x_5157_ = lean_box(0);
v_isShared_5158_ = v_isSharedCheck_5162_;
goto v_resetjp_5156_;
}
v_resetjp_5156_:
{
lean_object* v___x_5160_; 
if (v_isShared_5158_ == 0)
{
v___x_5160_ = v___x_5157_;
goto v_reusejp_5159_;
}
else
{
lean_object* v_reuseFailAlloc_5161_; 
v_reuseFailAlloc_5161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5161_, 0, v_a_5155_);
v___x_5160_ = v_reuseFailAlloc_5161_;
goto v_reusejp_5159_;
}
v_reusejp_5159_:
{
return v___x_5160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__5___boxed(lean_object* v___f_5163_, lean_object* v_u_5164_, lean_object* v___x_5165_, lean_object* v___x_5166_, lean_object* v_snd_5167_, lean_object* v___x_5168_, lean_object* v_e_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_){
_start:
{
lean_object* v_res_5178_; 
v_res_5178_ = l_Lean_Elab_Do_elabDoFor___lam__5(v___f_5163_, v_u_5164_, v___x_5165_, v___x_5166_, v_snd_5167_, v___x_5168_, v_e_5169_, v___y_5170_, v___y_5171_, v___y_5172_, v___y_5173_, v___y_5174_, v___y_5175_, v___y_5176_);
lean_dec(v___y_5176_);
lean_dec_ref(v___y_5175_);
lean_dec(v___y_5174_);
lean_dec_ref(v___y_5173_);
lean_dec(v___y_5172_);
lean_dec_ref(v___y_5171_);
lean_dec_ref(v___y_5170_);
return v_res_5178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__6(lean_object* v___f_5180_, lean_object* v___x_5181_, lean_object* v_u_5182_, lean_object* v___x_5183_, lean_object* v___x_5184_, lean_object* v_snd_5185_, lean_object* v___x_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_){
_start:
{
lean_object* v___x_5195_; 
lean_inc(v___y_5193_);
lean_inc_ref(v___y_5192_);
lean_inc(v___y_5191_);
lean_inc_ref(v___y_5190_);
lean_inc(v___y_5189_);
lean_inc_ref(v___y_5188_);
v___x_5195_ = lean_apply_8(v___f_5180_, v___x_5181_, v___y_5188_, v___y_5189_, v___y_5190_, v___y_5191_, v___y_5192_, v___y_5193_, lean_box(0));
if (lean_obj_tag(v___x_5195_) == 0)
{
lean_object* v_a_5196_; lean_object* v___x_5197_; 
v_a_5196_ = lean_ctor_get(v___x_5195_, 0);
lean_inc(v_a_5196_);
lean_dec_ref_known(v___x_5195_, 1);
v___x_5197_ = l_Lean_Meta_mkProdMkN(v_a_5196_, v_u_5182_, v___y_5190_, v___y_5191_, v___y_5192_, v___y_5193_);
if (lean_obj_tag(v___x_5197_) == 0)
{
lean_object* v_a_5198_; lean_object* v_fst_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; 
v_a_5198_ = lean_ctor_get(v___x_5197_, 0);
lean_inc(v_a_5198_);
lean_dec_ref_known(v___x_5197_, 1);
v_fst_5199_ = lean_ctor_get(v_a_5198_, 0);
lean_inc(v_fst_5199_);
lean_dec(v_a_5198_);
v___x_5200_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__6___closed__0));
v___x_5201_ = l_Lean_Name_mkStr2(v___x_5183_, v___x_5200_);
v___x_5202_ = l_Lean_mkConst(v___x_5201_, v___x_5184_);
v___x_5203_ = l_Lean_mkAppB(v___x_5202_, v_snd_5185_, v_fst_5199_);
v___x_5204_ = l_Lean_Elab_Do_mkPureApp(v___x_5186_, v___x_5203_, v___y_5187_, v___y_5188_, v___y_5189_, v___y_5190_, v___y_5191_, v___y_5192_, v___y_5193_);
return v___x_5204_;
}
else
{
lean_object* v_a_5205_; lean_object* v___x_5207_; uint8_t v_isShared_5208_; uint8_t v_isSharedCheck_5212_; 
lean_dec_ref(v___x_5186_);
lean_dec_ref(v_snd_5185_);
lean_dec(v___x_5184_);
lean_dec_ref(v___x_5183_);
v_a_5205_ = lean_ctor_get(v___x_5197_, 0);
v_isSharedCheck_5212_ = !lean_is_exclusive(v___x_5197_);
if (v_isSharedCheck_5212_ == 0)
{
v___x_5207_ = v___x_5197_;
v_isShared_5208_ = v_isSharedCheck_5212_;
goto v_resetjp_5206_;
}
else
{
lean_inc(v_a_5205_);
lean_dec(v___x_5197_);
v___x_5207_ = lean_box(0);
v_isShared_5208_ = v_isSharedCheck_5212_;
goto v_resetjp_5206_;
}
v_resetjp_5206_:
{
lean_object* v___x_5210_; 
if (v_isShared_5208_ == 0)
{
v___x_5210_ = v___x_5207_;
goto v_reusejp_5209_;
}
else
{
lean_object* v_reuseFailAlloc_5211_; 
v_reuseFailAlloc_5211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5211_, 0, v_a_5205_);
v___x_5210_ = v_reuseFailAlloc_5211_;
goto v_reusejp_5209_;
}
v_reusejp_5209_:
{
return v___x_5210_;
}
}
}
}
else
{
lean_object* v_a_5213_; lean_object* v___x_5215_; uint8_t v_isShared_5216_; uint8_t v_isSharedCheck_5220_; 
lean_dec_ref(v___x_5186_);
lean_dec_ref(v_snd_5185_);
lean_dec(v___x_5184_);
lean_dec_ref(v___x_5183_);
lean_dec(v_u_5182_);
v_a_5213_ = lean_ctor_get(v___x_5195_, 0);
v_isSharedCheck_5220_ = !lean_is_exclusive(v___x_5195_);
if (v_isSharedCheck_5220_ == 0)
{
v___x_5215_ = v___x_5195_;
v_isShared_5216_ = v_isSharedCheck_5220_;
goto v_resetjp_5214_;
}
else
{
lean_inc(v_a_5213_);
lean_dec(v___x_5195_);
v___x_5215_ = lean_box(0);
v_isShared_5216_ = v_isSharedCheck_5220_;
goto v_resetjp_5214_;
}
v_resetjp_5214_:
{
lean_object* v___x_5218_; 
if (v_isShared_5216_ == 0)
{
v___x_5218_ = v___x_5215_;
goto v_reusejp_5217_;
}
else
{
lean_object* v_reuseFailAlloc_5219_; 
v_reuseFailAlloc_5219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5219_, 0, v_a_5213_);
v___x_5218_ = v_reuseFailAlloc_5219_;
goto v_reusejp_5217_;
}
v_reusejp_5217_:
{
return v___x_5218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__6___boxed(lean_object* v___f_5221_, lean_object* v___x_5222_, lean_object* v_u_5223_, lean_object* v___x_5224_, lean_object* v___x_5225_, lean_object* v_snd_5226_, lean_object* v___x_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_, lean_object* v___y_5232_, lean_object* v___y_5233_, lean_object* v___y_5234_, lean_object* v___y_5235_){
_start:
{
lean_object* v_res_5236_; 
v_res_5236_ = l_Lean_Elab_Do_elabDoFor___lam__6(v___f_5221_, v___x_5222_, v_u_5223_, v___x_5224_, v___x_5225_, v_snd_5226_, v___x_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_);
lean_dec(v___y_5234_);
lean_dec_ref(v___y_5233_);
lean_dec(v___y_5232_);
lean_dec_ref(v___y_5231_);
lean_dec(v___y_5230_);
lean_dec_ref(v___y_5229_);
lean_dec_ref(v___y_5228_);
return v_res_5236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__7(lean_object* v___f_5237_, lean_object* v___x_5238_, lean_object* v_u_5239_, lean_object* v___x_5240_, lean_object* v___x_5241_, lean_object* v_snd_5242_, lean_object* v___x_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_){
_start:
{
lean_object* v___x_5252_; 
lean_inc(v___y_5250_);
lean_inc_ref(v___y_5249_);
lean_inc(v___y_5248_);
lean_inc_ref(v___y_5247_);
lean_inc(v___y_5246_);
lean_inc_ref(v___y_5245_);
v___x_5252_ = lean_apply_8(v___f_5237_, v___x_5238_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_, lean_box(0));
if (lean_obj_tag(v___x_5252_) == 0)
{
lean_object* v_a_5253_; lean_object* v___x_5254_; 
v_a_5253_ = lean_ctor_get(v___x_5252_, 0);
lean_inc(v_a_5253_);
lean_dec_ref_known(v___x_5252_, 1);
v___x_5254_ = l_Lean_Meta_mkProdMkN(v_a_5253_, v_u_5239_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_);
if (lean_obj_tag(v___x_5254_) == 0)
{
lean_object* v_a_5255_; lean_object* v_fst_5256_; lean_object* v___x_5257_; lean_object* v___x_5258_; lean_object* v___x_5259_; lean_object* v___x_5260_; lean_object* v___x_5261_; 
v_a_5255_ = lean_ctor_get(v___x_5254_, 0);
lean_inc(v_a_5255_);
lean_dec_ref_known(v___x_5254_, 1);
v_fst_5256_ = lean_ctor_get(v_a_5255_, 0);
lean_inc(v_fst_5256_);
lean_dec(v_a_5255_);
v___x_5257_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__5___closed__0));
v___x_5258_ = l_Lean_Name_mkStr2(v___x_5240_, v___x_5257_);
v___x_5259_ = l_Lean_mkConst(v___x_5258_, v___x_5241_);
v___x_5260_ = l_Lean_mkAppB(v___x_5259_, v_snd_5242_, v_fst_5256_);
v___x_5261_ = l_Lean_Elab_Do_mkPureApp(v___x_5243_, v___x_5260_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_);
return v___x_5261_;
}
else
{
lean_object* v_a_5262_; lean_object* v___x_5264_; uint8_t v_isShared_5265_; uint8_t v_isSharedCheck_5269_; 
lean_dec_ref(v___x_5243_);
lean_dec_ref(v_snd_5242_);
lean_dec(v___x_5241_);
lean_dec_ref(v___x_5240_);
v_a_5262_ = lean_ctor_get(v___x_5254_, 0);
v_isSharedCheck_5269_ = !lean_is_exclusive(v___x_5254_);
if (v_isSharedCheck_5269_ == 0)
{
v___x_5264_ = v___x_5254_;
v_isShared_5265_ = v_isSharedCheck_5269_;
goto v_resetjp_5263_;
}
else
{
lean_inc(v_a_5262_);
lean_dec(v___x_5254_);
v___x_5264_ = lean_box(0);
v_isShared_5265_ = v_isSharedCheck_5269_;
goto v_resetjp_5263_;
}
v_resetjp_5263_:
{
lean_object* v___x_5267_; 
if (v_isShared_5265_ == 0)
{
v___x_5267_ = v___x_5264_;
goto v_reusejp_5266_;
}
else
{
lean_object* v_reuseFailAlloc_5268_; 
v_reuseFailAlloc_5268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5268_, 0, v_a_5262_);
v___x_5267_ = v_reuseFailAlloc_5268_;
goto v_reusejp_5266_;
}
v_reusejp_5266_:
{
return v___x_5267_;
}
}
}
}
else
{
lean_object* v_a_5270_; lean_object* v___x_5272_; uint8_t v_isShared_5273_; uint8_t v_isSharedCheck_5277_; 
lean_dec_ref(v___x_5243_);
lean_dec_ref(v_snd_5242_);
lean_dec(v___x_5241_);
lean_dec_ref(v___x_5240_);
lean_dec(v_u_5239_);
v_a_5270_ = lean_ctor_get(v___x_5252_, 0);
v_isSharedCheck_5277_ = !lean_is_exclusive(v___x_5252_);
if (v_isSharedCheck_5277_ == 0)
{
v___x_5272_ = v___x_5252_;
v_isShared_5273_ = v_isSharedCheck_5277_;
goto v_resetjp_5271_;
}
else
{
lean_inc(v_a_5270_);
lean_dec(v___x_5252_);
v___x_5272_ = lean_box(0);
v_isShared_5273_ = v_isSharedCheck_5277_;
goto v_resetjp_5271_;
}
v_resetjp_5271_:
{
lean_object* v___x_5275_; 
if (v_isShared_5273_ == 0)
{
v___x_5275_ = v___x_5272_;
goto v_reusejp_5274_;
}
else
{
lean_object* v_reuseFailAlloc_5276_; 
v_reuseFailAlloc_5276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5276_, 0, v_a_5270_);
v___x_5275_ = v_reuseFailAlloc_5276_;
goto v_reusejp_5274_;
}
v_reusejp_5274_:
{
return v___x_5275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__7___boxed(lean_object* v___f_5278_, lean_object* v___x_5279_, lean_object* v_u_5280_, lean_object* v___x_5281_, lean_object* v___x_5282_, lean_object* v_snd_5283_, lean_object* v___x_5284_, lean_object* v___y_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_){
_start:
{
lean_object* v_res_5293_; 
v_res_5293_ = l_Lean_Elab_Do_elabDoFor___lam__7(v___f_5278_, v___x_5279_, v_u_5280_, v___x_5281_, v___x_5282_, v_snd_5283_, v___x_5284_, v___y_5285_, v___y_5286_, v___y_5287_, v___y_5288_, v___y_5289_, v___y_5290_, v___y_5291_);
lean_dec(v___y_5291_);
lean_dec_ref(v___y_5290_);
lean_dec(v___y_5289_);
lean_dec_ref(v___y_5288_);
lean_dec(v___y_5287_);
lean_dec_ref(v___y_5286_);
lean_dec_ref(v___y_5285_);
return v_res_5293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__8(lean_object* v___x_5294_, lean_object* v___f_5295_, lean_object* v___f_5296_, lean_object* v___x_5297_, lean_object* v___x_5298_, lean_object* v___y_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_){
_start:
{
lean_object* v_monadInfo_5307_; lean_object* v_mutVars_5308_; lean_object* v_mutVarDefs_5309_; lean_object* v_contInfo_5310_; uint8_t v_deadCode_5311_; lean_object* v_ops_5312_; lean_object* v___x_5314_; uint8_t v_isShared_5315_; uint8_t v_isSharedCheck_5320_; 
v_monadInfo_5307_ = lean_ctor_get(v___y_5299_, 0);
v_mutVars_5308_ = lean_ctor_get(v___y_5299_, 1);
v_mutVarDefs_5309_ = lean_ctor_get(v___y_5299_, 2);
v_contInfo_5310_ = lean_ctor_get(v___y_5299_, 4);
v_deadCode_5311_ = lean_ctor_get_uint8(v___y_5299_, sizeof(void*)*6);
v_ops_5312_ = lean_ctor_get(v___y_5299_, 5);
v_isSharedCheck_5320_ = !lean_is_exclusive(v___y_5299_);
if (v_isSharedCheck_5320_ == 0)
{
lean_object* v_unused_5321_; 
v_unused_5321_ = lean_ctor_get(v___y_5299_, 3);
lean_dec(v_unused_5321_);
v___x_5314_ = v___y_5299_;
v_isShared_5315_ = v_isSharedCheck_5320_;
goto v_resetjp_5313_;
}
else
{
lean_inc(v_ops_5312_);
lean_inc(v_contInfo_5310_);
lean_inc(v_mutVarDefs_5309_);
lean_inc(v_mutVars_5308_);
lean_inc(v_monadInfo_5307_);
lean_dec(v___y_5299_);
v___x_5314_ = lean_box(0);
v_isShared_5315_ = v_isSharedCheck_5320_;
goto v_resetjp_5313_;
}
v_resetjp_5313_:
{
lean_object* v___x_5317_; 
if (v_isShared_5315_ == 0)
{
lean_ctor_set(v___x_5314_, 3, v___x_5294_);
v___x_5317_ = v___x_5314_;
goto v_reusejp_5316_;
}
else
{
lean_object* v_reuseFailAlloc_5319_; 
v_reuseFailAlloc_5319_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_5319_, 0, v_monadInfo_5307_);
lean_ctor_set(v_reuseFailAlloc_5319_, 1, v_mutVars_5308_);
lean_ctor_set(v_reuseFailAlloc_5319_, 2, v_mutVarDefs_5309_);
lean_ctor_set(v_reuseFailAlloc_5319_, 3, v___x_5294_);
lean_ctor_set(v_reuseFailAlloc_5319_, 4, v_contInfo_5310_);
lean_ctor_set(v_reuseFailAlloc_5319_, 5, v_ops_5312_);
lean_ctor_set_uint8(v_reuseFailAlloc_5319_, sizeof(void*)*6, v_deadCode_5311_);
v___x_5317_ = v_reuseFailAlloc_5319_;
goto v_reusejp_5316_;
}
v_reusejp_5316_:
{
lean_object* v___x_5318_; 
v___x_5318_ = l_Lean_Elab_Do_enterLoopBody___redArg(v___f_5295_, v___f_5296_, v___x_5297_, v___x_5298_, v___x_5317_, v___y_5300_, v___y_5301_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_);
lean_dec_ref(v___x_5317_);
return v___x_5318_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__8___boxed(lean_object* v___x_5322_, lean_object* v___f_5323_, lean_object* v___f_5324_, lean_object* v___x_5325_, lean_object* v___x_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_){
_start:
{
lean_object* v_res_5335_; 
v_res_5335_ = l_Lean_Elab_Do_elabDoFor___lam__8(v___x_5322_, v___f_5323_, v___f_5324_, v___x_5325_, v___x_5326_, v___y_5327_, v___y_5328_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_);
lean_dec(v___y_5333_);
lean_dec_ref(v___y_5332_);
lean_dec(v___y_5331_);
lean_dec_ref(v___y_5330_);
lean_dec(v___y_5329_);
lean_dec_ref(v___y_5328_);
return v_res_5335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9(lean_object* v_a_5339_, lean_object* v_a_5340_, lean_object* v_u_5341_, lean_object* v_snd_5342_, lean_object* v___f_5343_, lean_object* v___x_5344_, lean_object* v_body_5345_, uint8_t v___x_5346_, lean_object* v___y_5347_, lean_object* v_xh_5348_, lean_object* v_loopS_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_){
_start:
{
lean_object* v_resultType_5358_; lean_object* v___x_5360_; uint8_t v_isShared_5361_; uint8_t v_isSharedCheck_5395_; 
v_resultType_5358_ = lean_ctor_get(v_a_5339_, 0);
v_isSharedCheck_5395_ = !lean_is_exclusive(v_a_5339_);
if (v_isSharedCheck_5395_ == 0)
{
lean_object* v_unused_5396_; 
v_unused_5396_ = lean_ctor_get(v_a_5339_, 1);
lean_dec(v_unused_5396_);
v___x_5360_ = v_a_5339_;
v_isShared_5361_ = v_isSharedCheck_5395_;
goto v_resetjp_5359_;
}
else
{
lean_inc(v_resultType_5358_);
lean_dec(v_a_5339_);
v___x_5360_ = lean_box(0);
v_isShared_5361_ = v_isSharedCheck_5395_;
goto v_resetjp_5359_;
}
v_resetjp_5359_:
{
lean_object* v_resultName_5362_; lean_object* v_resultType_5363_; lean_object* v___x_5365_; uint8_t v_isShared_5366_; uint8_t v_isSharedCheck_5393_; 
v_resultName_5362_ = lean_ctor_get(v_a_5340_, 0);
v_resultType_5363_ = lean_ctor_get(v_a_5340_, 1);
v_isSharedCheck_5393_ = !lean_is_exclusive(v_a_5340_);
if (v_isSharedCheck_5393_ == 0)
{
lean_object* v_unused_5394_; 
v_unused_5394_ = lean_ctor_get(v_a_5340_, 2);
lean_dec(v_unused_5394_);
v___x_5365_ = v_a_5340_;
v_isShared_5366_ = v_isSharedCheck_5393_;
goto v_resetjp_5364_;
}
else
{
lean_inc(v_resultType_5363_);
lean_inc(v_resultName_5362_);
lean_dec(v_a_5340_);
v___x_5365_ = lean_box(0);
v_isShared_5366_ = v_isSharedCheck_5393_;
goto v_resetjp_5364_;
}
v_resetjp_5364_:
{
lean_object* v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; lean_object* v___f_5374_; lean_object* v___f_5375_; lean_object* v___f_5376_; lean_object* v___x_5378_; 
v___x_5367_ = l_Lean_Expr_fvarId_x21(v_loopS_5349_);
v___x_5368_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__9___closed__0));
v___x_5369_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__9___closed__1));
v___x_5370_ = lean_box(0);
lean_inc_n(v_u_5341_, 3);
v___x_5371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5371_, 0, v_u_5341_);
lean_ctor_set(v___x_5371_, 1, v___x_5370_);
lean_inc_ref_n(v___x_5371_, 3);
v___x_5372_ = l_Lean_mkConst(v___x_5369_, v___x_5371_);
lean_inc_ref_n(v_snd_5342_, 3);
v___x_5373_ = l_Lean_Expr_app___override(v___x_5372_, v_snd_5342_);
lean_inc_ref_n(v___x_5373_, 3);
lean_inc_ref_n(v___f_5343_, 2);
v___f_5374_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__5___boxed), 15, 6);
lean_closure_set(v___f_5374_, 0, v___f_5343_);
lean_closure_set(v___f_5374_, 1, v_u_5341_);
lean_closure_set(v___f_5374_, 2, v___x_5368_);
lean_closure_set(v___f_5374_, 3, v___x_5371_);
lean_closure_set(v___f_5374_, 4, v_snd_5342_);
lean_closure_set(v___f_5374_, 5, v___x_5373_);
lean_inc(v___x_5344_);
v___f_5375_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__6___boxed), 15, 7);
lean_closure_set(v___f_5375_, 0, v___f_5343_);
lean_closure_set(v___f_5375_, 1, v___x_5344_);
lean_closure_set(v___f_5375_, 2, v_u_5341_);
lean_closure_set(v___f_5375_, 3, v___x_5368_);
lean_closure_set(v___f_5375_, 4, v___x_5371_);
lean_closure_set(v___f_5375_, 5, v_snd_5342_);
lean_closure_set(v___f_5375_, 6, v___x_5373_);
v___f_5376_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__7___boxed), 15, 7);
lean_closure_set(v___f_5376_, 0, v___f_5343_);
lean_closure_set(v___f_5376_, 1, v___x_5344_);
lean_closure_set(v___f_5376_, 2, v_u_5341_);
lean_closure_set(v___f_5376_, 3, v___x_5368_);
lean_closure_set(v___f_5376_, 4, v___x_5371_);
lean_closure_set(v___f_5376_, 5, v_snd_5342_);
lean_closure_set(v___f_5376_, 6, v___x_5373_);
if (v_isShared_5361_ == 0)
{
lean_ctor_set(v___x_5360_, 1, v___f_5374_);
v___x_5378_ = v___x_5360_;
goto v_reusejp_5377_;
}
else
{
lean_object* v_reuseFailAlloc_5392_; 
v_reuseFailAlloc_5392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5392_, 0, v_resultType_5358_);
lean_ctor_set(v_reuseFailAlloc_5392_, 1, v___f_5374_);
v___x_5378_ = v_reuseFailAlloc_5392_;
goto v_reusejp_5377_;
}
v_reusejp_5377_:
{
uint8_t v___x_5379_; lean_object* v___x_5381_; 
v___x_5379_ = 1;
lean_inc_ref(v___f_5375_);
if (v_isShared_5366_ == 0)
{
lean_ctor_set(v___x_5365_, 2, v___f_5375_);
v___x_5381_ = v___x_5365_;
goto v_reusejp_5380_;
}
else
{
lean_object* v_reuseFailAlloc_5391_; 
v_reuseFailAlloc_5391_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_5391_, 0, v_resultName_5362_);
lean_ctor_set(v_reuseFailAlloc_5391_, 1, v_resultType_5363_);
lean_ctor_set(v_reuseFailAlloc_5391_, 2, v___f_5375_);
v___x_5381_ = v_reuseFailAlloc_5391_;
goto v_reusejp_5380_;
}
v_reusejp_5380_:
{
lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___f_5384_; lean_object* v___x_5385_; 
lean_ctor_set_uint8(v___x_5381_, sizeof(void*)*3, v___x_5379_);
v___x_5382_ = lean_box(v___x_5346_);
v___x_5383_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoSeq___boxed), 11, 3);
lean_closure_set(v___x_5383_, 0, v_body_5345_);
lean_closure_set(v___x_5383_, 1, v___x_5381_);
lean_closure_set(v___x_5383_, 2, v___x_5382_);
v___f_5384_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__8___boxed), 13, 5);
lean_closure_set(v___f_5384_, 0, v___x_5373_);
lean_closure_set(v___f_5384_, 1, v___f_5376_);
lean_closure_set(v___f_5384_, 2, v___f_5375_);
lean_closure_set(v___f_5384_, 3, v___x_5378_);
lean_closure_set(v___f_5384_, 4, v___x_5383_);
v___x_5385_ = l_Lean_Elab_Do_bindMutVarsFromTuple(v___y_5347_, v___x_5367_, v___f_5384_, v___y_5350_, v___y_5351_, v___y_5352_, v___y_5353_, v___y_5354_, v___y_5355_, v___y_5356_);
if (lean_obj_tag(v___x_5385_) == 0)
{
lean_object* v_a_5386_; lean_object* v___x_5387_; uint8_t v___x_5388_; uint8_t v___x_5389_; lean_object* v___x_5390_; 
v_a_5386_ = lean_ctor_get(v___x_5385_, 0);
lean_inc(v_a_5386_);
lean_dec_ref_known(v___x_5385_, 1);
v___x_5387_ = lean_array_push(v_xh_5348_, v_loopS_5349_);
v___x_5388_ = 0;
v___x_5389_ = 1;
v___x_5390_ = l_Lean_Meta_mkLambdaFVars(v___x_5387_, v_a_5386_, v___x_5388_, v___x_5346_, v___x_5388_, v___x_5346_, v___x_5389_, v___y_5353_, v___y_5354_, v___y_5355_, v___y_5356_);
lean_dec_ref(v___x_5387_);
return v___x_5390_;
}
else
{
lean_dec_ref(v_loopS_5349_);
lean_dec_ref(v_xh_5348_);
return v___x_5385_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__9___boxed(lean_object** _args){
lean_object* v_a_5397_ = _args[0];
lean_object* v_a_5398_ = _args[1];
lean_object* v_u_5399_ = _args[2];
lean_object* v_snd_5400_ = _args[3];
lean_object* v___f_5401_ = _args[4];
lean_object* v___x_5402_ = _args[5];
lean_object* v_body_5403_ = _args[6];
lean_object* v___x_5404_ = _args[7];
lean_object* v___y_5405_ = _args[8];
lean_object* v_xh_5406_ = _args[9];
lean_object* v_loopS_5407_ = _args[10];
lean_object* v___y_5408_ = _args[11];
lean_object* v___y_5409_ = _args[12];
lean_object* v___y_5410_ = _args[13];
lean_object* v___y_5411_ = _args[14];
lean_object* v___y_5412_ = _args[15];
lean_object* v___y_5413_ = _args[16];
lean_object* v___y_5414_ = _args[17];
lean_object* v___y_5415_ = _args[18];
_start:
{
uint8_t v___x_89787__boxed_5416_; lean_object* v_res_5417_; 
v___x_89787__boxed_5416_ = lean_unbox(v___x_5404_);
v_res_5417_ = l_Lean_Elab_Do_elabDoFor___lam__9(v_a_5397_, v_a_5398_, v_u_5399_, v_snd_5400_, v___f_5401_, v___x_5402_, v_body_5403_, v___x_89787__boxed_5416_, v___y_5405_, v_xh_5406_, v_loopS_5407_, v___y_5408_, v___y_5409_, v___y_5410_, v___y_5411_, v___y_5412_, v___y_5413_, v___y_5414_);
lean_dec(v___y_5414_);
lean_dec_ref(v___y_5413_);
lean_dec(v___y_5412_);
lean_dec_ref(v___y_5411_);
lean_dec(v___y_5410_);
lean_dec_ref(v___y_5409_);
lean_dec_ref(v___y_5408_);
return v_res_5417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__10(lean_object* v___x_5418_, lean_object* v___x_5419_, lean_object* v_x_5420_, lean_object* v_a_5421_, lean_object* v_a_5422_, lean_object* v_u_5423_, lean_object* v_snd_5424_, lean_object* v___f_5425_, lean_object* v___x_5426_, lean_object* v_body_5427_, uint8_t v___x_5428_, lean_object* v___y_5429_, lean_object* v_a_5430_, lean_object* v_h_x3f_5431_, lean_object* v___x_5432_, lean_object* v_xh_5433_, lean_object* v___y_5434_, lean_object* v___y_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_, lean_object* v___y_5438_, lean_object* v___y_5439_, lean_object* v___y_5440_){
_start:
{
lean_object* v___x_5442_; lean_object* v___x_5443_; 
v___x_5442_ = lean_array_get_borrowed(v___x_5418_, v_xh_5433_, v___x_5419_);
lean_inc(v___x_5442_);
v___x_5443_ = l_Lean_Elab_Term_addLocalVarInfo(v_x_5420_, v___x_5442_, v___y_5435_, v___y_5436_, v___y_5437_, v___y_5438_, v___y_5439_, v___y_5440_);
if (lean_obj_tag(v___x_5443_) == 0)
{
lean_object* v___x_5444_; lean_object* v___f_5445_; lean_object* v___y_5447_; lean_object* v___y_5448_; lean_object* v___y_5449_; lean_object* v___y_5450_; lean_object* v___y_5451_; lean_object* v___y_5452_; lean_object* v___y_5453_; 
lean_dec_ref_known(v___x_5443_, 1);
v___x_5444_ = lean_box(v___x_5428_);
lean_inc_ref(v_xh_5433_);
lean_inc_ref(v_snd_5424_);
v___f_5445_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__9___boxed), 19, 10);
lean_closure_set(v___f_5445_, 0, v_a_5421_);
lean_closure_set(v___f_5445_, 1, v_a_5422_);
lean_closure_set(v___f_5445_, 2, v_u_5423_);
lean_closure_set(v___f_5445_, 3, v_snd_5424_);
lean_closure_set(v___f_5445_, 4, v___f_5425_);
lean_closure_set(v___f_5445_, 5, v___x_5426_);
lean_closure_set(v___f_5445_, 6, v_body_5427_);
lean_closure_set(v___f_5445_, 7, v___x_5444_);
lean_closure_set(v___f_5445_, 8, v___y_5429_);
lean_closure_set(v___f_5445_, 9, v_xh_5433_);
if (lean_obj_tag(v_h_x3f_5431_) == 1)
{
lean_object* v_val_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; 
v_val_5457_ = lean_ctor_get(v_h_x3f_5431_, 0);
lean_inc(v_val_5457_);
lean_dec_ref_known(v_h_x3f_5431_, 1);
v___x_5458_ = lean_array_get(v___x_5418_, v_xh_5433_, v___x_5432_);
lean_dec_ref(v_xh_5433_);
v___x_5459_ = l_Lean_Elab_Term_addLocalVarInfo(v_val_5457_, v___x_5458_, v___y_5435_, v___y_5436_, v___y_5437_, v___y_5438_, v___y_5439_, v___y_5440_);
if (lean_obj_tag(v___x_5459_) == 0)
{
lean_dec_ref_known(v___x_5459_, 1);
v___y_5447_ = v___y_5434_;
v___y_5448_ = v___y_5435_;
v___y_5449_ = v___y_5436_;
v___y_5450_ = v___y_5437_;
v___y_5451_ = v___y_5438_;
v___y_5452_ = v___y_5439_;
v___y_5453_ = v___y_5440_;
goto v___jp_5446_;
}
else
{
lean_object* v_a_5460_; lean_object* v___x_5462_; uint8_t v_isShared_5463_; uint8_t v_isSharedCheck_5467_; 
lean_dec_ref(v___f_5445_);
lean_dec(v_a_5430_);
lean_dec_ref(v_snd_5424_);
v_a_5460_ = lean_ctor_get(v___x_5459_, 0);
v_isSharedCheck_5467_ = !lean_is_exclusive(v___x_5459_);
if (v_isSharedCheck_5467_ == 0)
{
v___x_5462_ = v___x_5459_;
v_isShared_5463_ = v_isSharedCheck_5467_;
goto v_resetjp_5461_;
}
else
{
lean_inc(v_a_5460_);
lean_dec(v___x_5459_);
v___x_5462_ = lean_box(0);
v_isShared_5463_ = v_isSharedCheck_5467_;
goto v_resetjp_5461_;
}
v_resetjp_5461_:
{
lean_object* v___x_5465_; 
if (v_isShared_5463_ == 0)
{
v___x_5465_ = v___x_5462_;
goto v_reusejp_5464_;
}
else
{
lean_object* v_reuseFailAlloc_5466_; 
v_reuseFailAlloc_5466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5466_, 0, v_a_5460_);
v___x_5465_ = v_reuseFailAlloc_5466_;
goto v_reusejp_5464_;
}
v_reusejp_5464_:
{
return v___x_5465_;
}
}
}
}
else
{
lean_dec_ref(v_xh_5433_);
lean_dec(v_h_x3f_5431_);
v___y_5447_ = v___y_5434_;
v___y_5448_ = v___y_5435_;
v___y_5449_ = v___y_5436_;
v___y_5450_ = v___y_5437_;
v___y_5451_ = v___y_5438_;
v___y_5452_ = v___y_5439_;
v___y_5453_ = v___y_5440_;
goto v___jp_5446_;
}
v___jp_5446_:
{
uint8_t v___x_5454_; uint8_t v___x_5455_; lean_object* v___x_5456_; 
v___x_5454_ = 0;
v___x_5455_ = 1;
v___x_5456_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_a_5430_, v___x_5454_, v_snd_5424_, v___f_5445_, v___x_5455_, v___y_5447_, v___y_5448_, v___y_5449_, v___y_5450_, v___y_5451_, v___y_5452_, v___y_5453_);
return v___x_5456_;
}
}
else
{
lean_object* v_a_5468_; lean_object* v___x_5470_; uint8_t v_isShared_5471_; uint8_t v_isSharedCheck_5475_; 
lean_dec_ref(v_xh_5433_);
lean_dec(v_h_x3f_5431_);
lean_dec(v_a_5430_);
lean_dec(v___y_5429_);
lean_dec(v_body_5427_);
lean_dec(v___x_5426_);
lean_dec_ref(v___f_5425_);
lean_dec_ref(v_snd_5424_);
lean_dec(v_u_5423_);
lean_dec_ref(v_a_5422_);
lean_dec_ref(v_a_5421_);
v_a_5468_ = lean_ctor_get(v___x_5443_, 0);
v_isSharedCheck_5475_ = !lean_is_exclusive(v___x_5443_);
if (v_isSharedCheck_5475_ == 0)
{
v___x_5470_ = v___x_5443_;
v_isShared_5471_ = v_isSharedCheck_5475_;
goto v_resetjp_5469_;
}
else
{
lean_inc(v_a_5468_);
lean_dec(v___x_5443_);
v___x_5470_ = lean_box(0);
v_isShared_5471_ = v_isSharedCheck_5475_;
goto v_resetjp_5469_;
}
v_resetjp_5469_:
{
lean_object* v___x_5473_; 
if (v_isShared_5471_ == 0)
{
v___x_5473_ = v___x_5470_;
goto v_reusejp_5472_;
}
else
{
lean_object* v_reuseFailAlloc_5474_; 
v_reuseFailAlloc_5474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5474_, 0, v_a_5468_);
v___x_5473_ = v_reuseFailAlloc_5474_;
goto v_reusejp_5472_;
}
v_reusejp_5472_:
{
return v___x_5473_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__10___boxed(lean_object** _args){
lean_object* v___x_5476_ = _args[0];
lean_object* v___x_5477_ = _args[1];
lean_object* v_x_5478_ = _args[2];
lean_object* v_a_5479_ = _args[3];
lean_object* v_a_5480_ = _args[4];
lean_object* v_u_5481_ = _args[5];
lean_object* v_snd_5482_ = _args[6];
lean_object* v___f_5483_ = _args[7];
lean_object* v___x_5484_ = _args[8];
lean_object* v_body_5485_ = _args[9];
lean_object* v___x_5486_ = _args[10];
lean_object* v___y_5487_ = _args[11];
lean_object* v_a_5488_ = _args[12];
lean_object* v_h_x3f_5489_ = _args[13];
lean_object* v___x_5490_ = _args[14];
lean_object* v_xh_5491_ = _args[15];
lean_object* v___y_5492_ = _args[16];
lean_object* v___y_5493_ = _args[17];
lean_object* v___y_5494_ = _args[18];
lean_object* v___y_5495_ = _args[19];
lean_object* v___y_5496_ = _args[20];
lean_object* v___y_5497_ = _args[21];
lean_object* v___y_5498_ = _args[22];
lean_object* v___y_5499_ = _args[23];
_start:
{
uint8_t v___x_89910__boxed_5500_; lean_object* v_res_5501_; 
v___x_89910__boxed_5500_ = lean_unbox(v___x_5486_);
v_res_5501_ = l_Lean_Elab_Do_elabDoFor___lam__10(v___x_5476_, v___x_5477_, v_x_5478_, v_a_5479_, v_a_5480_, v_u_5481_, v_snd_5482_, v___f_5483_, v___x_5484_, v_body_5485_, v___x_89910__boxed_5500_, v___y_5487_, v_a_5488_, v_h_x3f_5489_, v___x_5490_, v_xh_5491_, v___y_5492_, v___y_5493_, v___y_5494_, v___y_5495_, v___y_5496_, v___y_5497_, v___y_5498_);
lean_dec(v___y_5498_);
lean_dec_ref(v___y_5497_);
lean_dec(v___y_5496_);
lean_dec_ref(v___y_5495_);
lean_dec(v___y_5494_);
lean_dec_ref(v___y_5493_);
lean_dec_ref(v___y_5492_);
lean_dec(v___x_5490_);
lean_dec(v___x_5477_);
lean_dec_ref(v___x_5476_);
return v_res_5501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__11(lean_object* v_a_5507_, lean_object* v_a_5508_, lean_object* v___x_5509_, lean_object* v_a_5510_, lean_object* v_a_5511_, lean_object* v_val_5512_, lean_object* v_a_5513_, lean_object* v_x_5514_, lean_object* v___y_5515_, lean_object* v___y_5516_, lean_object* v___y_5517_, lean_object* v___y_5518_, lean_object* v___y_5519_, lean_object* v___y_5520_, lean_object* v___y_5521_){
_start:
{
lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___x_5528_; lean_object* v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; 
v___x_5523_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___lam__11___closed__2));
v___x_5524_ = lean_box(0);
v___x_5525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5525_, 0, v_a_5507_);
lean_ctor_set(v___x_5525_, 1, v___x_5524_);
v___x_5526_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5526_, 0, v_a_5508_);
lean_ctor_set(v___x_5526_, 1, v___x_5525_);
v___x_5527_ = l_Lean_mkConst(v___x_5523_, v___x_5526_);
v___x_5528_ = l_Lean_instInhabitedExpr;
v___x_5529_ = lean_array_get_borrowed(v___x_5528_, v_x_5514_, v___x_5509_);
lean_inc(v___x_5529_);
v___x_5530_ = l_Lean_mkApp5(v___x_5527_, v_a_5510_, v_a_5511_, v_val_5512_, v_a_5513_, v___x_5529_);
v___x_5531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5531_, 0, v___x_5530_);
return v___x_5531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___lam__11___boxed(lean_object* v_a_5532_, lean_object* v_a_5533_, lean_object* v___x_5534_, lean_object* v_a_5535_, lean_object* v_a_5536_, lean_object* v_val_5537_, lean_object* v_a_5538_, lean_object* v_x_5539_, lean_object* v___y_5540_, lean_object* v___y_5541_, lean_object* v___y_5542_, lean_object* v___y_5543_, lean_object* v___y_5544_, lean_object* v___y_5545_, lean_object* v___y_5546_, lean_object* v___y_5547_){
_start:
{
lean_object* v_res_5548_; 
v_res_5548_ = l_Lean_Elab_Do_elabDoFor___lam__11(v_a_5532_, v_a_5533_, v___x_5534_, v_a_5535_, v_a_5536_, v_val_5537_, v_a_5538_, v_x_5539_, v___y_5540_, v___y_5541_, v___y_5542_, v___y_5543_, v___y_5544_, v___y_5545_, v___y_5546_);
lean_dec(v___y_5546_);
lean_dec_ref(v___y_5545_);
lean_dec(v___y_5544_);
lean_dec_ref(v___y_5543_);
lean_dec(v___y_5542_);
lean_dec_ref(v___y_5541_);
lean_dec_ref(v___y_5540_);
lean_dec_ref(v_x_5539_);
lean_dec(v___x_5534_);
return v_res_5548_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__5(size_t v_sz_5549_, size_t v_i_5550_, lean_object* v_bs_5551_){
_start:
{
uint8_t v___x_5552_; 
v___x_5552_ = lean_usize_dec_lt(v_i_5550_, v_sz_5549_);
if (v___x_5552_ == 0)
{
return v_bs_5551_;
}
else
{
lean_object* v_v_5553_; lean_object* v___x_5554_; lean_object* v_bs_x27_5555_; lean_object* v___x_5556_; size_t v___x_5557_; size_t v___x_5558_; lean_object* v___x_5559_; 
v_v_5553_ = lean_array_uget(v_bs_5551_, v_i_5550_);
v___x_5554_ = lean_unsigned_to_nat(0u);
v_bs_x27_5555_ = lean_array_uset(v_bs_5551_, v_i_5550_, v___x_5554_);
v___x_5556_ = l_Lean_Elab_Do_MutVar_getId(v_v_5553_);
lean_dec(v_v_5553_);
v___x_5557_ = ((size_t)1ULL);
v___x_5558_ = lean_usize_add(v_i_5550_, v___x_5557_);
v___x_5559_ = lean_array_uset(v_bs_x27_5555_, v_i_5550_, v___x_5556_);
v_i_5550_ = v___x_5558_;
v_bs_5551_ = v___x_5559_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__5___boxed(lean_object* v_sz_5561_, lean_object* v_i_5562_, lean_object* v_bs_5563_){
_start:
{
size_t v_sz_boxed_5564_; size_t v_i_boxed_5565_; lean_object* v_res_5566_; 
v_sz_boxed_5564_ = lean_unbox_usize(v_sz_5561_);
lean_dec(v_sz_5561_);
v_i_boxed_5565_ = lean_unbox_usize(v_i_5562_);
lean_dec(v_i_5562_);
v_res_5566_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__5(v_sz_boxed_5564_, v_i_boxed_5565_, v_bs_5563_);
return v_res_5566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__6(lean_object* v_a_5567_, lean_object* v_as_5568_, size_t v_i_5569_, size_t v_stop_5570_, lean_object* v_b_5571_){
_start:
{
lean_object* v___y_5573_; uint8_t v___x_5577_; 
v___x_5577_ = lean_usize_dec_eq(v_i_5569_, v_stop_5570_);
if (v___x_5577_ == 0)
{
lean_object* v_reassigns_5578_; lean_object* v___x_5579_; lean_object* v___x_5580_; uint8_t v___x_5581_; 
v_reassigns_5578_ = lean_ctor_get(v_a_5567_, 1);
v___x_5579_ = lean_array_uget_borrowed(v_as_5568_, v_i_5569_);
v___x_5580_ = l_Lean_Elab_Do_MutVar_getId(v___x_5579_);
v___x_5581_ = l_Lean_NameSet_contains(v_reassigns_5578_, v___x_5580_);
lean_dec(v___x_5580_);
if (v___x_5581_ == 0)
{
v___y_5573_ = v_b_5571_;
goto v___jp_5572_;
}
else
{
lean_object* v___x_5582_; 
lean_inc(v___x_5579_);
v___x_5582_ = lean_array_push(v_b_5571_, v___x_5579_);
v___y_5573_ = v___x_5582_;
goto v___jp_5572_;
}
}
else
{
return v_b_5571_;
}
v___jp_5572_:
{
size_t v___x_5574_; size_t v___x_5575_; 
v___x_5574_ = ((size_t)1ULL);
v___x_5575_ = lean_usize_add(v_i_5569_, v___x_5574_);
v_i_5569_ = v___x_5575_;
v_b_5571_ = v___y_5573_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__6___boxed(lean_object* v_a_5583_, lean_object* v_as_5584_, lean_object* v_i_5585_, lean_object* v_stop_5586_, lean_object* v_b_5587_){
_start:
{
size_t v_i_boxed_5588_; size_t v_stop_boxed_5589_; lean_object* v_res_5590_; 
v_i_boxed_5588_ = lean_unbox_usize(v_i_5585_);
lean_dec(v_i_5585_);
v_stop_boxed_5589_ = lean_unbox_usize(v_stop_5586_);
lean_dec(v_stop_5586_);
v_res_5590_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__6(v_a_5583_, v_as_5584_, v_i_boxed_5588_, v_stop_boxed_5589_, v_b_5587_);
lean_dec_ref(v_as_5584_);
lean_dec_ref(v_a_5583_);
return v_res_5590_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0(uint8_t v___y_5598_, uint8_t v_suppressElabErrors_5599_, lean_object* v_x_5600_){
_start:
{
if (lean_obj_tag(v_x_5600_) == 1)
{
lean_object* v_pre_5601_; 
v_pre_5601_ = lean_ctor_get(v_x_5600_, 0);
switch(lean_obj_tag(v_pre_5601_))
{
case 1:
{
lean_object* v_pre_5602_; 
v_pre_5602_ = lean_ctor_get(v_pre_5601_, 0);
switch(lean_obj_tag(v_pre_5602_))
{
case 0:
{
lean_object* v_str_5603_; lean_object* v_str_5604_; lean_object* v___x_5605_; uint8_t v___x_5606_; 
v_str_5603_ = lean_ctor_get(v_x_5600_, 1);
v_str_5604_ = lean_ctor_get(v_pre_5601_, 1);
v___x_5605_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66));
v___x_5606_ = lean_string_dec_eq(v_str_5604_, v___x_5605_);
if (v___x_5606_ == 0)
{
lean_object* v___x_5607_; uint8_t v___x_5608_; 
v___x_5607_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0___closed__0));
v___x_5608_ = lean_string_dec_eq(v_str_5604_, v___x_5607_);
if (v___x_5608_ == 0)
{
return v___y_5598_;
}
else
{
lean_object* v___x_5609_; uint8_t v___x_5610_; 
v___x_5609_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0___closed__1));
v___x_5610_ = lean_string_dec_eq(v_str_5603_, v___x_5609_);
if (v___x_5610_ == 0)
{
return v___y_5598_;
}
else
{
return v_suppressElabErrors_5599_;
}
}
}
else
{
lean_object* v___x_5611_; uint8_t v___x_5612_; 
v___x_5611_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0___closed__2));
v___x_5612_ = lean_string_dec_eq(v_str_5603_, v___x_5611_);
if (v___x_5612_ == 0)
{
return v___y_5598_;
}
else
{
return v_suppressElabErrors_5599_;
}
}
}
case 1:
{
lean_object* v_pre_5613_; 
v_pre_5613_ = lean_ctor_get(v_pre_5602_, 0);
if (lean_obj_tag(v_pre_5613_) == 0)
{
lean_object* v_str_5614_; lean_object* v_str_5615_; lean_object* v_str_5616_; lean_object* v___x_5617_; uint8_t v___x_5618_; 
v_str_5614_ = lean_ctor_get(v_x_5600_, 1);
v_str_5615_ = lean_ctor_get(v_pre_5601_, 1);
v_str_5616_ = lean_ctor_get(v_pre_5602_, 1);
v___x_5617_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0___closed__3));
v___x_5618_ = lean_string_dec_eq(v_str_5616_, v___x_5617_);
if (v___x_5618_ == 0)
{
return v___y_5598_;
}
else
{
lean_object* v___x_5619_; uint8_t v___x_5620_; 
v___x_5619_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0___closed__4));
v___x_5620_ = lean_string_dec_eq(v_str_5615_, v___x_5619_);
if (v___x_5620_ == 0)
{
return v___y_5598_;
}
else
{
lean_object* v___x_5621_; uint8_t v___x_5622_; 
v___x_5621_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0___closed__5));
v___x_5622_ = lean_string_dec_eq(v_str_5614_, v___x_5621_);
if (v___x_5622_ == 0)
{
return v___y_5598_;
}
else
{
return v_suppressElabErrors_5599_;
}
}
}
}
else
{
return v___y_5598_;
}
}
default: 
{
return v___y_5598_;
}
}
}
case 0:
{
lean_object* v_str_5623_; lean_object* v___x_5624_; uint8_t v___x_5625_; 
v_str_5623_ = lean_ctor_get(v_x_5600_, 1);
v___x_5624_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0___closed__6));
v___x_5625_ = lean_string_dec_eq(v_str_5623_, v___x_5624_);
if (v___x_5625_ == 0)
{
return v___y_5598_;
}
else
{
return v_suppressElabErrors_5599_;
}
}
default: 
{
return v___y_5598_;
}
}
}
else
{
return v___y_5598_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0___boxed(lean_object* v___y_5626_, lean_object* v_suppressElabErrors_5627_, lean_object* v_x_5628_){
_start:
{
uint8_t v___y_90160__boxed_5629_; uint8_t v_suppressElabErrors_boxed_5630_; uint8_t v_res_5631_; lean_object* v_r_5632_; 
v___y_90160__boxed_5629_ = lean_unbox(v___y_5626_);
v_suppressElabErrors_boxed_5630_ = lean_unbox(v_suppressElabErrors_5627_);
v_res_5631_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0(v___y_90160__boxed_5629_, v_suppressElabErrors_boxed_5630_, v_x_5628_);
lean_dec(v_x_5628_);
v_r_5632_ = lean_box(v_res_5631_);
return v_r_5632_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg(lean_object* v_ref_5633_, lean_object* v_msgData_5634_, uint8_t v_severity_5635_, uint8_t v_isSilent_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_, lean_object* v___y_5639_, lean_object* v___y_5640_){
_start:
{
uint8_t v___y_5643_; lean_object* v___y_5644_; uint8_t v___y_5645_; lean_object* v___y_5646_; lean_object* v___y_5647_; lean_object* v___y_5648_; lean_object* v___y_5649_; lean_object* v___y_5650_; lean_object* v___y_5651_; lean_object* v___y_5679_; uint8_t v___y_5680_; lean_object* v___y_5681_; uint8_t v___y_5682_; lean_object* v___y_5683_; lean_object* v___y_5684_; uint8_t v___y_5685_; lean_object* v___y_5686_; lean_object* v___y_5704_; uint8_t v___y_5705_; lean_object* v___y_5706_; uint8_t v___y_5707_; lean_object* v___y_5708_; uint8_t v___y_5709_; lean_object* v___y_5710_; lean_object* v___y_5711_; lean_object* v___y_5715_; lean_object* v___y_5716_; uint8_t v___y_5717_; lean_object* v___y_5718_; lean_object* v___y_5719_; uint8_t v___y_5720_; uint8_t v___y_5721_; uint8_t v___x_5726_; lean_object* v___y_5728_; lean_object* v___y_5729_; lean_object* v___y_5730_; lean_object* v___y_5731_; uint8_t v___y_5732_; uint8_t v___y_5733_; uint8_t v___y_5734_; uint8_t v___y_5736_; uint8_t v___x_5751_; 
v___x_5726_ = 2;
v___x_5751_ = l_Lean_instBEqMessageSeverity_beq(v_severity_5635_, v___x_5726_);
if (v___x_5751_ == 0)
{
v___y_5736_ = v___x_5751_;
goto v___jp_5735_;
}
else
{
uint8_t v___x_5752_; 
lean_inc_ref(v_msgData_5634_);
v___x_5752_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_5634_);
v___y_5736_ = v___x_5752_;
goto v___jp_5735_;
}
v___jp_5642_:
{
lean_object* v___x_5652_; lean_object* v_currNamespace_5653_; lean_object* v_openDecls_5654_; lean_object* v_env_5655_; lean_object* v_nextMacroScope_5656_; lean_object* v_ngen_5657_; lean_object* v_auxDeclNGen_5658_; lean_object* v_traceState_5659_; lean_object* v_cache_5660_; lean_object* v_messages_5661_; lean_object* v_infoState_5662_; lean_object* v_snapshotTasks_5663_; lean_object* v___x_5665_; uint8_t v_isShared_5666_; uint8_t v_isSharedCheck_5677_; 
v___x_5652_ = lean_st_ref_take(v___y_5651_);
v_currNamespace_5653_ = lean_ctor_get(v___y_5650_, 6);
v_openDecls_5654_ = lean_ctor_get(v___y_5650_, 7);
v_env_5655_ = lean_ctor_get(v___x_5652_, 0);
v_nextMacroScope_5656_ = lean_ctor_get(v___x_5652_, 1);
v_ngen_5657_ = lean_ctor_get(v___x_5652_, 2);
v_auxDeclNGen_5658_ = lean_ctor_get(v___x_5652_, 3);
v_traceState_5659_ = lean_ctor_get(v___x_5652_, 4);
v_cache_5660_ = lean_ctor_get(v___x_5652_, 5);
v_messages_5661_ = lean_ctor_get(v___x_5652_, 6);
v_infoState_5662_ = lean_ctor_get(v___x_5652_, 7);
v_snapshotTasks_5663_ = lean_ctor_get(v___x_5652_, 8);
v_isSharedCheck_5677_ = !lean_is_exclusive(v___x_5652_);
if (v_isSharedCheck_5677_ == 0)
{
v___x_5665_ = v___x_5652_;
v_isShared_5666_ = v_isSharedCheck_5677_;
goto v_resetjp_5664_;
}
else
{
lean_inc(v_snapshotTasks_5663_);
lean_inc(v_infoState_5662_);
lean_inc(v_messages_5661_);
lean_inc(v_cache_5660_);
lean_inc(v_traceState_5659_);
lean_inc(v_auxDeclNGen_5658_);
lean_inc(v_ngen_5657_);
lean_inc(v_nextMacroScope_5656_);
lean_inc(v_env_5655_);
lean_dec(v___x_5652_);
v___x_5665_ = lean_box(0);
v_isShared_5666_ = v_isSharedCheck_5677_;
goto v_resetjp_5664_;
}
v_resetjp_5664_:
{
lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; lean_object* v___x_5672_; 
lean_inc(v_openDecls_5654_);
lean_inc(v_currNamespace_5653_);
v___x_5667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5667_, 0, v_currNamespace_5653_);
lean_ctor_set(v___x_5667_, 1, v_openDecls_5654_);
v___x_5668_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_5668_, 0, v___x_5667_);
lean_ctor_set(v___x_5668_, 1, v___y_5649_);
lean_inc_ref(v___y_5646_);
lean_inc_ref(v___y_5647_);
v___x_5669_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_5669_, 0, v___y_5647_);
lean_ctor_set(v___x_5669_, 1, v___y_5648_);
lean_ctor_set(v___x_5669_, 2, v___y_5644_);
lean_ctor_set(v___x_5669_, 3, v___y_5646_);
lean_ctor_set(v___x_5669_, 4, v___x_5668_);
lean_ctor_set_uint8(v___x_5669_, sizeof(void*)*5, v___y_5645_);
lean_ctor_set_uint8(v___x_5669_, sizeof(void*)*5 + 1, v___y_5643_);
lean_ctor_set_uint8(v___x_5669_, sizeof(void*)*5 + 2, v_isSilent_5636_);
v___x_5670_ = l_Lean_MessageLog_add(v___x_5669_, v_messages_5661_);
if (v_isShared_5666_ == 0)
{
lean_ctor_set(v___x_5665_, 6, v___x_5670_);
v___x_5672_ = v___x_5665_;
goto v_reusejp_5671_;
}
else
{
lean_object* v_reuseFailAlloc_5676_; 
v_reuseFailAlloc_5676_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5676_, 0, v_env_5655_);
lean_ctor_set(v_reuseFailAlloc_5676_, 1, v_nextMacroScope_5656_);
lean_ctor_set(v_reuseFailAlloc_5676_, 2, v_ngen_5657_);
lean_ctor_set(v_reuseFailAlloc_5676_, 3, v_auxDeclNGen_5658_);
lean_ctor_set(v_reuseFailAlloc_5676_, 4, v_traceState_5659_);
lean_ctor_set(v_reuseFailAlloc_5676_, 5, v_cache_5660_);
lean_ctor_set(v_reuseFailAlloc_5676_, 6, v___x_5670_);
lean_ctor_set(v_reuseFailAlloc_5676_, 7, v_infoState_5662_);
lean_ctor_set(v_reuseFailAlloc_5676_, 8, v_snapshotTasks_5663_);
v___x_5672_ = v_reuseFailAlloc_5676_;
goto v_reusejp_5671_;
}
v_reusejp_5671_:
{
lean_object* v___x_5673_; lean_object* v___x_5674_; lean_object* v___x_5675_; 
v___x_5673_ = lean_st_ref_put(v___y_5651_, v___x_5672_);
v___x_5674_ = lean_box(0);
v___x_5675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5675_, 0, v___x_5674_);
return v___x_5675_;
}
}
}
v___jp_5678_:
{
lean_object* v___x_5687_; lean_object* v___x_5688_; lean_object* v_a_5689_; lean_object* v___x_5691_; uint8_t v_isShared_5692_; uint8_t v_isSharedCheck_5702_; 
v___x_5687_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_5634_);
v___x_5688_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0_spec__0_spec__1(v___x_5687_, v___y_5637_, v___y_5638_, v___y_5639_, v___y_5640_);
v_a_5689_ = lean_ctor_get(v___x_5688_, 0);
v_isSharedCheck_5702_ = !lean_is_exclusive(v___x_5688_);
if (v_isSharedCheck_5702_ == 0)
{
v___x_5691_ = v___x_5688_;
v_isShared_5692_ = v_isSharedCheck_5702_;
goto v_resetjp_5690_;
}
else
{
lean_inc(v_a_5689_);
lean_dec(v___x_5688_);
v___x_5691_ = lean_box(0);
v_isShared_5692_ = v_isSharedCheck_5702_;
goto v_resetjp_5690_;
}
v_resetjp_5690_:
{
lean_object* v___x_5693_; lean_object* v___x_5694_; lean_object* v___x_5695_; lean_object* v___x_5696_; 
lean_inc_ref_n(v___y_5681_, 2);
v___x_5693_ = l_Lean_FileMap_toPosition(v___y_5681_, v___y_5684_);
lean_dec(v___y_5684_);
v___x_5694_ = l_Lean_FileMap_toPosition(v___y_5681_, v___y_5686_);
lean_dec(v___y_5686_);
v___x_5695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5695_, 0, v___x_5694_);
v___x_5696_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__64));
if (v___y_5685_ == 0)
{
lean_del_object(v___x_5691_);
lean_dec_ref(v___y_5679_);
v___y_5643_ = v___y_5680_;
v___y_5644_ = v___x_5695_;
v___y_5645_ = v___y_5682_;
v___y_5646_ = v___x_5696_;
v___y_5647_ = v___y_5683_;
v___y_5648_ = v___x_5693_;
v___y_5649_ = v_a_5689_;
v___y_5650_ = v___y_5639_;
v___y_5651_ = v___y_5640_;
goto v___jp_5642_;
}
else
{
uint8_t v___x_5697_; 
lean_inc(v_a_5689_);
v___x_5697_ = l_Lean_MessageData_hasTag(v___y_5679_, v_a_5689_);
if (v___x_5697_ == 0)
{
lean_object* v___x_5698_; lean_object* v___x_5700_; 
lean_dec_ref_known(v___x_5695_, 1);
lean_dec_ref(v___x_5693_);
lean_dec(v_a_5689_);
v___x_5698_ = lean_box(0);
if (v_isShared_5692_ == 0)
{
lean_ctor_set(v___x_5691_, 0, v___x_5698_);
v___x_5700_ = v___x_5691_;
goto v_reusejp_5699_;
}
else
{
lean_object* v_reuseFailAlloc_5701_; 
v_reuseFailAlloc_5701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5701_, 0, v___x_5698_);
v___x_5700_ = v_reuseFailAlloc_5701_;
goto v_reusejp_5699_;
}
v_reusejp_5699_:
{
return v___x_5700_;
}
}
else
{
lean_del_object(v___x_5691_);
v___y_5643_ = v___y_5680_;
v___y_5644_ = v___x_5695_;
v___y_5645_ = v___y_5682_;
v___y_5646_ = v___x_5696_;
v___y_5647_ = v___y_5683_;
v___y_5648_ = v___x_5693_;
v___y_5649_ = v_a_5689_;
v___y_5650_ = v___y_5639_;
v___y_5651_ = v___y_5640_;
goto v___jp_5642_;
}
}
}
}
v___jp_5703_:
{
lean_object* v___x_5712_; 
v___x_5712_ = l_Lean_Syntax_getTailPos_x3f(v___y_5710_, v___y_5707_);
lean_dec(v___y_5710_);
if (lean_obj_tag(v___x_5712_) == 0)
{
lean_inc(v___y_5711_);
v___y_5679_ = v___y_5704_;
v___y_5680_ = v___y_5705_;
v___y_5681_ = v___y_5706_;
v___y_5682_ = v___y_5707_;
v___y_5683_ = v___y_5708_;
v___y_5684_ = v___y_5711_;
v___y_5685_ = v___y_5709_;
v___y_5686_ = v___y_5711_;
goto v___jp_5678_;
}
else
{
lean_object* v_val_5713_; 
v_val_5713_ = lean_ctor_get(v___x_5712_, 0);
lean_inc(v_val_5713_);
lean_dec_ref_known(v___x_5712_, 1);
v___y_5679_ = v___y_5704_;
v___y_5680_ = v___y_5705_;
v___y_5681_ = v___y_5706_;
v___y_5682_ = v___y_5707_;
v___y_5683_ = v___y_5708_;
v___y_5684_ = v___y_5711_;
v___y_5685_ = v___y_5709_;
v___y_5686_ = v_val_5713_;
goto v___jp_5678_;
}
}
v___jp_5714_:
{
lean_object* v_ref_5722_; lean_object* v___x_5723_; 
v_ref_5722_ = l_Lean_replaceRef(v_ref_5633_, v___y_5719_);
v___x_5723_ = l_Lean_Syntax_getPos_x3f(v_ref_5722_, v___y_5717_);
if (lean_obj_tag(v___x_5723_) == 0)
{
lean_object* v___x_5724_; 
v___x_5724_ = lean_unsigned_to_nat(0u);
v___y_5704_ = v___y_5715_;
v___y_5705_ = v___y_5721_;
v___y_5706_ = v___y_5716_;
v___y_5707_ = v___y_5717_;
v___y_5708_ = v___y_5718_;
v___y_5709_ = v___y_5720_;
v___y_5710_ = v_ref_5722_;
v___y_5711_ = v___x_5724_;
goto v___jp_5703_;
}
else
{
lean_object* v_val_5725_; 
v_val_5725_ = lean_ctor_get(v___x_5723_, 0);
lean_inc(v_val_5725_);
lean_dec_ref_known(v___x_5723_, 1);
v___y_5704_ = v___y_5715_;
v___y_5705_ = v___y_5721_;
v___y_5706_ = v___y_5716_;
v___y_5707_ = v___y_5717_;
v___y_5708_ = v___y_5718_;
v___y_5709_ = v___y_5720_;
v___y_5710_ = v_ref_5722_;
v___y_5711_ = v_val_5725_;
goto v___jp_5703_;
}
}
v___jp_5727_:
{
if (v___y_5734_ == 0)
{
v___y_5715_ = v___y_5730_;
v___y_5716_ = v___y_5728_;
v___y_5717_ = v___y_5733_;
v___y_5718_ = v___y_5729_;
v___y_5719_ = v___y_5731_;
v___y_5720_ = v___y_5732_;
v___y_5721_ = v_severity_5635_;
goto v___jp_5714_;
}
else
{
v___y_5715_ = v___y_5730_;
v___y_5716_ = v___y_5728_;
v___y_5717_ = v___y_5733_;
v___y_5718_ = v___y_5729_;
v___y_5719_ = v___y_5731_;
v___y_5720_ = v___y_5732_;
v___y_5721_ = v___x_5726_;
goto v___jp_5714_;
}
}
v___jp_5735_:
{
if (v___y_5736_ == 0)
{
lean_object* v_fileName_5737_; lean_object* v_fileMap_5738_; lean_object* v_options_5739_; lean_object* v_ref_5740_; uint8_t v_suppressElabErrors_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___f_5744_; uint8_t v___x_5745_; uint8_t v___x_5746_; 
v_fileName_5737_ = lean_ctor_get(v___y_5639_, 0);
v_fileMap_5738_ = lean_ctor_get(v___y_5639_, 1);
v_options_5739_ = lean_ctor_get(v___y_5639_, 2);
v_ref_5740_ = lean_ctor_get(v___y_5639_, 5);
v_suppressElabErrors_5741_ = lean_ctor_get_uint8(v___y_5639_, sizeof(void*)*14 + 1);
v___x_5742_ = lean_box(v___y_5736_);
v___x_5743_ = lean_box(v_suppressElabErrors_5741_);
v___f_5744_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_5744_, 0, v___x_5742_);
lean_closure_set(v___f_5744_, 1, v___x_5743_);
v___x_5745_ = 1;
v___x_5746_ = l_Lean_instBEqMessageSeverity_beq(v_severity_5635_, v___x_5745_);
if (v___x_5746_ == 0)
{
v___y_5728_ = v_fileMap_5738_;
v___y_5729_ = v_fileName_5737_;
v___y_5730_ = v___f_5744_;
v___y_5731_ = v_ref_5740_;
v___y_5732_ = v_suppressElabErrors_5741_;
v___y_5733_ = v___y_5736_;
v___y_5734_ = v___x_5746_;
goto v___jp_5727_;
}
else
{
lean_object* v___x_5747_; uint8_t v___x_5748_; 
v___x_5747_ = l_Lean_warningAsError;
v___x_5748_ = l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__10(v_options_5739_, v___x_5747_);
v___y_5728_ = v_fileMap_5738_;
v___y_5729_ = v_fileName_5737_;
v___y_5730_ = v___f_5744_;
v___y_5731_ = v_ref_5740_;
v___y_5732_ = v_suppressElabErrors_5741_;
v___y_5733_ = v___y_5736_;
v___y_5734_ = v___x_5748_;
goto v___jp_5727_;
}
}
else
{
lean_object* v___x_5749_; lean_object* v___x_5750_; 
lean_dec_ref(v_msgData_5634_);
v___x_5749_ = lean_box(0);
v___x_5750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5750_, 0, v___x_5749_);
return v___x_5750_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg___boxed(lean_object* v_ref_5753_, lean_object* v_msgData_5754_, lean_object* v_severity_5755_, lean_object* v_isSilent_5756_, lean_object* v___y_5757_, lean_object* v___y_5758_, lean_object* v___y_5759_, lean_object* v___y_5760_, lean_object* v___y_5761_){
_start:
{
uint8_t v_severity_boxed_5762_; uint8_t v_isSilent_boxed_5763_; lean_object* v_res_5764_; 
v_severity_boxed_5762_ = lean_unbox(v_severity_5755_);
v_isSilent_boxed_5763_ = lean_unbox(v_isSilent_5756_);
v_res_5764_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg(v_ref_5753_, v_msgData_5754_, v_severity_boxed_5762_, v_isSilent_boxed_5763_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_);
lean_dec(v___y_5760_);
lean_dec_ref(v___y_5759_);
lean_dec(v___y_5758_);
lean_dec_ref(v___y_5757_);
lean_dec(v_ref_5753_);
return v_res_5764_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11(lean_object* v_ref_5765_, lean_object* v_msgData_5766_, lean_object* v___y_5767_, lean_object* v___y_5768_, lean_object* v___y_5769_, lean_object* v___y_5770_, lean_object* v___y_5771_, lean_object* v___y_5772_, lean_object* v___y_5773_){
_start:
{
uint8_t v___x_5775_; uint8_t v___x_5776_; lean_object* v___x_5777_; 
v___x_5775_ = 1;
v___x_5776_ = 0;
v___x_5777_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg(v_ref_5765_, v_msgData_5766_, v___x_5775_, v___x_5776_, v___y_5770_, v___y_5771_, v___y_5772_, v___y_5773_);
return v___x_5777_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11___boxed(lean_object* v_ref_5778_, lean_object* v_msgData_5779_, lean_object* v___y_5780_, lean_object* v___y_5781_, lean_object* v___y_5782_, lean_object* v___y_5783_, lean_object* v___y_5784_, lean_object* v___y_5785_, lean_object* v___y_5786_, lean_object* v___y_5787_){
_start:
{
lean_object* v_res_5788_; 
v_res_5788_ = l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11(v_ref_5778_, v_msgData_5779_, v___y_5780_, v___y_5781_, v___y_5782_, v___y_5783_, v___y_5784_, v___y_5785_, v___y_5786_);
lean_dec(v___y_5786_);
lean_dec_ref(v___y_5785_);
lean_dec(v___y_5784_);
lean_dec_ref(v___y_5783_);
lean_dec(v___y_5782_);
lean_dec_ref(v___y_5781_);
lean_dec_ref(v___y_5780_);
lean_dec(v_ref_5778_);
return v_res_5788_;
}
}
static lean_object* _init_l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7___closed__1(void){
_start:
{
lean_object* v___x_5790_; lean_object* v___x_5791_; 
v___x_5790_ = ((lean_object*)(l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7___closed__0));
v___x_5791_ = l_Lean_stringToMessageData(v___x_5790_);
return v___x_5791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7(lean_object* v_kw_5792_, lean_object* v_what_5793_, lean_object* v___y_5794_, lean_object* v___y_5795_, lean_object* v___y_5796_, lean_object* v___y_5797_, lean_object* v___y_5798_, lean_object* v___y_5799_, lean_object* v___y_5800_){
_start:
{
lean_object* v_options_5802_; lean_object* v___x_5803_; uint8_t v___x_5804_; 
v_options_5802_ = lean_ctor_get(v___y_5799_, 2);
v___x_5803_ = l_Lean_Elab_Do_experimental_intrinsic;
v___x_5804_ = l_Lean_Option_get___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__10(v_options_5802_, v___x_5803_);
if (v___x_5804_ == 0)
{
lean_object* v___x_5805_; lean_object* v___x_5806_; lean_object* v___x_5807_; lean_object* v___x_5808_; lean_object* v___x_5809_; 
v___x_5805_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__1, &l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders___closed__1);
v___x_5806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5806_, 0, v___x_5805_);
lean_ctor_set(v___x_5806_, 1, v_what_5793_);
v___x_5807_ = lean_obj_once(&l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7___closed__1, &l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7___closed__1_once, _init_l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7___closed__1);
v___x_5808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5808_, 0, v___x_5806_);
lean_ctor_set(v___x_5808_, 1, v___x_5807_);
v___x_5809_ = l_Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11(v_kw_5792_, v___x_5808_, v___y_5794_, v___y_5795_, v___y_5796_, v___y_5797_, v___y_5798_, v___y_5799_, v___y_5800_);
return v___x_5809_;
}
else
{
lean_object* v___x_5810_; lean_object* v___x_5811_; 
lean_dec_ref(v_what_5793_);
v___x_5810_ = lean_box(0);
v___x_5811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5811_, 0, v___x_5810_);
return v___x_5811_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7___boxed(lean_object* v_kw_5812_, lean_object* v_what_5813_, lean_object* v___y_5814_, lean_object* v___y_5815_, lean_object* v___y_5816_, lean_object* v___y_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_, lean_object* v___y_5820_, lean_object* v___y_5821_){
_start:
{
lean_object* v_res_5822_; 
v_res_5822_ = l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7(v_kw_5812_, v_what_5813_, v___y_5814_, v___y_5815_, v___y_5816_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_);
lean_dec(v___y_5820_);
lean_dec_ref(v___y_5819_);
lean_dec(v___y_5818_);
lean_dec_ref(v___y_5817_);
lean_dec(v___y_5816_);
lean_dec_ref(v___y_5815_);
lean_dec_ref(v___y_5814_);
lean_dec(v_kw_5812_);
return v_res_5822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___lam__0(lean_object* v___x_5823_, lean_object* v_a_5824_, lean_object* v___y_5825_, lean_object* v___y_5826_, lean_object* v___y_5827_, lean_object* v___y_5828_, lean_object* v___y_5829_, lean_object* v___y_5830_, lean_object* v___y_5831_){
_start:
{
lean_object* v___x_5833_; lean_object* v___x_88346__overap_5834_; lean_object* v___x_5835_; 
v___x_5833_ = l_Lean_instInhabitedExpr;
v___x_88346__overap_5834_ = l_instInhabitedOfMonad___redArg(v___x_5823_, v___x_5833_);
lean_inc(v___y_5831_);
lean_inc_ref(v___y_5830_);
lean_inc(v___y_5829_);
lean_inc_ref(v___y_5828_);
lean_inc(v___y_5827_);
lean_inc_ref(v___y_5826_);
lean_inc_ref(v___y_5825_);
v___x_5835_ = lean_apply_8(v___x_88346__overap_5834_, v___y_5825_, v___y_5826_, v___y_5827_, v___y_5828_, v___y_5829_, v___y_5830_, v___y_5831_, lean_box(0));
return v___x_5835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___lam__0___boxed(lean_object* v___x_5836_, lean_object* v_a_5837_, lean_object* v___y_5838_, lean_object* v___y_5839_, lean_object* v___y_5840_, lean_object* v___y_5841_, lean_object* v___y_5842_, lean_object* v___y_5843_, lean_object* v___y_5844_, lean_object* v___y_5845_){
_start:
{
lean_object* v_res_5846_; 
v_res_5846_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___lam__0(v___x_5836_, v_a_5837_, v___y_5838_, v___y_5839_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_);
lean_dec(v___y_5844_);
lean_dec_ref(v___y_5843_);
lean_dec(v___y_5842_);
lean_dec_ref(v___y_5841_);
lean_dec(v___y_5840_);
lean_dec_ref(v___y_5839_);
lean_dec_ref(v___y_5838_);
lean_dec_ref(v_a_5837_);
return v_res_5846_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__0(void){
_start:
{
lean_object* v___x_5847_; 
v___x_5847_ = l_instMonadEIO(lean_box(0));
return v___x_5847_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__1(void){
_start:
{
lean_object* v___x_5848_; lean_object* v___x_5849_; 
v___x_5848_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__0);
v___x_5849_ = l_StateRefT_x27_instMonad___redArg(v___x_5848_);
return v___x_5849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___lam__1___boxed(lean_object* v_acc_5856_, lean_object* v_declInfos_5857_, lean_object* v_k_5858_, lean_object* v_kind_5859_, lean_object* v_x_5860_, lean_object* v___y_5861_, lean_object* v___y_5862_, lean_object* v___y_5863_, lean_object* v___y_5864_, lean_object* v___y_5865_, lean_object* v___y_5866_, lean_object* v___y_5867_, lean_object* v___y_5868_){
_start:
{
uint8_t v_kind_boxed_5869_; lean_object* v_res_5870_; 
v_kind_boxed_5869_ = lean_unbox(v_kind_5859_);
v_res_5870_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___lam__1(v_acc_5856_, v_declInfos_5857_, v_k_5858_, v_kind_boxed_5869_, v_x_5860_, v___y_5861_, v___y_5862_, v___y_5863_, v___y_5864_, v___y_5865_, v___y_5866_, v___y_5867_);
lean_dec(v___y_5867_);
lean_dec_ref(v___y_5866_);
lean_dec(v___y_5865_);
lean_dec_ref(v___y_5864_);
lean_dec(v___y_5863_);
lean_dec_ref(v___y_5862_);
lean_dec_ref(v___y_5861_);
return v_res_5870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8(lean_object* v_declInfos_5871_, lean_object* v_k_5872_, uint8_t v_kind_5873_, lean_object* v_acc_5874_, lean_object* v___y_5875_, lean_object* v___y_5876_, lean_object* v___y_5877_, lean_object* v___y_5878_, lean_object* v___y_5879_, lean_object* v___y_5880_, lean_object* v___y_5881_){
_start:
{
lean_object* v___x_5883_; lean_object* v_toApplicative_5884_; lean_object* v_toFunctor_5885_; lean_object* v_toSeq_5886_; lean_object* v_toSeqLeft_5887_; lean_object* v_toSeqRight_5888_; lean_object* v___f_5889_; lean_object* v___f_5890_; lean_object* v___f_5891_; lean_object* v___f_5892_; lean_object* v___x_5893_; lean_object* v___f_5894_; lean_object* v___f_5895_; lean_object* v___f_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v_toApplicative_5900_; lean_object* v___x_5902_; uint8_t v_isShared_5903_; uint8_t v_isSharedCheck_5980_; 
v___x_5883_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__1);
v_toApplicative_5884_ = lean_ctor_get(v___x_5883_, 0);
v_toFunctor_5885_ = lean_ctor_get(v_toApplicative_5884_, 0);
v_toSeq_5886_ = lean_ctor_get(v_toApplicative_5884_, 2);
v_toSeqLeft_5887_ = lean_ctor_get(v_toApplicative_5884_, 3);
v_toSeqRight_5888_ = lean_ctor_get(v_toApplicative_5884_, 4);
v___f_5889_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__2));
v___f_5890_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__3));
lean_inc_ref_n(v_toFunctor_5885_, 2);
v___f_5891_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5891_, 0, v_toFunctor_5885_);
v___f_5892_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5892_, 0, v_toFunctor_5885_);
v___x_5893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5893_, 0, v___f_5891_);
lean_ctor_set(v___x_5893_, 1, v___f_5892_);
lean_inc(v_toSeqRight_5888_);
v___f_5894_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5894_, 0, v_toSeqRight_5888_);
lean_inc(v_toSeqLeft_5887_);
v___f_5895_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5895_, 0, v_toSeqLeft_5887_);
lean_inc(v_toSeq_5886_);
v___f_5896_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5896_, 0, v_toSeq_5886_);
v___x_5897_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5897_, 0, v___x_5893_);
lean_ctor_set(v___x_5897_, 1, v___f_5889_);
lean_ctor_set(v___x_5897_, 2, v___f_5896_);
lean_ctor_set(v___x_5897_, 3, v___f_5895_);
lean_ctor_set(v___x_5897_, 4, v___f_5894_);
v___x_5898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5898_, 0, v___x_5897_);
lean_ctor_set(v___x_5898_, 1, v___f_5890_);
v___x_5899_ = l_StateRefT_x27_instMonad___redArg(v___x_5898_);
v_toApplicative_5900_ = lean_ctor_get(v___x_5899_, 0);
v_isSharedCheck_5980_ = !lean_is_exclusive(v___x_5899_);
if (v_isSharedCheck_5980_ == 0)
{
lean_object* v_unused_5981_; 
v_unused_5981_ = lean_ctor_get(v___x_5899_, 1);
lean_dec(v_unused_5981_);
v___x_5902_ = v___x_5899_;
v_isShared_5903_ = v_isSharedCheck_5980_;
goto v_resetjp_5901_;
}
else
{
lean_inc(v_toApplicative_5900_);
lean_dec(v___x_5899_);
v___x_5902_ = lean_box(0);
v_isShared_5903_ = v_isSharedCheck_5980_;
goto v_resetjp_5901_;
}
v_resetjp_5901_:
{
lean_object* v_toFunctor_5904_; lean_object* v_toSeq_5905_; lean_object* v_toSeqLeft_5906_; lean_object* v_toSeqRight_5907_; lean_object* v___x_5909_; uint8_t v_isShared_5910_; uint8_t v_isSharedCheck_5978_; 
v_toFunctor_5904_ = lean_ctor_get(v_toApplicative_5900_, 0);
v_toSeq_5905_ = lean_ctor_get(v_toApplicative_5900_, 2);
v_toSeqLeft_5906_ = lean_ctor_get(v_toApplicative_5900_, 3);
v_toSeqRight_5907_ = lean_ctor_get(v_toApplicative_5900_, 4);
v_isSharedCheck_5978_ = !lean_is_exclusive(v_toApplicative_5900_);
if (v_isSharedCheck_5978_ == 0)
{
lean_object* v_unused_5979_; 
v_unused_5979_ = lean_ctor_get(v_toApplicative_5900_, 1);
lean_dec(v_unused_5979_);
v___x_5909_ = v_toApplicative_5900_;
v_isShared_5910_ = v_isSharedCheck_5978_;
goto v_resetjp_5908_;
}
else
{
lean_inc(v_toSeqRight_5907_);
lean_inc(v_toSeqLeft_5906_);
lean_inc(v_toSeq_5905_);
lean_inc(v_toFunctor_5904_);
lean_dec(v_toApplicative_5900_);
v___x_5909_ = lean_box(0);
v_isShared_5910_ = v_isSharedCheck_5978_;
goto v_resetjp_5908_;
}
v_resetjp_5908_:
{
lean_object* v___f_5911_; lean_object* v___f_5912_; lean_object* v___f_5913_; lean_object* v___f_5914_; lean_object* v___x_5915_; lean_object* v___f_5916_; lean_object* v___f_5917_; lean_object* v___f_5918_; lean_object* v___x_5920_; 
v___f_5911_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__4));
v___f_5912_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__5));
lean_inc_ref(v_toFunctor_5904_);
v___f_5913_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5913_, 0, v_toFunctor_5904_);
v___f_5914_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5914_, 0, v_toFunctor_5904_);
v___x_5915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5915_, 0, v___f_5913_);
lean_ctor_set(v___x_5915_, 1, v___f_5914_);
v___f_5916_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5916_, 0, v_toSeqRight_5907_);
v___f_5917_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5917_, 0, v_toSeqLeft_5906_);
v___f_5918_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5918_, 0, v_toSeq_5905_);
if (v_isShared_5910_ == 0)
{
lean_ctor_set(v___x_5909_, 4, v___f_5916_);
lean_ctor_set(v___x_5909_, 3, v___f_5917_);
lean_ctor_set(v___x_5909_, 2, v___f_5918_);
lean_ctor_set(v___x_5909_, 1, v___f_5911_);
lean_ctor_set(v___x_5909_, 0, v___x_5915_);
v___x_5920_ = v___x_5909_;
goto v_reusejp_5919_;
}
else
{
lean_object* v_reuseFailAlloc_5977_; 
v_reuseFailAlloc_5977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5977_, 0, v___x_5915_);
lean_ctor_set(v_reuseFailAlloc_5977_, 1, v___f_5911_);
lean_ctor_set(v_reuseFailAlloc_5977_, 2, v___f_5918_);
lean_ctor_set(v_reuseFailAlloc_5977_, 3, v___f_5917_);
lean_ctor_set(v_reuseFailAlloc_5977_, 4, v___f_5916_);
v___x_5920_ = v_reuseFailAlloc_5977_;
goto v_reusejp_5919_;
}
v_reusejp_5919_:
{
lean_object* v___x_5922_; 
if (v_isShared_5903_ == 0)
{
lean_ctor_set(v___x_5902_, 1, v___f_5912_);
lean_ctor_set(v___x_5902_, 0, v___x_5920_);
v___x_5922_ = v___x_5902_;
goto v_reusejp_5921_;
}
else
{
lean_object* v_reuseFailAlloc_5976_; 
v_reuseFailAlloc_5976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5976_, 0, v___x_5920_);
lean_ctor_set(v_reuseFailAlloc_5976_, 1, v___f_5912_);
v___x_5922_ = v_reuseFailAlloc_5976_;
goto v_reusejp_5921_;
}
v_reusejp_5921_:
{
lean_object* v___x_5923_; lean_object* v_toApplicative_5924_; lean_object* v___x_5926_; uint8_t v_isShared_5927_; uint8_t v_isSharedCheck_5974_; 
v___x_5923_ = l_StateRefT_x27_instMonad___redArg(v___x_5922_);
v_toApplicative_5924_ = lean_ctor_get(v___x_5923_, 0);
v_isSharedCheck_5974_ = !lean_is_exclusive(v___x_5923_);
if (v_isSharedCheck_5974_ == 0)
{
lean_object* v_unused_5975_; 
v_unused_5975_ = lean_ctor_get(v___x_5923_, 1);
lean_dec(v_unused_5975_);
v___x_5926_ = v___x_5923_;
v_isShared_5927_ = v_isSharedCheck_5974_;
goto v_resetjp_5925_;
}
else
{
lean_inc(v_toApplicative_5924_);
lean_dec(v___x_5923_);
v___x_5926_ = lean_box(0);
v_isShared_5927_ = v_isSharedCheck_5974_;
goto v_resetjp_5925_;
}
v_resetjp_5925_:
{
lean_object* v_toFunctor_5928_; lean_object* v_toSeq_5929_; lean_object* v_toSeqLeft_5930_; lean_object* v_toSeqRight_5931_; lean_object* v___x_5933_; uint8_t v_isShared_5934_; uint8_t v_isSharedCheck_5972_; 
v_toFunctor_5928_ = lean_ctor_get(v_toApplicative_5924_, 0);
v_toSeq_5929_ = lean_ctor_get(v_toApplicative_5924_, 2);
v_toSeqLeft_5930_ = lean_ctor_get(v_toApplicative_5924_, 3);
v_toSeqRight_5931_ = lean_ctor_get(v_toApplicative_5924_, 4);
v_isSharedCheck_5972_ = !lean_is_exclusive(v_toApplicative_5924_);
if (v_isSharedCheck_5972_ == 0)
{
lean_object* v_unused_5973_; 
v_unused_5973_ = lean_ctor_get(v_toApplicative_5924_, 1);
lean_dec(v_unused_5973_);
v___x_5933_ = v_toApplicative_5924_;
v_isShared_5934_ = v_isSharedCheck_5972_;
goto v_resetjp_5932_;
}
else
{
lean_inc(v_toSeqRight_5931_);
lean_inc(v_toSeqLeft_5930_);
lean_inc(v_toSeq_5929_);
lean_inc(v_toFunctor_5928_);
lean_dec(v_toApplicative_5924_);
v___x_5933_ = lean_box(0);
v_isShared_5934_ = v_isSharedCheck_5972_;
goto v_resetjp_5932_;
}
v_resetjp_5932_:
{
lean_object* v___f_5935_; lean_object* v___f_5936_; lean_object* v___f_5937_; lean_object* v___f_5938_; lean_object* v___x_5939_; lean_object* v___f_5940_; lean_object* v___f_5941_; lean_object* v___f_5942_; lean_object* v___x_5944_; 
v___f_5935_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__6));
v___f_5936_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___closed__7));
lean_inc_ref(v_toFunctor_5928_);
v___f_5937_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5937_, 0, v_toFunctor_5928_);
v___f_5938_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5938_, 0, v_toFunctor_5928_);
v___x_5939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5939_, 0, v___f_5937_);
lean_ctor_set(v___x_5939_, 1, v___f_5938_);
v___f_5940_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5940_, 0, v_toSeqRight_5931_);
v___f_5941_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5941_, 0, v_toSeqLeft_5930_);
v___f_5942_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5942_, 0, v_toSeq_5929_);
if (v_isShared_5934_ == 0)
{
lean_ctor_set(v___x_5933_, 4, v___f_5940_);
lean_ctor_set(v___x_5933_, 3, v___f_5941_);
lean_ctor_set(v___x_5933_, 2, v___f_5942_);
lean_ctor_set(v___x_5933_, 1, v___f_5935_);
lean_ctor_set(v___x_5933_, 0, v___x_5939_);
v___x_5944_ = v___x_5933_;
goto v_reusejp_5943_;
}
else
{
lean_object* v_reuseFailAlloc_5971_; 
v_reuseFailAlloc_5971_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5971_, 0, v___x_5939_);
lean_ctor_set(v_reuseFailAlloc_5971_, 1, v___f_5935_);
lean_ctor_set(v_reuseFailAlloc_5971_, 2, v___f_5942_);
lean_ctor_set(v_reuseFailAlloc_5971_, 3, v___f_5941_);
lean_ctor_set(v_reuseFailAlloc_5971_, 4, v___f_5940_);
v___x_5944_ = v_reuseFailAlloc_5971_;
goto v_reusejp_5943_;
}
v_reusejp_5943_:
{
lean_object* v___x_5946_; 
if (v_isShared_5927_ == 0)
{
lean_ctor_set(v___x_5926_, 1, v___f_5936_);
lean_ctor_set(v___x_5926_, 0, v___x_5944_);
v___x_5946_ = v___x_5926_;
goto v_reusejp_5945_;
}
else
{
lean_object* v_reuseFailAlloc_5970_; 
v_reuseFailAlloc_5970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5970_, 0, v___x_5944_);
lean_ctor_set(v_reuseFailAlloc_5970_, 1, v___f_5936_);
v___x_5946_ = v_reuseFailAlloc_5970_;
goto v_reusejp_5945_;
}
v_reusejp_5945_:
{
lean_object* v___x_5947_; lean_object* v___x_5948_; lean_object* v___x_5949_; uint8_t v___x_5950_; 
v___x_5947_ = l_ReaderT_instMonad___redArg(v___x_5946_);
v___x_5948_ = lean_array_get_size(v_acc_5874_);
v___x_5949_ = lean_array_get_size(v_declInfos_5871_);
v___x_5950_ = lean_nat_dec_lt(v___x_5948_, v___x_5949_);
if (v___x_5950_ == 0)
{
lean_object* v___x_5951_; 
lean_dec_ref(v___x_5947_);
lean_dec_ref(v_declInfos_5871_);
lean_inc(v___y_5881_);
lean_inc_ref(v___y_5880_);
lean_inc(v___y_5879_);
lean_inc_ref(v___y_5878_);
lean_inc(v___y_5877_);
lean_inc_ref(v___y_5876_);
lean_inc_ref(v___y_5875_);
v___x_5951_ = lean_apply_9(v_k_5872_, v_acc_5874_, v___y_5875_, v___y_5876_, v___y_5877_, v___y_5878_, v___y_5879_, v___y_5880_, v___y_5881_, lean_box(0));
return v___x_5951_;
}
else
{
lean_object* v___f_5952_; lean_object* v___x_5953_; uint8_t v___x_5954_; lean_object* v___f_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; lean_object* v___x_5959_; lean_object* v_snd_5960_; lean_object* v_fst_5961_; lean_object* v_fst_5962_; lean_object* v_snd_5963_; lean_object* v___x_5964_; 
v___f_5952_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___lam__0___boxed), 10, 1);
lean_closure_set(v___f_5952_, 0, v___x_5947_);
v___x_5953_ = lean_box(0);
v___x_5954_ = 0;
v___f_5955_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5955_, 0, v___f_5952_);
v___x_5956_ = lean_box(v___x_5954_);
v___x_5957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5957_, 0, v___x_5956_);
lean_ctor_set(v___x_5957_, 1, v___f_5955_);
v___x_5958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5958_, 0, v___x_5953_);
lean_ctor_set(v___x_5958_, 1, v___x_5957_);
v___x_5959_ = lean_array_get(v___x_5958_, v_declInfos_5871_, v___x_5948_);
lean_dec_ref_known(v___x_5958_, 2);
v_snd_5960_ = lean_ctor_get(v___x_5959_, 1);
lean_inc(v_snd_5960_);
v_fst_5961_ = lean_ctor_get(v___x_5959_, 0);
lean_inc(v_fst_5961_);
lean_dec(v___x_5959_);
v_fst_5962_ = lean_ctor_get(v_snd_5960_, 0);
lean_inc(v_fst_5962_);
v_snd_5963_ = lean_ctor_get(v_snd_5960_, 1);
lean_inc(v_snd_5963_);
lean_dec(v_snd_5960_);
lean_inc(v___y_5881_);
lean_inc_ref(v___y_5880_);
lean_inc(v___y_5879_);
lean_inc_ref(v___y_5878_);
lean_inc(v___y_5877_);
lean_inc_ref(v___y_5876_);
lean_inc_ref(v___y_5875_);
lean_inc_ref(v_acc_5874_);
v___x_5964_ = lean_apply_9(v_snd_5963_, v_acc_5874_, v___y_5875_, v___y_5876_, v___y_5877_, v___y_5878_, v___y_5879_, v___y_5880_, v___y_5881_, lean_box(0));
if (lean_obj_tag(v___x_5964_) == 0)
{
lean_object* v_a_5965_; lean_object* v___x_5966_; lean_object* v___f_5967_; uint8_t v___x_5968_; lean_object* v___x_5969_; 
v_a_5965_ = lean_ctor_get(v___x_5964_, 0);
lean_inc(v_a_5965_);
lean_dec_ref_known(v___x_5964_, 1);
v___x_5966_ = lean_box(v_kind_5873_);
v___f_5967_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___lam__1___boxed), 13, 4);
lean_closure_set(v___f_5967_, 0, v_acc_5874_);
lean_closure_set(v___f_5967_, 1, v_declInfos_5871_);
lean_closure_set(v___f_5967_, 2, v_k_5872_);
lean_closure_set(v___f_5967_, 3, v___x_5966_);
v___x_5968_ = lean_unbox(v_fst_5962_);
lean_dec(v_fst_5962_);
v___x_5969_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_fst_5961_, v___x_5968_, v_a_5965_, v___f_5967_, v_kind_5873_, v___y_5875_, v___y_5876_, v___y_5877_, v___y_5878_, v___y_5879_, v___y_5880_, v___y_5881_);
return v___x_5969_;
}
else
{
lean_dec(v_fst_5962_);
lean_dec(v_fst_5961_);
lean_dec_ref(v_acc_5874_);
lean_dec_ref(v_k_5872_);
lean_dec_ref(v_declInfos_5871_);
return v___x_5964_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___lam__1(lean_object* v_acc_5982_, lean_object* v_declInfos_5983_, lean_object* v_k_5984_, uint8_t v_kind_5985_, lean_object* v_x_5986_, lean_object* v___y_5987_, lean_object* v___y_5988_, lean_object* v___y_5989_, lean_object* v___y_5990_, lean_object* v___y_5991_, lean_object* v___y_5992_, lean_object* v___y_5993_){
_start:
{
lean_object* v___x_5995_; lean_object* v___x_5996_; 
v___x_5995_ = lean_array_push(v_acc_5982_, v_x_5986_);
v___x_5996_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8(v_declInfos_5983_, v_k_5984_, v_kind_5985_, v___x_5995_, v___y_5987_, v___y_5988_, v___y_5989_, v___y_5990_, v___y_5991_, v___y_5992_, v___y_5993_);
return v___x_5996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8___boxed(lean_object* v_declInfos_5997_, lean_object* v_k_5998_, lean_object* v_kind_5999_, lean_object* v_acc_6000_, lean_object* v___y_6001_, lean_object* v___y_6002_, lean_object* v___y_6003_, lean_object* v___y_6004_, lean_object* v___y_6005_, lean_object* v___y_6006_, lean_object* v___y_6007_, lean_object* v___y_6008_){
_start:
{
uint8_t v_kind_boxed_6009_; lean_object* v_res_6010_; 
v_kind_boxed_6009_ = lean_unbox(v_kind_5999_);
v_res_6010_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8(v_declInfos_5997_, v_k_5998_, v_kind_boxed_6009_, v_acc_6000_, v___y_6001_, v___y_6002_, v___y_6003_, v___y_6004_, v___y_6005_, v___y_6006_, v___y_6007_);
lean_dec(v___y_6007_);
lean_dec_ref(v___y_6006_);
lean_dec(v___y_6005_);
lean_dec_ref(v___y_6004_);
lean_dec(v___y_6003_);
lean_dec_ref(v___y_6002_);
lean_dec_ref(v___y_6001_);
return v_res_6010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(lean_object* v_declInfos_6013_, lean_object* v_k_6014_, uint8_t v_kind_6015_, lean_object* v___y_6016_, lean_object* v___y_6017_, lean_object* v___y_6018_, lean_object* v___y_6019_, lean_object* v___y_6020_, lean_object* v___y_6021_, lean_object* v___y_6022_){
_start:
{
lean_object* v___x_6024_; lean_object* v___x_6025_; 
v___x_6024_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6___closed__0));
v___x_6025_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6_spec__8(v_declInfos_6013_, v_k_6014_, v_kind_6015_, v___x_6024_, v___y_6016_, v___y_6017_, v___y_6018_, v___y_6019_, v___y_6020_, v___y_6021_, v___y_6022_);
return v___x_6025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6___boxed(lean_object* v_declInfos_6026_, lean_object* v_k_6027_, lean_object* v_kind_6028_, lean_object* v___y_6029_, lean_object* v___y_6030_, lean_object* v___y_6031_, lean_object* v___y_6032_, lean_object* v___y_6033_, lean_object* v___y_6034_, lean_object* v___y_6035_, lean_object* v___y_6036_){
_start:
{
uint8_t v_kind_boxed_6037_; lean_object* v_res_6038_; 
v_kind_boxed_6037_ = lean_unbox(v_kind_6028_);
v_res_6038_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(v_declInfos_6026_, v_k_6027_, v_kind_boxed_6037_, v___y_6029_, v___y_6030_, v___y_6031_, v___y_6032_, v___y_6033_, v___y_6034_, v___y_6035_);
lean_dec(v___y_6035_);
lean_dec_ref(v___y_6034_);
lean_dec(v___y_6033_);
lean_dec_ref(v___y_6032_);
lean_dec(v___y_6031_);
lean_dec_ref(v___y_6030_);
lean_dec_ref(v___y_6029_);
return v_res_6038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__5(size_t v_sz_6039_, size_t v_i_6040_, lean_object* v_bs_6041_){
_start:
{
uint8_t v___x_6042_; 
v___x_6042_ = lean_usize_dec_lt(v_i_6040_, v_sz_6039_);
if (v___x_6042_ == 0)
{
return v_bs_6041_;
}
else
{
lean_object* v_v_6043_; lean_object* v_fst_6044_; lean_object* v_snd_6045_; lean_object* v___x_6047_; uint8_t v_isShared_6048_; uint8_t v_isSharedCheck_6061_; 
v_v_6043_ = lean_array_uget(v_bs_6041_, v_i_6040_);
v_fst_6044_ = lean_ctor_get(v_v_6043_, 0);
v_snd_6045_ = lean_ctor_get(v_v_6043_, 1);
v_isSharedCheck_6061_ = !lean_is_exclusive(v_v_6043_);
if (v_isSharedCheck_6061_ == 0)
{
v___x_6047_ = v_v_6043_;
v_isShared_6048_ = v_isSharedCheck_6061_;
goto v_resetjp_6046_;
}
else
{
lean_inc(v_snd_6045_);
lean_inc(v_fst_6044_);
lean_dec(v_v_6043_);
v___x_6047_ = lean_box(0);
v_isShared_6048_ = v_isSharedCheck_6061_;
goto v_resetjp_6046_;
}
v_resetjp_6046_:
{
lean_object* v___x_6049_; lean_object* v_bs_x27_6050_; uint8_t v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6054_; 
v___x_6049_ = lean_unsigned_to_nat(0u);
v_bs_x27_6050_ = lean_array_uset(v_bs_6041_, v_i_6040_, v___x_6049_);
v___x_6051_ = 0;
v___x_6052_ = lean_box(v___x_6051_);
if (v_isShared_6048_ == 0)
{
lean_ctor_set(v___x_6047_, 0, v___x_6052_);
v___x_6054_ = v___x_6047_;
goto v_reusejp_6053_;
}
else
{
lean_object* v_reuseFailAlloc_6060_; 
v_reuseFailAlloc_6060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6060_, 0, v___x_6052_);
lean_ctor_set(v_reuseFailAlloc_6060_, 1, v_snd_6045_);
v___x_6054_ = v_reuseFailAlloc_6060_;
goto v_reusejp_6053_;
}
v_reusejp_6053_:
{
lean_object* v___x_6055_; size_t v___x_6056_; size_t v___x_6057_; lean_object* v___x_6058_; 
v___x_6055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6055_, 0, v_fst_6044_);
lean_ctor_set(v___x_6055_, 1, v___x_6054_);
v___x_6056_ = ((size_t)1ULL);
v___x_6057_ = lean_usize_add(v_i_6040_, v___x_6056_);
v___x_6058_ = lean_array_uset(v_bs_x27_6050_, v_i_6040_, v___x_6055_);
v_i_6040_ = v___x_6057_;
v_bs_6041_ = v___x_6058_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__5___boxed(lean_object* v_sz_6062_, lean_object* v_i_6063_, lean_object* v_bs_6064_){
_start:
{
size_t v_sz_boxed_6065_; size_t v_i_boxed_6066_; lean_object* v_res_6067_; 
v_sz_boxed_6065_ = lean_unbox_usize(v_sz_6062_);
lean_dec(v_sz_6062_);
v_i_boxed_6066_ = lean_unbox_usize(v_i_6063_);
lean_dec(v_i_6063_);
v_res_6067_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__5(v_sz_boxed_6065_, v_i_boxed_6066_, v_bs_6064_);
return v_res_6067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(lean_object* v_declInfos_6068_, lean_object* v_k_6069_, uint8_t v_kind_6070_, lean_object* v___y_6071_, lean_object* v___y_6072_, lean_object* v___y_6073_, lean_object* v___y_6074_, lean_object* v___y_6075_, lean_object* v___y_6076_, lean_object* v___y_6077_){
_start:
{
size_t v_sz_6079_; size_t v___x_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; 
v_sz_6079_ = lean_array_size(v_declInfos_6068_);
v___x_6080_ = ((size_t)0ULL);
v___x_6081_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__5(v_sz_6079_, v___x_6080_, v_declInfos_6068_);
v___x_6082_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(v___x_6081_, v_k_6069_, v_kind_6070_, v___y_6071_, v___y_6072_, v___y_6073_, v___y_6074_, v___y_6075_, v___y_6076_, v___y_6077_);
return v___x_6082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4___boxed(lean_object* v_declInfos_6083_, lean_object* v_k_6084_, lean_object* v_kind_6085_, lean_object* v___y_6086_, lean_object* v___y_6087_, lean_object* v___y_6088_, lean_object* v___y_6089_, lean_object* v___y_6090_, lean_object* v___y_6091_, lean_object* v___y_6092_, lean_object* v___y_6093_){
_start:
{
uint8_t v_kind_boxed_6094_; lean_object* v_res_6095_; 
v_kind_boxed_6094_ = lean_unbox(v_kind_6085_);
v_res_6095_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(v_declInfos_6083_, v_k_6084_, v_kind_boxed_6094_, v___y_6086_, v___y_6087_, v___y_6088_, v___y_6089_, v___y_6090_, v___y_6091_, v___y_6092_);
lean_dec(v___y_6092_);
lean_dec_ref(v___y_6091_);
lean_dec(v___y_6090_);
lean_dec_ref(v___y_6089_);
lean_dec(v___y_6088_);
lean_dec_ref(v___y_6087_);
lean_dec_ref(v___y_6086_);
return v_res_6095_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___closed__3(void){
_start:
{
lean_object* v___x_6101_; lean_object* v___x_6102_; 
v___x_6101_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__2));
v___x_6102_ = l_Lean_stringToMessageData(v___x_6101_);
return v___x_6102_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___closed__23(void){
_start:
{
lean_object* v___x_6134_; lean_object* v___x_6135_; 
v___x_6134_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__22));
v___x_6135_ = l_Lean_stringToMessageData(v___x_6134_);
return v___x_6135_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoFor___closed__25(void){
_start:
{
lean_object* v___x_6137_; lean_object* v___x_6138_; 
v___x_6137_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__24));
v___x_6138_ = l_Lean_stringToMessageData(v___x_6137_);
return v___x_6138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor(lean_object* v_stx_6139_, lean_object* v_dec_6140_, lean_object* v_a_6141_, lean_object* v_a_6142_, lean_object* v_a_6143_, lean_object* v_a_6144_, lean_object* v_a_6145_, lean_object* v_a_6146_, lean_object* v_a_6147_){
_start:
{
lean_object* v___x_6149_; uint8_t v___x_6150_; 
v___x_6149_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
lean_inc(v_stx_6139_);
v___x_6150_ = l_Lean_Syntax_isOfKind(v_stx_6139_, v___x_6149_);
if (v___x_6150_ == 0)
{
lean_object* v___x_6151_; 
lean_dec_ref(v_dec_6140_);
lean_dec(v_stx_6139_);
v___x_6151_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg();
return v___x_6151_;
}
else
{
lean_object* v___x_6152_; lean_object* v___x_6153_; uint8_t v___x_6154_; 
v___x_6152_ = lean_unsigned_to_nat(1u);
v___x_6153_ = l_Lean_Syntax_getArg(v_stx_6139_, v___x_6152_);
lean_inc(v___x_6153_);
v___x_6154_ = l_Lean_Syntax_matchesNull(v___x_6153_, v___x_6152_);
if (v___x_6154_ == 0)
{
lean_object* v___x_6155_; 
lean_dec(v___x_6153_);
lean_dec_ref(v_dec_6140_);
lean_dec(v_stx_6139_);
v___x_6155_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg();
return v___x_6155_;
}
else
{
lean_object* v___x_6156_; lean_object* v___x_6157_; lean_object* v___x_6158_; uint8_t v___x_6159_; lean_object* v___y_6161_; lean_object* v___y_6162_; lean_object* v___y_6163_; lean_object* v___y_6164_; uint8_t v___y_6165_; lean_object* v___y_6166_; lean_object* v___y_6167_; lean_object* v___y_6168_; lean_object* v___y_6169_; lean_object* v___y_6170_; lean_object* v___y_6171_; lean_object* v_forIn_6172_; lean_object* v___y_6173_; lean_object* v___y_6174_; lean_object* v___y_6175_; lean_object* v___y_6176_; lean_object* v___y_6177_; lean_object* v___y_6178_; lean_object* v___y_6179_; lean_object* v___y_6189_; lean_object* v___y_6190_; lean_object* v___y_6191_; lean_object* v___y_6192_; uint8_t v___y_6193_; lean_object* v___y_6194_; lean_object* v___y_6195_; lean_object* v___y_6196_; lean_object* v___y_6197_; lean_object* v___y_6198_; lean_object* v___y_6199_; lean_object* v___y_6200_; lean_object* v___y_6201_; uint8_t v___y_6202_; lean_object* v___y_6203_; lean_object* v___y_6204_; lean_object* v___y_6205_; lean_object* v___y_6206_; lean_object* v___y_6207_; lean_object* v___y_6208_; lean_object* v___y_6209_; lean_object* v___y_6210_; lean_object* v___y_6211_; lean_object* v___y_6212_; lean_object* v___y_6213_; lean_object* v___y_6214_; lean_object* v___y_6215_; lean_object* v___y_6216_; lean_object* v___y_6217_; lean_object* v___y_6259_; lean_object* v___y_6260_; lean_object* v___y_6261_; lean_object* v___y_6262_; lean_object* v___y_6263_; lean_object* v___y_6264_; uint8_t v___y_6265_; lean_object* v___y_6266_; lean_object* v___y_6267_; lean_object* v___y_6268_; lean_object* v___y_6269_; lean_object* v___y_6270_; lean_object* v___y_6271_; lean_object* v___y_6272_; lean_object* v___y_6273_; lean_object* v___y_6274_; lean_object* v___y_6275_; lean_object* v___y_6276_; lean_object* v___y_6277_; uint8_t v___y_6278_; lean_object* v___y_6279_; lean_object* v___y_6280_; lean_object* v___y_6281_; lean_object* v___y_6282_; lean_object* v___y_6283_; lean_object* v___y_6284_; lean_object* v___y_6285_; lean_object* v___y_6286_; lean_object* v___y_6287_; lean_object* v___y_6288_; lean_object* v___y_6289_; lean_object* v___y_6290_; uint8_t v___y_6291_; lean_object* v___y_6292_; lean_object* v___y_6293_; lean_object* v___y_6294_; lean_object* v___y_6295_; lean_object* v___y_6304_; lean_object* v___y_6305_; lean_object* v___y_6306_; lean_object* v___y_6307_; lean_object* v___y_6308_; lean_object* v___y_6309_; uint8_t v___y_6310_; lean_object* v___y_6311_; lean_object* v___y_6312_; lean_object* v___y_6313_; lean_object* v___y_6314_; lean_object* v___y_6315_; lean_object* v___y_6316_; lean_object* v___y_6317_; lean_object* v___y_6318_; lean_object* v___y_6319_; lean_object* v___y_6320_; lean_object* v___y_6321_; lean_object* v___y_6322_; lean_object* v___y_6323_; uint8_t v___y_6324_; lean_object* v___y_6325_; lean_object* v___y_6326_; lean_object* v___y_6327_; lean_object* v___y_6328_; lean_object* v___y_6329_; lean_object* v___y_6330_; lean_object* v___y_6331_; lean_object* v___y_6332_; lean_object* v___y_6333_; lean_object* v___y_6334_; lean_object* v___y_6335_; lean_object* v___y_6336_; lean_object* v___y_6337_; lean_object* v___y_6338_; uint8_t v___y_6339_; lean_object* v___y_6340_; lean_object* v___y_6346_; lean_object* v___y_6347_; lean_object* v___y_6348_; lean_object* v___y_6349_; lean_object* v___y_6350_; lean_object* v___y_6351_; lean_object* v___y_6352_; uint8_t v___y_6353_; lean_object* v___y_6354_; lean_object* v___y_6355_; lean_object* v___y_6356_; lean_object* v___y_6357_; lean_object* v___y_6358_; lean_object* v___y_6359_; lean_object* v___y_6360_; lean_object* v___y_6361_; lean_object* v___y_6362_; lean_object* v___y_6363_; lean_object* v___y_6364_; lean_object* v___y_6365_; lean_object* v___y_6366_; lean_object* v___y_6367_; lean_object* v___y_6368_; lean_object* v___y_6369_; uint8_t v___y_6370_; lean_object* v___y_6371_; lean_object* v___y_6372_; lean_object* v___y_6373_; lean_object* v___y_6374_; lean_object* v___y_6375_; lean_object* v___y_6376_; uint8_t v___y_6377_; lean_object* v___y_6378_; lean_object* v___y_6379_; lean_object* v_fst_6380_; lean_object* v_snd_6381_; lean_object* v___y_6382_; lean_object* v___y_6383_; lean_object* v___y_6384_; lean_object* v___y_6385_; lean_object* v___y_6386_; lean_object* v___y_6387_; lean_object* v___y_6388_; lean_object* v___y_6413_; lean_object* v___y_6414_; lean_object* v___y_6415_; lean_object* v___y_6416_; lean_object* v___y_6417_; uint8_t v___y_6418_; lean_object* v___y_6419_; lean_object* v___y_6420_; lean_object* v___y_6421_; lean_object* v___y_6422_; lean_object* v___y_6423_; lean_object* v___y_6424_; lean_object* v___y_6425_; lean_object* v___y_6426_; lean_object* v___y_6427_; lean_object* v___y_6428_; lean_object* v___y_6429_; lean_object* v___y_6430_; lean_object* v___y_6431_; lean_object* v___y_6432_; lean_object* v___y_6433_; lean_object* v___y_6434_; lean_object* v___y_6435_; lean_object* v___y_6436_; uint8_t v___y_6437_; lean_object* v___y_6438_; lean_object* v___y_6439_; lean_object* v___y_6440_; lean_object* v___y_6441_; lean_object* v___y_6442_; lean_object* v___y_6443_; lean_object* v___y_6444_; lean_object* v___y_6445_; lean_object* v___y_6446_; uint8_t v___y_6447_; lean_object* v___y_6448_; lean_object* v___y_6449_; lean_object* v___y_6450_; lean_object* v___y_6451_; lean_object* v___y_6535_; lean_object* v___y_6536_; lean_object* v___y_6537_; lean_object* v___y_6538_; lean_object* v___y_6539_; lean_object* v___y_6540_; lean_object* v___y_6541_; lean_object* v___y_6542_; lean_object* v___y_6543_; lean_object* v___y_6544_; lean_object* v___y_6545_; lean_object* v___y_6546_; lean_object* v___y_6547_; uint8_t v___y_6548_; lean_object* v___y_6549_; lean_object* v___y_6550_; lean_object* v___y_6551_; lean_object* v___y_6552_; lean_object* v___y_6553_; lean_object* v___y_6554_; lean_object* v___y_6555_; lean_object* v___y_6556_; lean_object* v___y_6557_; lean_object* v___y_6558_; lean_object* v___y_6559_; uint8_t v___y_6560_; lean_object* v___y_6561_; lean_object* v___y_6562_; lean_object* v___y_6563_; lean_object* v___y_6564_; lean_object* v___y_6565_; lean_object* v___y_6566_; lean_object* v___y_6567_; uint8_t v___y_6568_; lean_object* v___y_6569_; lean_object* v___y_6570_; lean_object* v___y_6571_; lean_object* v___y_6572_; 
v___x_6156_ = lean_unsigned_to_nat(0u);
v___x_6157_ = l_Lean_Syntax_getArg(v___x_6153_, v___x_6156_);
lean_dec(v___x_6153_);
v___x_6158_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4));
lean_inc(v___x_6157_);
v___x_6159_ = l_Lean_Syntax_isOfKind(v___x_6157_, v___x_6158_);
if (v___x_6159_ == 0)
{
lean_object* v___x_6586_; 
lean_dec(v___x_6157_);
lean_dec_ref(v_dec_6140_);
lean_dec(v_stx_6139_);
v___x_6586_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg();
return v___x_6586_;
}
else
{
lean_object* v_tk_6587_; lean_object* v___y_6589_; lean_object* v___y_6590_; lean_object* v___y_6591_; uint8_t v___y_6592_; lean_object* v___y_6593_; lean_object* v___y_6594_; lean_object* v___y_6595_; lean_object* v___y_6596_; lean_object* v___y_6597_; lean_object* v___y_6598_; uint8_t v___y_6599_; lean_object* v___y_6600_; lean_object* v___y_6601_; lean_object* v___y_6602_; lean_object* v___y_6603_; lean_object* v___y_6604_; lean_object* v___y_6605_; lean_object* v___y_6606_; lean_object* v___y_6607_; lean_object* v___y_6725_; lean_object* v___y_6726_; lean_object* v___y_6727_; lean_object* v___y_6728_; lean_object* v___y_6729_; lean_object* v___y_6730_; lean_object* v___y_6731_; lean_object* v___y_6732_; lean_object* v___y_6733_; lean_object* v___y_6734_; lean_object* v___y_6735_; lean_object* v___y_6736_; uint8_t v___y_6737_; lean_object* v___y_6738_; lean_object* v___y_6739_; uint8_t v___y_6740_; lean_object* v___y_6741_; lean_object* v___y_6742_; lean_object* v___y_6756_; lean_object* v___y_6757_; uint8_t v___y_6758_; lean_object* v___y_6759_; lean_object* v___y_6760_; lean_object* v___y_6761_; lean_object* v___y_6762_; lean_object* v___y_6763_; uint8_t v___y_6764_; lean_object* v_dec_x3f_6765_; lean_object* v___y_6766_; lean_object* v___y_6767_; lean_object* v___y_6768_; lean_object* v___y_6769_; lean_object* v___y_6770_; lean_object* v___y_6771_; lean_object* v___y_6772_; lean_object* v___y_6788_; lean_object* v___y_6789_; uint8_t v___y_6790_; lean_object* v___y_6791_; lean_object* v___y_6792_; lean_object* v___y_6793_; lean_object* v___y_6794_; uint8_t v___y_6795_; lean_object* v___y_6796_; lean_object* v_inv_x3f_6797_; lean_object* v___y_6798_; lean_object* v___y_6799_; lean_object* v___y_6800_; lean_object* v___y_6801_; lean_object* v___y_6802_; lean_object* v___y_6803_; lean_object* v___y_6804_; lean_object* v_h_x3f_6816_; lean_object* v___y_6817_; lean_object* v___y_6818_; lean_object* v___y_6819_; lean_object* v___y_6820_; lean_object* v___y_6821_; lean_object* v___y_6822_; lean_object* v___y_6823_; lean_object* v___x_6841_; uint8_t v___x_6842_; 
v_tk_6587_ = l_Lean_Syntax_getArg(v_stx_6139_, v___x_6156_);
v___x_6841_ = l_Lean_Syntax_getArg(v___x_6157_, v___x_6156_);
v___x_6842_ = l_Lean_Syntax_isNone(v___x_6841_);
if (v___x_6842_ == 0)
{
lean_object* v___x_6843_; uint8_t v___x_6844_; 
v___x_6843_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_6841_);
v___x_6844_ = l_Lean_Syntax_matchesNull(v___x_6841_, v___x_6843_);
if (v___x_6844_ == 0)
{
lean_object* v___x_6845_; 
lean_dec(v___x_6841_);
lean_dec(v_tk_6587_);
lean_dec(v___x_6157_);
lean_dec_ref(v_dec_6140_);
lean_dec(v_stx_6139_);
v___x_6845_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg();
return v___x_6845_;
}
else
{
lean_object* v_h_x3f_6846_; lean_object* v___x_6847_; 
v_h_x3f_6846_ = l_Lean_Syntax_getArg(v___x_6841_, v___x_6156_);
lean_dec(v___x_6841_);
v___x_6847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6847_, 0, v_h_x3f_6846_);
v_h_x3f_6816_ = v___x_6847_;
v___y_6817_ = v_a_6141_;
v___y_6818_ = v_a_6142_;
v___y_6819_ = v_a_6143_;
v___y_6820_ = v_a_6144_;
v___y_6821_ = v_a_6145_;
v___y_6822_ = v_a_6146_;
v___y_6823_ = v_a_6147_;
goto v___jp_6815_;
}
}
else
{
lean_object* v___x_6848_; 
lean_dec(v___x_6841_);
v___x_6848_ = lean_box(0);
v_h_x3f_6816_ = v___x_6848_;
v___y_6817_ = v_a_6141_;
v___y_6818_ = v_a_6142_;
v___y_6819_ = v_a_6143_;
v___y_6820_ = v_a_6144_;
v___y_6821_ = v_a_6145_;
v___y_6822_ = v_a_6146_;
v___y_6823_ = v_a_6147_;
goto v___jp_6815_;
}
v___jp_6588_:
{
lean_object* v___x_6608_; 
v___x_6608_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_6140_, v_tk_6587_, v___y_6601_, v___y_6602_, v___y_6603_, v___y_6604_, v___y_6605_, v___y_6606_, v___y_6607_);
lean_dec(v_tk_6587_);
if (lean_obj_tag(v___x_6608_) == 0)
{
lean_object* v_a_6609_; lean_object* v___x_6610_; lean_object* v___x_6611_; lean_object* v___x_6612_; 
v_a_6609_ = lean_ctor_get(v___x_6608_, 0);
lean_inc(v_a_6609_);
lean_dec_ref_known(v___x_6608_, 1);
v___x_6610_ = lean_mk_empty_array_with_capacity(v___x_6152_);
lean_inc(v___y_6595_);
v___x_6611_ = lean_array_push(v___x_6610_, v___y_6595_);
v___x_6612_ = l_Lean_Elab_Do_checkMutVarsForShadowing(v___x_6611_, v___y_6601_, v___y_6602_, v___y_6603_, v___y_6604_, v___y_6605_, v___y_6606_, v___y_6607_);
lean_dec_ref(v___x_6611_);
if (lean_obj_tag(v___x_6612_) == 0)
{
lean_object* v___x_6613_; 
lean_dec_ref_known(v___x_6612_, 1);
v___x_6613_ = l_Lean_Meta_mkFreshLevelMVar(v___y_6604_, v___y_6605_, v___y_6606_, v___y_6607_);
if (lean_obj_tag(v___x_6613_) == 0)
{
lean_object* v_a_6614_; lean_object* v___x_6615_; 
v_a_6614_ = lean_ctor_get(v___x_6613_, 0);
lean_inc(v_a_6614_);
lean_dec_ref_known(v___x_6613_, 1);
v___x_6615_ = l_Lean_Meta_mkFreshLevelMVar(v___y_6604_, v___y_6605_, v___y_6606_, v___y_6607_);
if (lean_obj_tag(v___x_6615_) == 0)
{
lean_object* v_a_6616_; lean_object* v___x_6617_; lean_object* v___x_6618_; lean_object* v___x_6619_; uint8_t v___x_6620_; lean_object* v___x_6621_; lean_object* v___x_6622_; 
v_a_6616_ = lean_ctor_get(v___x_6615_, 0);
lean_inc(v_a_6616_);
lean_dec_ref_known(v___x_6615_, 1);
lean_inc(v_a_6614_);
v___x_6617_ = l_Lean_Level_succ___override(v_a_6614_);
v___x_6618_ = l_Lean_mkSort(v___x_6617_);
v___x_6619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6619_, 0, v___x_6618_);
v___x_6620_ = 0;
v___x_6621_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__16));
v___x_6622_ = l_Lean_Meta_mkFreshExprMVar(v___x_6619_, v___x_6620_, v___x_6621_, v___y_6604_, v___y_6605_, v___y_6606_, v___y_6607_);
if (lean_obj_tag(v___x_6622_) == 0)
{
lean_object* v_a_6623_; lean_object* v___x_6625_; uint8_t v_isShared_6626_; uint8_t v_isSharedCheck_6691_; 
v_a_6623_ = lean_ctor_get(v___x_6622_, 0);
v_isSharedCheck_6691_ = !lean_is_exclusive(v___x_6622_);
if (v_isSharedCheck_6691_ == 0)
{
v___x_6625_ = v___x_6622_;
v_isShared_6626_ = v_isSharedCheck_6691_;
goto v_resetjp_6624_;
}
else
{
lean_inc(v_a_6623_);
lean_dec(v___x_6622_);
v___x_6625_ = lean_box(0);
v_isShared_6626_ = v_isSharedCheck_6691_;
goto v_resetjp_6624_;
}
v_resetjp_6624_:
{
lean_object* v___x_6627_; lean_object* v___x_6628_; lean_object* v___x_6630_; 
lean_inc(v_a_6616_);
v___x_6627_ = l_Lean_Level_succ___override(v_a_6616_);
v___x_6628_ = l_Lean_mkSort(v___x_6627_);
if (v_isShared_6626_ == 0)
{
lean_ctor_set_tag(v___x_6625_, 1);
lean_ctor_set(v___x_6625_, 0, v___x_6628_);
v___x_6630_ = v___x_6625_;
goto v_reusejp_6629_;
}
else
{
lean_object* v_reuseFailAlloc_6690_; 
v_reuseFailAlloc_6690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6690_, 0, v___x_6628_);
v___x_6630_ = v_reuseFailAlloc_6690_;
goto v_reusejp_6629_;
}
v_reusejp_6629_:
{
lean_object* v___x_6631_; lean_object* v___x_6632_; 
v___x_6631_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__18));
v___x_6632_ = l_Lean_Meta_mkFreshExprMVar(v___x_6630_, v___x_6620_, v___x_6631_, v___y_6604_, v___y_6605_, v___y_6606_, v___y_6607_);
if (lean_obj_tag(v___x_6632_) == 0)
{
lean_object* v_a_6633_; lean_object* v___x_6635_; uint8_t v_isShared_6636_; uint8_t v_isSharedCheck_6689_; 
v_a_6633_ = lean_ctor_get(v___x_6632_, 0);
v_isSharedCheck_6689_ = !lean_is_exclusive(v___x_6632_);
if (v_isSharedCheck_6689_ == 0)
{
v___x_6635_ = v___x_6632_;
v_isShared_6636_ = v_isSharedCheck_6689_;
goto v_resetjp_6634_;
}
else
{
lean_inc(v_a_6633_);
lean_dec(v___x_6632_);
v___x_6635_ = lean_box(0);
v_isShared_6636_ = v_isSharedCheck_6689_;
goto v_resetjp_6634_;
}
v_resetjp_6634_:
{
lean_object* v___x_6638_; 
lean_inc(v_a_6633_);
if (v_isShared_6636_ == 0)
{
lean_ctor_set_tag(v___x_6635_, 1);
v___x_6638_ = v___x_6635_;
goto v_reusejp_6637_;
}
else
{
lean_object* v_reuseFailAlloc_6688_; 
v_reuseFailAlloc_6688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6688_, 0, v_a_6633_);
v___x_6638_ = v_reuseFailAlloc_6688_;
goto v_reusejp_6637_;
}
v_reusejp_6637_:
{
lean_object* v___x_6639_; lean_object* v___x_6640_; 
v___x_6639_ = lean_box(0);
v___x_6640_ = l_Lean_Elab_Term_elabTermEnsuringType(v___y_6600_, v___x_6638_, v___x_6159_, v___x_6159_, v___x_6639_, v___y_6602_, v___y_6603_, v___y_6604_, v___y_6605_, v___y_6606_, v___y_6607_);
if (lean_obj_tag(v___x_6640_) == 0)
{
lean_object* v_a_6641_; lean_object* v___x_6642_; 
v_a_6641_ = lean_ctor_get(v___x_6640_, 0);
lean_inc(v_a_6641_);
lean_dec_ref_known(v___x_6640_, 1);
v___x_6642_ = l_Lean_Elab_Do_inferControlInfoSeq(v___y_6593_, v___y_6602_, v___y_6603_, v___y_6604_, v___y_6605_, v___y_6606_, v___y_6607_);
if (lean_obj_tag(v___x_6642_) == 0)
{
lean_object* v_a_6643_; lean_object* v___x_6644_; 
v_a_6643_ = lean_ctor_get(v___x_6642_, 0);
lean_inc(v_a_6643_);
lean_dec_ref_known(v___x_6642_, 1);
v___x_6644_ = l_Lean_Elab_Do_getReturnCont___redArg(v___y_6601_);
if (lean_obj_tag(v___x_6644_) == 0)
{
lean_object* v_a_6645_; lean_object* v___x_6646_; lean_object* v___x_6647_; 
v_a_6645_ = lean_ctor_get(v___x_6644_, 0);
lean_inc(v_a_6645_);
lean_dec_ref_known(v___x_6644_, 1);
v___x_6646_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__20));
v___x_6647_ = l_Lean_Core_mkFreshUserName(v___x_6646_, v___y_6606_, v___y_6607_);
if (lean_obj_tag(v___x_6647_) == 0)
{
lean_object* v_a_6648_; lean_object* v_monadInfo_6649_; lean_object* v_mutVars_6650_; lean_object* v___f_6651_; lean_object* v___x_6652_; lean_object* v___f_6653_; lean_object* v___x_6654_; lean_object* v___x_6655_; uint8_t v___x_6656_; 
v_a_6648_ = lean_ctor_get(v___x_6647_, 0);
lean_inc(v_a_6648_);
lean_dec_ref_known(v___x_6647_, 1);
v_monadInfo_6649_ = lean_ctor_get(v___y_6601_, 0);
v_mutVars_6650_ = lean_ctor_get(v___y_6601_, 1);
lean_inc(v_a_6623_);
v___f_6651_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__0___boxed), 10, 1);
lean_closure_set(v___f_6651_, 0, v_a_6623_);
v___x_6652_ = lean_box(v___x_6159_);
lean_inc(v_a_6645_);
v___f_6653_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__2___boxed), 12, 3);
lean_closure_set(v___f_6653_, 0, v_a_6645_);
lean_closure_set(v___f_6653_, 1, v___x_6152_);
lean_closure_set(v___f_6653_, 2, v___x_6652_);
v___x_6654_ = lean_array_get_size(v_mutVars_6650_);
v___x_6655_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__21));
v___x_6656_ = lean_nat_dec_lt(v___x_6156_, v___x_6654_);
if (v___x_6656_ == 0)
{
lean_inc(v_a_6614_);
lean_inc(v_a_6616_);
lean_inc(v_a_6641_);
lean_inc(v_a_6623_);
lean_inc_ref(v___f_6651_);
lean_inc(v_a_6633_);
lean_inc(v_a_6648_);
v___y_6535_ = v___y_6589_;
v___y_6536_ = v_a_6648_;
v___y_6537_ = v_a_6633_;
v___y_6538_ = v___y_6590_;
v___y_6539_ = v___f_6653_;
v___y_6540_ = v_monadInfo_6649_;
v___y_6541_ = v___y_6591_;
v___y_6542_ = v_a_6645_;
v___y_6543_ = v___f_6651_;
v___y_6544_ = v_a_6623_;
v___y_6545_ = v_a_6641_;
v___y_6546_ = v_a_6616_;
v___y_6547_ = v_a_6614_;
v___y_6548_ = v___y_6592_;
v___y_6549_ = v___f_6651_;
v___y_6550_ = v_a_6609_;
v___y_6551_ = v_a_6648_;
v___y_6552_ = v___y_6607_;
v___y_6553_ = v___y_6595_;
v___y_6554_ = v___y_6605_;
v___y_6555_ = v_a_6623_;
v___y_6556_ = v___y_6606_;
v___y_6557_ = v_a_6641_;
v___y_6558_ = v_a_6616_;
v___y_6559_ = v___y_6596_;
v___y_6560_ = v___y_6599_;
v___y_6561_ = v___y_6604_;
v___y_6562_ = v_a_6633_;
v___y_6563_ = v___y_6594_;
v___y_6564_ = v___y_6603_;
v___y_6565_ = v___y_6602_;
v___y_6566_ = v___y_6597_;
v___y_6567_ = v___y_6598_;
v___y_6568_ = v___x_6620_;
v___y_6569_ = v_a_6614_;
v___y_6570_ = v_a_6643_;
v___y_6571_ = v___y_6601_;
v___y_6572_ = v___x_6655_;
goto v___jp_6534_;
}
else
{
uint8_t v___x_6657_; 
v___x_6657_ = lean_nat_dec_le(v___x_6654_, v___x_6654_);
if (v___x_6657_ == 0)
{
if (v___x_6656_ == 0)
{
lean_inc(v_a_6614_);
lean_inc(v_a_6616_);
lean_inc(v_a_6641_);
lean_inc(v_a_6623_);
lean_inc_ref(v___f_6651_);
lean_inc(v_a_6633_);
lean_inc(v_a_6648_);
v___y_6535_ = v___y_6589_;
v___y_6536_ = v_a_6648_;
v___y_6537_ = v_a_6633_;
v___y_6538_ = v___y_6590_;
v___y_6539_ = v___f_6653_;
v___y_6540_ = v_monadInfo_6649_;
v___y_6541_ = v___y_6591_;
v___y_6542_ = v_a_6645_;
v___y_6543_ = v___f_6651_;
v___y_6544_ = v_a_6623_;
v___y_6545_ = v_a_6641_;
v___y_6546_ = v_a_6616_;
v___y_6547_ = v_a_6614_;
v___y_6548_ = v___y_6592_;
v___y_6549_ = v___f_6651_;
v___y_6550_ = v_a_6609_;
v___y_6551_ = v_a_6648_;
v___y_6552_ = v___y_6607_;
v___y_6553_ = v___y_6595_;
v___y_6554_ = v___y_6605_;
v___y_6555_ = v_a_6623_;
v___y_6556_ = v___y_6606_;
v___y_6557_ = v_a_6641_;
v___y_6558_ = v_a_6616_;
v___y_6559_ = v___y_6596_;
v___y_6560_ = v___y_6599_;
v___y_6561_ = v___y_6604_;
v___y_6562_ = v_a_6633_;
v___y_6563_ = v___y_6594_;
v___y_6564_ = v___y_6603_;
v___y_6565_ = v___y_6602_;
v___y_6566_ = v___y_6597_;
v___y_6567_ = v___y_6598_;
v___y_6568_ = v___x_6620_;
v___y_6569_ = v_a_6614_;
v___y_6570_ = v_a_6643_;
v___y_6571_ = v___y_6601_;
v___y_6572_ = v___x_6655_;
goto v___jp_6534_;
}
else
{
size_t v___x_6658_; size_t v___x_6659_; lean_object* v___x_6660_; 
v___x_6658_ = ((size_t)0ULL);
v___x_6659_ = lean_usize_of_nat(v___x_6654_);
v___x_6660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__6(v_a_6643_, v_mutVars_6650_, v___x_6658_, v___x_6659_, v___x_6655_);
lean_inc(v_a_6614_);
lean_inc(v_a_6616_);
lean_inc(v_a_6641_);
lean_inc(v_a_6623_);
lean_inc_ref(v___f_6651_);
lean_inc(v_a_6633_);
lean_inc(v_a_6648_);
v___y_6535_ = v___y_6589_;
v___y_6536_ = v_a_6648_;
v___y_6537_ = v_a_6633_;
v___y_6538_ = v___y_6590_;
v___y_6539_ = v___f_6653_;
v___y_6540_ = v_monadInfo_6649_;
v___y_6541_ = v___y_6591_;
v___y_6542_ = v_a_6645_;
v___y_6543_ = v___f_6651_;
v___y_6544_ = v_a_6623_;
v___y_6545_ = v_a_6641_;
v___y_6546_ = v_a_6616_;
v___y_6547_ = v_a_6614_;
v___y_6548_ = v___y_6592_;
v___y_6549_ = v___f_6651_;
v___y_6550_ = v_a_6609_;
v___y_6551_ = v_a_6648_;
v___y_6552_ = v___y_6607_;
v___y_6553_ = v___y_6595_;
v___y_6554_ = v___y_6605_;
v___y_6555_ = v_a_6623_;
v___y_6556_ = v___y_6606_;
v___y_6557_ = v_a_6641_;
v___y_6558_ = v_a_6616_;
v___y_6559_ = v___y_6596_;
v___y_6560_ = v___y_6599_;
v___y_6561_ = v___y_6604_;
v___y_6562_ = v_a_6633_;
v___y_6563_ = v___y_6594_;
v___y_6564_ = v___y_6603_;
v___y_6565_ = v___y_6602_;
v___y_6566_ = v___y_6597_;
v___y_6567_ = v___y_6598_;
v___y_6568_ = v___x_6620_;
v___y_6569_ = v_a_6614_;
v___y_6570_ = v_a_6643_;
v___y_6571_ = v___y_6601_;
v___y_6572_ = v___x_6660_;
goto v___jp_6534_;
}
}
else
{
size_t v___x_6661_; size_t v___x_6662_; lean_object* v___x_6663_; 
v___x_6661_ = ((size_t)0ULL);
v___x_6662_ = lean_usize_of_nat(v___x_6654_);
v___x_6663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__6(v_a_6643_, v_mutVars_6650_, v___x_6661_, v___x_6662_, v___x_6655_);
lean_inc(v_a_6614_);
lean_inc(v_a_6616_);
lean_inc(v_a_6641_);
lean_inc(v_a_6623_);
lean_inc_ref(v___f_6651_);
lean_inc(v_a_6633_);
lean_inc(v_a_6648_);
v___y_6535_ = v___y_6589_;
v___y_6536_ = v_a_6648_;
v___y_6537_ = v_a_6633_;
v___y_6538_ = v___y_6590_;
v___y_6539_ = v___f_6653_;
v___y_6540_ = v_monadInfo_6649_;
v___y_6541_ = v___y_6591_;
v___y_6542_ = v_a_6645_;
v___y_6543_ = v___f_6651_;
v___y_6544_ = v_a_6623_;
v___y_6545_ = v_a_6641_;
v___y_6546_ = v_a_6616_;
v___y_6547_ = v_a_6614_;
v___y_6548_ = v___y_6592_;
v___y_6549_ = v___f_6651_;
v___y_6550_ = v_a_6609_;
v___y_6551_ = v_a_6648_;
v___y_6552_ = v___y_6607_;
v___y_6553_ = v___y_6595_;
v___y_6554_ = v___y_6605_;
v___y_6555_ = v_a_6623_;
v___y_6556_ = v___y_6606_;
v___y_6557_ = v_a_6641_;
v___y_6558_ = v_a_6616_;
v___y_6559_ = v___y_6596_;
v___y_6560_ = v___y_6599_;
v___y_6561_ = v___y_6604_;
v___y_6562_ = v_a_6633_;
v___y_6563_ = v___y_6594_;
v___y_6564_ = v___y_6603_;
v___y_6565_ = v___y_6602_;
v___y_6566_ = v___y_6597_;
v___y_6567_ = v___y_6598_;
v___y_6568_ = v___x_6620_;
v___y_6569_ = v_a_6614_;
v___y_6570_ = v_a_6643_;
v___y_6571_ = v___y_6601_;
v___y_6572_ = v___x_6663_;
goto v___jp_6534_;
}
}
}
else
{
lean_object* v_a_6664_; lean_object* v___x_6666_; uint8_t v_isShared_6667_; uint8_t v_isSharedCheck_6671_; 
lean_dec(v_a_6645_);
lean_dec(v_a_6643_);
lean_dec(v_a_6641_);
lean_dec(v_a_6633_);
lean_dec(v_a_6623_);
lean_dec(v_a_6616_);
lean_dec(v_a_6614_);
lean_dec(v_a_6609_);
lean_dec(v___y_6598_);
lean_dec(v___y_6597_);
lean_dec(v___y_6595_);
lean_dec(v___y_6594_);
lean_dec(v___y_6591_);
lean_dec(v___y_6590_);
lean_dec(v___y_6589_);
v_a_6664_ = lean_ctor_get(v___x_6647_, 0);
v_isSharedCheck_6671_ = !lean_is_exclusive(v___x_6647_);
if (v_isSharedCheck_6671_ == 0)
{
v___x_6666_ = v___x_6647_;
v_isShared_6667_ = v_isSharedCheck_6671_;
goto v_resetjp_6665_;
}
else
{
lean_inc(v_a_6664_);
lean_dec(v___x_6647_);
v___x_6666_ = lean_box(0);
v_isShared_6667_ = v_isSharedCheck_6671_;
goto v_resetjp_6665_;
}
v_resetjp_6665_:
{
lean_object* v___x_6669_; 
if (v_isShared_6667_ == 0)
{
v___x_6669_ = v___x_6666_;
goto v_reusejp_6668_;
}
else
{
lean_object* v_reuseFailAlloc_6670_; 
v_reuseFailAlloc_6670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6670_, 0, v_a_6664_);
v___x_6669_ = v_reuseFailAlloc_6670_;
goto v_reusejp_6668_;
}
v_reusejp_6668_:
{
return v___x_6669_;
}
}
}
}
else
{
lean_object* v_a_6672_; lean_object* v___x_6674_; uint8_t v_isShared_6675_; uint8_t v_isSharedCheck_6679_; 
lean_dec(v_a_6643_);
lean_dec(v_a_6641_);
lean_dec(v_a_6633_);
lean_dec(v_a_6623_);
lean_dec(v_a_6616_);
lean_dec(v_a_6614_);
lean_dec(v_a_6609_);
lean_dec(v___y_6598_);
lean_dec(v___y_6597_);
lean_dec(v___y_6595_);
lean_dec(v___y_6594_);
lean_dec(v___y_6591_);
lean_dec(v___y_6590_);
lean_dec(v___y_6589_);
v_a_6672_ = lean_ctor_get(v___x_6644_, 0);
v_isSharedCheck_6679_ = !lean_is_exclusive(v___x_6644_);
if (v_isSharedCheck_6679_ == 0)
{
v___x_6674_ = v___x_6644_;
v_isShared_6675_ = v_isSharedCheck_6679_;
goto v_resetjp_6673_;
}
else
{
lean_inc(v_a_6672_);
lean_dec(v___x_6644_);
v___x_6674_ = lean_box(0);
v_isShared_6675_ = v_isSharedCheck_6679_;
goto v_resetjp_6673_;
}
v_resetjp_6673_:
{
lean_object* v___x_6677_; 
if (v_isShared_6675_ == 0)
{
v___x_6677_ = v___x_6674_;
goto v_reusejp_6676_;
}
else
{
lean_object* v_reuseFailAlloc_6678_; 
v_reuseFailAlloc_6678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6678_, 0, v_a_6672_);
v___x_6677_ = v_reuseFailAlloc_6678_;
goto v_reusejp_6676_;
}
v_reusejp_6676_:
{
return v___x_6677_;
}
}
}
}
else
{
lean_object* v_a_6680_; lean_object* v___x_6682_; uint8_t v_isShared_6683_; uint8_t v_isSharedCheck_6687_; 
lean_dec(v_a_6641_);
lean_dec(v_a_6633_);
lean_dec(v_a_6623_);
lean_dec(v_a_6616_);
lean_dec(v_a_6614_);
lean_dec(v_a_6609_);
lean_dec(v___y_6598_);
lean_dec(v___y_6597_);
lean_dec(v___y_6595_);
lean_dec(v___y_6594_);
lean_dec(v___y_6591_);
lean_dec(v___y_6590_);
lean_dec(v___y_6589_);
v_a_6680_ = lean_ctor_get(v___x_6642_, 0);
v_isSharedCheck_6687_ = !lean_is_exclusive(v___x_6642_);
if (v_isSharedCheck_6687_ == 0)
{
v___x_6682_ = v___x_6642_;
v_isShared_6683_ = v_isSharedCheck_6687_;
goto v_resetjp_6681_;
}
else
{
lean_inc(v_a_6680_);
lean_dec(v___x_6642_);
v___x_6682_ = lean_box(0);
v_isShared_6683_ = v_isSharedCheck_6687_;
goto v_resetjp_6681_;
}
v_resetjp_6681_:
{
lean_object* v___x_6685_; 
if (v_isShared_6683_ == 0)
{
v___x_6685_ = v___x_6682_;
goto v_reusejp_6684_;
}
else
{
lean_object* v_reuseFailAlloc_6686_; 
v_reuseFailAlloc_6686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6686_, 0, v_a_6680_);
v___x_6685_ = v_reuseFailAlloc_6686_;
goto v_reusejp_6684_;
}
v_reusejp_6684_:
{
return v___x_6685_;
}
}
}
}
else
{
lean_dec(v_a_6633_);
lean_dec(v_a_6623_);
lean_dec(v_a_6616_);
lean_dec(v_a_6614_);
lean_dec(v_a_6609_);
lean_dec(v___y_6598_);
lean_dec(v___y_6597_);
lean_dec(v___y_6595_);
lean_dec(v___y_6594_);
lean_dec(v___y_6593_);
lean_dec(v___y_6591_);
lean_dec(v___y_6590_);
lean_dec(v___y_6589_);
return v___x_6640_;
}
}
}
}
else
{
lean_dec(v_a_6623_);
lean_dec(v_a_6616_);
lean_dec(v_a_6614_);
lean_dec(v_a_6609_);
lean_dec(v___y_6600_);
lean_dec(v___y_6598_);
lean_dec(v___y_6597_);
lean_dec(v___y_6595_);
lean_dec(v___y_6594_);
lean_dec(v___y_6593_);
lean_dec(v___y_6591_);
lean_dec(v___y_6590_);
lean_dec(v___y_6589_);
return v___x_6632_;
}
}
}
}
else
{
lean_dec(v_a_6616_);
lean_dec(v_a_6614_);
lean_dec(v_a_6609_);
lean_dec(v___y_6600_);
lean_dec(v___y_6598_);
lean_dec(v___y_6597_);
lean_dec(v___y_6595_);
lean_dec(v___y_6594_);
lean_dec(v___y_6593_);
lean_dec(v___y_6591_);
lean_dec(v___y_6590_);
lean_dec(v___y_6589_);
return v___x_6622_;
}
}
else
{
lean_object* v_a_6692_; lean_object* v___x_6694_; uint8_t v_isShared_6695_; uint8_t v_isSharedCheck_6699_; 
lean_dec(v_a_6614_);
lean_dec(v_a_6609_);
lean_dec(v___y_6600_);
lean_dec(v___y_6598_);
lean_dec(v___y_6597_);
lean_dec(v___y_6595_);
lean_dec(v___y_6594_);
lean_dec(v___y_6593_);
lean_dec(v___y_6591_);
lean_dec(v___y_6590_);
lean_dec(v___y_6589_);
v_a_6692_ = lean_ctor_get(v___x_6615_, 0);
v_isSharedCheck_6699_ = !lean_is_exclusive(v___x_6615_);
if (v_isSharedCheck_6699_ == 0)
{
v___x_6694_ = v___x_6615_;
v_isShared_6695_ = v_isSharedCheck_6699_;
goto v_resetjp_6693_;
}
else
{
lean_inc(v_a_6692_);
lean_dec(v___x_6615_);
v___x_6694_ = lean_box(0);
v_isShared_6695_ = v_isSharedCheck_6699_;
goto v_resetjp_6693_;
}
v_resetjp_6693_:
{
lean_object* v___x_6697_; 
if (v_isShared_6695_ == 0)
{
v___x_6697_ = v___x_6694_;
goto v_reusejp_6696_;
}
else
{
lean_object* v_reuseFailAlloc_6698_; 
v_reuseFailAlloc_6698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6698_, 0, v_a_6692_);
v___x_6697_ = v_reuseFailAlloc_6698_;
goto v_reusejp_6696_;
}
v_reusejp_6696_:
{
return v___x_6697_;
}
}
}
}
else
{
lean_object* v_a_6700_; lean_object* v___x_6702_; uint8_t v_isShared_6703_; uint8_t v_isSharedCheck_6707_; 
lean_dec(v_a_6609_);
lean_dec(v___y_6600_);
lean_dec(v___y_6598_);
lean_dec(v___y_6597_);
lean_dec(v___y_6595_);
lean_dec(v___y_6594_);
lean_dec(v___y_6593_);
lean_dec(v___y_6591_);
lean_dec(v___y_6590_);
lean_dec(v___y_6589_);
v_a_6700_ = lean_ctor_get(v___x_6613_, 0);
v_isSharedCheck_6707_ = !lean_is_exclusive(v___x_6613_);
if (v_isSharedCheck_6707_ == 0)
{
v___x_6702_ = v___x_6613_;
v_isShared_6703_ = v_isSharedCheck_6707_;
goto v_resetjp_6701_;
}
else
{
lean_inc(v_a_6700_);
lean_dec(v___x_6613_);
v___x_6702_ = lean_box(0);
v_isShared_6703_ = v_isSharedCheck_6707_;
goto v_resetjp_6701_;
}
v_resetjp_6701_:
{
lean_object* v___x_6705_; 
if (v_isShared_6703_ == 0)
{
v___x_6705_ = v___x_6702_;
goto v_reusejp_6704_;
}
else
{
lean_object* v_reuseFailAlloc_6706_; 
v_reuseFailAlloc_6706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6706_, 0, v_a_6700_);
v___x_6705_ = v_reuseFailAlloc_6706_;
goto v_reusejp_6704_;
}
v_reusejp_6704_:
{
return v___x_6705_;
}
}
}
}
else
{
lean_object* v_a_6708_; lean_object* v___x_6710_; uint8_t v_isShared_6711_; uint8_t v_isSharedCheck_6715_; 
lean_dec(v_a_6609_);
lean_dec(v___y_6600_);
lean_dec(v___y_6598_);
lean_dec(v___y_6597_);
lean_dec(v___y_6595_);
lean_dec(v___y_6594_);
lean_dec(v___y_6593_);
lean_dec(v___y_6591_);
lean_dec(v___y_6590_);
lean_dec(v___y_6589_);
v_a_6708_ = lean_ctor_get(v___x_6612_, 0);
v_isSharedCheck_6715_ = !lean_is_exclusive(v___x_6612_);
if (v_isSharedCheck_6715_ == 0)
{
v___x_6710_ = v___x_6612_;
v_isShared_6711_ = v_isSharedCheck_6715_;
goto v_resetjp_6709_;
}
else
{
lean_inc(v_a_6708_);
lean_dec(v___x_6612_);
v___x_6710_ = lean_box(0);
v_isShared_6711_ = v_isSharedCheck_6715_;
goto v_resetjp_6709_;
}
v_resetjp_6709_:
{
lean_object* v___x_6713_; 
if (v_isShared_6711_ == 0)
{
v___x_6713_ = v___x_6710_;
goto v_reusejp_6712_;
}
else
{
lean_object* v_reuseFailAlloc_6714_; 
v_reuseFailAlloc_6714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6714_, 0, v_a_6708_);
v___x_6713_ = v_reuseFailAlloc_6714_;
goto v_reusejp_6712_;
}
v_reusejp_6712_:
{
return v___x_6713_;
}
}
}
}
else
{
lean_object* v_a_6716_; lean_object* v___x_6718_; uint8_t v_isShared_6719_; uint8_t v_isSharedCheck_6723_; 
lean_dec(v___y_6600_);
lean_dec(v___y_6598_);
lean_dec(v___y_6597_);
lean_dec(v___y_6595_);
lean_dec(v___y_6594_);
lean_dec(v___y_6593_);
lean_dec(v___y_6591_);
lean_dec(v___y_6590_);
lean_dec(v___y_6589_);
v_a_6716_ = lean_ctor_get(v___x_6608_, 0);
v_isSharedCheck_6723_ = !lean_is_exclusive(v___x_6608_);
if (v_isSharedCheck_6723_ == 0)
{
v___x_6718_ = v___x_6608_;
v_isShared_6719_ = v_isSharedCheck_6723_;
goto v_resetjp_6717_;
}
else
{
lean_inc(v_a_6716_);
lean_dec(v___x_6608_);
v___x_6718_ = lean_box(0);
v_isShared_6719_ = v_isSharedCheck_6723_;
goto v_resetjp_6717_;
}
v_resetjp_6717_:
{
lean_object* v___x_6721_; 
if (v_isShared_6719_ == 0)
{
v___x_6721_ = v___x_6718_;
goto v_reusejp_6720_;
}
else
{
lean_object* v_reuseFailAlloc_6722_; 
v_reuseFailAlloc_6722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6722_, 0, v_a_6716_);
v___x_6721_ = v_reuseFailAlloc_6722_;
goto v_reusejp_6720_;
}
v_reusejp_6720_:
{
return v___x_6721_;
}
}
}
}
v___jp_6724_:
{
if (lean_obj_tag(v___y_6726_) == 1)
{
lean_object* v_val_6743_; lean_object* v___x_6744_; lean_object* v___x_6745_; lean_object* v___x_6746_; 
v_val_6743_ = lean_ctor_get(v___y_6726_, 0);
v___x_6744_ = l_Lean_Syntax_getArg(v_val_6743_, v___x_6156_);
v___x_6745_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___closed__23, &l_Lean_Elab_Do_elabDoFor___closed__23_once, _init_l_Lean_Elab_Do_elabDoFor___closed__23);
v___x_6746_ = l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7(v___x_6744_, v___x_6745_, v___y_6728_, v___y_6729_, v___y_6733_, v___y_6739_, v___y_6734_, v___y_6736_, v___y_6732_);
lean_dec(v___x_6744_);
if (lean_obj_tag(v___x_6746_) == 0)
{
lean_dec_ref_known(v___x_6746_, 1);
lean_inc(v___y_6725_);
v___y_6589_ = v___y_6725_;
v___y_6590_ = v___y_6727_;
v___y_6591_ = v___y_6730_;
v___y_6592_ = v___y_6740_;
v___y_6593_ = v___y_6725_;
v___y_6594_ = v___y_6726_;
v___y_6595_ = v___y_6741_;
v___y_6596_ = v___y_6738_;
v___y_6597_ = v___y_6735_;
v___y_6598_ = v___y_6731_;
v___y_6599_ = v___y_6737_;
v___y_6600_ = v___y_6742_;
v___y_6601_ = v___y_6728_;
v___y_6602_ = v___y_6729_;
v___y_6603_ = v___y_6733_;
v___y_6604_ = v___y_6739_;
v___y_6605_ = v___y_6734_;
v___y_6606_ = v___y_6736_;
v___y_6607_ = v___y_6732_;
goto v___jp_6588_;
}
else
{
lean_object* v_a_6747_; lean_object* v___x_6749_; uint8_t v_isShared_6750_; uint8_t v_isSharedCheck_6754_; 
lean_dec_ref_known(v___y_6726_, 1);
lean_dec(v___y_6742_);
lean_dec(v___y_6741_);
lean_dec(v___y_6735_);
lean_dec(v___y_6731_);
lean_dec(v___y_6730_);
lean_dec(v___y_6727_);
lean_dec(v___y_6725_);
lean_dec(v_tk_6587_);
lean_dec_ref(v_dec_6140_);
v_a_6747_ = lean_ctor_get(v___x_6746_, 0);
v_isSharedCheck_6754_ = !lean_is_exclusive(v___x_6746_);
if (v_isSharedCheck_6754_ == 0)
{
v___x_6749_ = v___x_6746_;
v_isShared_6750_ = v_isSharedCheck_6754_;
goto v_resetjp_6748_;
}
else
{
lean_inc(v_a_6747_);
lean_dec(v___x_6746_);
v___x_6749_ = lean_box(0);
v_isShared_6750_ = v_isSharedCheck_6754_;
goto v_resetjp_6748_;
}
v_resetjp_6748_:
{
lean_object* v___x_6752_; 
if (v_isShared_6750_ == 0)
{
v___x_6752_ = v___x_6749_;
goto v_reusejp_6751_;
}
else
{
lean_object* v_reuseFailAlloc_6753_; 
v_reuseFailAlloc_6753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6753_, 0, v_a_6747_);
v___x_6752_ = v_reuseFailAlloc_6753_;
goto v_reusejp_6751_;
}
v_reusejp_6751_:
{
return v___x_6752_;
}
}
}
}
else
{
lean_inc(v___y_6725_);
v___y_6589_ = v___y_6725_;
v___y_6590_ = v___y_6727_;
v___y_6591_ = v___y_6730_;
v___y_6592_ = v___y_6740_;
v___y_6593_ = v___y_6725_;
v___y_6594_ = v___y_6726_;
v___y_6595_ = v___y_6741_;
v___y_6596_ = v___y_6738_;
v___y_6597_ = v___y_6735_;
v___y_6598_ = v___y_6731_;
v___y_6599_ = v___y_6737_;
v___y_6600_ = v___y_6742_;
v___y_6601_ = v___y_6728_;
v___y_6602_ = v___y_6729_;
v___y_6603_ = v___y_6733_;
v___y_6604_ = v___y_6739_;
v___y_6605_ = v___y_6734_;
v___y_6606_ = v___y_6736_;
v___y_6607_ = v___y_6732_;
goto v___jp_6588_;
}
}
v___jp_6755_:
{
lean_object* v___x_6773_; lean_object* v_body_6774_; 
v___x_6773_ = lean_unsigned_to_nat(5u);
v_body_6774_ = l_Lean_Syntax_getArg(v_stx_6139_, v___x_6773_);
lean_dec(v_stx_6139_);
if (lean_obj_tag(v___y_6761_) == 1)
{
lean_object* v_val_6775_; lean_object* v___x_6776_; lean_object* v___x_6777_; lean_object* v___x_6778_; 
v_val_6775_ = lean_ctor_get(v___y_6761_, 0);
v___x_6776_ = l_Lean_Syntax_getArg(v_val_6775_, v___x_6156_);
v___x_6777_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___closed__25, &l_Lean_Elab_Do_elabDoFor___closed__25_once, _init_l_Lean_Elab_Do_elabDoFor___closed__25);
v___x_6778_ = l_Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7(v___x_6776_, v___x_6777_, v___y_6766_, v___y_6767_, v___y_6768_, v___y_6769_, v___y_6770_, v___y_6771_, v___y_6772_);
lean_dec(v___x_6776_);
if (lean_obj_tag(v___x_6778_) == 0)
{
lean_dec_ref_known(v___x_6778_, 1);
v___y_6725_ = v_body_6774_;
v___y_6726_ = v_dec_x3f_6765_;
v___y_6727_ = v___y_6756_;
v___y_6728_ = v___y_6766_;
v___y_6729_ = v___y_6767_;
v___y_6730_ = v___y_6757_;
v___y_6731_ = v___y_6762_;
v___y_6732_ = v___y_6772_;
v___y_6733_ = v___y_6768_;
v___y_6734_ = v___y_6770_;
v___y_6735_ = v___y_6761_;
v___y_6736_ = v___y_6771_;
v___y_6737_ = v___y_6764_;
v___y_6738_ = v___y_6760_;
v___y_6739_ = v___y_6769_;
v___y_6740_ = v___y_6758_;
v___y_6741_ = v___y_6759_;
v___y_6742_ = v___y_6763_;
goto v___jp_6724_;
}
else
{
lean_object* v_a_6779_; lean_object* v___x_6781_; uint8_t v_isShared_6782_; uint8_t v_isSharedCheck_6786_; 
lean_dec_ref_known(v___y_6761_, 1);
lean_dec(v_body_6774_);
lean_dec(v_dec_x3f_6765_);
lean_dec(v___y_6763_);
lean_dec(v___y_6762_);
lean_dec(v___y_6759_);
lean_dec(v___y_6757_);
lean_dec(v___y_6756_);
lean_dec(v_tk_6587_);
lean_dec_ref(v_dec_6140_);
v_a_6779_ = lean_ctor_get(v___x_6778_, 0);
v_isSharedCheck_6786_ = !lean_is_exclusive(v___x_6778_);
if (v_isSharedCheck_6786_ == 0)
{
v___x_6781_ = v___x_6778_;
v_isShared_6782_ = v_isSharedCheck_6786_;
goto v_resetjp_6780_;
}
else
{
lean_inc(v_a_6779_);
lean_dec(v___x_6778_);
v___x_6781_ = lean_box(0);
v_isShared_6782_ = v_isSharedCheck_6786_;
goto v_resetjp_6780_;
}
v_resetjp_6780_:
{
lean_object* v___x_6784_; 
if (v_isShared_6782_ == 0)
{
v___x_6784_ = v___x_6781_;
goto v_reusejp_6783_;
}
else
{
lean_object* v_reuseFailAlloc_6785_; 
v_reuseFailAlloc_6785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6785_, 0, v_a_6779_);
v___x_6784_ = v_reuseFailAlloc_6785_;
goto v_reusejp_6783_;
}
v_reusejp_6783_:
{
return v___x_6784_;
}
}
}
}
else
{
v___y_6725_ = v_body_6774_;
v___y_6726_ = v_dec_x3f_6765_;
v___y_6727_ = v___y_6756_;
v___y_6728_ = v___y_6766_;
v___y_6729_ = v___y_6767_;
v___y_6730_ = v___y_6757_;
v___y_6731_ = v___y_6762_;
v___y_6732_ = v___y_6772_;
v___y_6733_ = v___y_6768_;
v___y_6734_ = v___y_6770_;
v___y_6735_ = v___y_6761_;
v___y_6736_ = v___y_6771_;
v___y_6737_ = v___y_6764_;
v___y_6738_ = v___y_6760_;
v___y_6739_ = v___y_6769_;
v___y_6740_ = v___y_6758_;
v___y_6741_ = v___y_6759_;
v___y_6742_ = v___y_6763_;
goto v___jp_6724_;
}
}
v___jp_6787_:
{
lean_object* v___x_6805_; uint8_t v___x_6806_; 
v___x_6805_ = l_Lean_Syntax_getArg(v_stx_6139_, v___y_6793_);
v___x_6806_ = l_Lean_Syntax_isNone(v___x_6805_);
if (v___x_6806_ == 0)
{
uint8_t v___x_6807_; 
lean_inc(v___x_6805_);
v___x_6807_ = l_Lean_Syntax_matchesNull(v___x_6805_, v___x_6152_);
if (v___x_6807_ == 0)
{
lean_object* v___x_6808_; 
lean_dec(v___x_6805_);
lean_dec(v_inv_x3f_6797_);
lean_dec(v___y_6796_);
lean_dec(v___y_6794_);
lean_dec(v___y_6791_);
lean_dec(v___y_6789_);
lean_dec(v___y_6788_);
lean_dec(v_tk_6587_);
lean_dec_ref(v_dec_6140_);
lean_dec(v_stx_6139_);
v___x_6808_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg();
return v___x_6808_;
}
else
{
lean_object* v_dec_x3f_6809_; lean_object* v___x_6810_; uint8_t v___x_6811_; 
v_dec_x3f_6809_ = l_Lean_Syntax_getArg(v___x_6805_, v___x_6156_);
lean_dec(v___x_6805_);
v___x_6810_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__17));
lean_inc(v_dec_x3f_6809_);
v___x_6811_ = l_Lean_Syntax_isOfKind(v_dec_x3f_6809_, v___x_6810_);
if (v___x_6811_ == 0)
{
lean_object* v___x_6812_; 
lean_dec(v_dec_x3f_6809_);
lean_dec(v_inv_x3f_6797_);
lean_dec(v___y_6796_);
lean_dec(v___y_6794_);
lean_dec(v___y_6791_);
lean_dec(v___y_6789_);
lean_dec(v___y_6788_);
lean_dec(v_tk_6587_);
lean_dec_ref(v_dec_6140_);
lean_dec(v_stx_6139_);
v___x_6812_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg();
return v___x_6812_;
}
else
{
lean_object* v___x_6813_; 
v___x_6813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6813_, 0, v_dec_x3f_6809_);
v___y_6756_ = v___y_6788_;
v___y_6757_ = v___y_6789_;
v___y_6758_ = v___y_6790_;
v___y_6759_ = v___y_6791_;
v___y_6760_ = v___y_6792_;
v___y_6761_ = v_inv_x3f_6797_;
v___y_6762_ = v___y_6794_;
v___y_6763_ = v___y_6796_;
v___y_6764_ = v___y_6795_;
v_dec_x3f_6765_ = v___x_6813_;
v___y_6766_ = v___y_6798_;
v___y_6767_ = v___y_6799_;
v___y_6768_ = v___y_6800_;
v___y_6769_ = v___y_6801_;
v___y_6770_ = v___y_6802_;
v___y_6771_ = v___y_6803_;
v___y_6772_ = v___y_6804_;
goto v___jp_6755_;
}
}
}
else
{
lean_object* v___x_6814_; 
lean_dec(v___x_6805_);
v___x_6814_ = lean_box(0);
v___y_6756_ = v___y_6788_;
v___y_6757_ = v___y_6789_;
v___y_6758_ = v___y_6790_;
v___y_6759_ = v___y_6791_;
v___y_6760_ = v___y_6792_;
v___y_6761_ = v_inv_x3f_6797_;
v___y_6762_ = v___y_6794_;
v___y_6763_ = v___y_6796_;
v___y_6764_ = v___y_6795_;
v_dec_x3f_6765_ = v___x_6814_;
v___y_6766_ = v___y_6798_;
v___y_6767_ = v___y_6799_;
v___y_6768_ = v___y_6800_;
v___y_6769_ = v___y_6801_;
v___y_6770_ = v___y_6802_;
v___y_6771_ = v___y_6803_;
v___y_6772_ = v___y_6804_;
goto v___jp_6755_;
}
}
v___jp_6815_:
{
lean_object* v_x_6824_; lean_object* v___x_6825_; uint8_t v___x_6826_; 
v_x_6824_ = l_Lean_Syntax_getArg(v___x_6157_, v___x_6152_);
v___x_6825_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__21));
lean_inc(v_x_6824_);
v___x_6826_ = l_Lean_Syntax_isOfKind(v_x_6824_, v___x_6825_);
if (v___x_6826_ == 0)
{
lean_object* v___x_6827_; 
lean_dec(v_x_6824_);
lean_dec(v_h_x3f_6816_);
lean_dec(v_tk_6587_);
lean_dec(v___x_6157_);
lean_dec_ref(v_dec_6140_);
lean_dec(v_stx_6139_);
v___x_6827_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg();
return v___x_6827_;
}
else
{
lean_object* v___x_6828_; lean_object* v___x_6829_; lean_object* v___x_6830_; lean_object* v___x_6831_; uint8_t v___x_6832_; 
v___x_6828_ = lean_unsigned_to_nat(2u);
v___x_6829_ = lean_unsigned_to_nat(3u);
v___x_6830_ = l_Lean_Syntax_getArg(v___x_6157_, v___x_6829_);
lean_dec(v___x_6157_);
v___x_6831_ = l_Lean_Syntax_getArg(v_stx_6139_, v___x_6828_);
v___x_6832_ = l_Lean_Syntax_isNone(v___x_6831_);
if (v___x_6832_ == 0)
{
uint8_t v___x_6833_; 
lean_inc(v___x_6831_);
v___x_6833_ = l_Lean_Syntax_matchesNull(v___x_6831_, v___x_6152_);
if (v___x_6833_ == 0)
{
lean_object* v___x_6834_; 
lean_dec(v___x_6831_);
lean_dec(v___x_6830_);
lean_dec(v_x_6824_);
lean_dec(v_h_x3f_6816_);
lean_dec(v_tk_6587_);
lean_dec_ref(v_dec_6140_);
lean_dec(v_stx_6139_);
v___x_6834_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg();
return v___x_6834_;
}
else
{
lean_object* v_inv_x3f_6835_; lean_object* v___x_6836_; uint8_t v___x_6837_; 
v_inv_x3f_6835_ = l_Lean_Syntax_getArg(v___x_6831_, v___x_6156_);
lean_dec(v___x_6831_);
v___x_6836_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__19));
lean_inc(v_inv_x3f_6835_);
v___x_6837_ = l_Lean_Syntax_isOfKind(v_inv_x3f_6835_, v___x_6836_);
if (v___x_6837_ == 0)
{
lean_object* v___x_6838_; 
lean_dec(v_inv_x3f_6835_);
lean_dec(v___x_6830_);
lean_dec(v_x_6824_);
lean_dec(v_h_x3f_6816_);
lean_dec(v_tk_6587_);
lean_dec_ref(v_dec_6140_);
lean_dec(v_stx_6139_);
v___x_6838_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_destructInvariant_spec__0___redArg();
return v___x_6838_;
}
else
{
lean_object* v___x_6839_; 
v___x_6839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6839_, 0, v_inv_x3f_6835_);
lean_inc(v_h_x3f_6816_);
lean_inc(v_x_6824_);
v___y_6788_ = v_x_6824_;
v___y_6789_ = v_h_x3f_6816_;
v___y_6790_ = v___x_6826_;
v___y_6791_ = v_x_6824_;
v___y_6792_ = v___x_6828_;
v___y_6793_ = v___x_6829_;
v___y_6794_ = v_h_x3f_6816_;
v___y_6795_ = v___x_6826_;
v___y_6796_ = v___x_6830_;
v_inv_x3f_6797_ = v___x_6839_;
v___y_6798_ = v___y_6817_;
v___y_6799_ = v___y_6818_;
v___y_6800_ = v___y_6819_;
v___y_6801_ = v___y_6820_;
v___y_6802_ = v___y_6821_;
v___y_6803_ = v___y_6822_;
v___y_6804_ = v___y_6823_;
goto v___jp_6787_;
}
}
}
else
{
lean_object* v___x_6840_; 
lean_dec(v___x_6831_);
v___x_6840_ = lean_box(0);
lean_inc(v_h_x3f_6816_);
lean_inc(v_x_6824_);
v___y_6788_ = v_x_6824_;
v___y_6789_ = v_h_x3f_6816_;
v___y_6790_ = v___x_6826_;
v___y_6791_ = v_x_6824_;
v___y_6792_ = v___x_6828_;
v___y_6793_ = v___x_6829_;
v___y_6794_ = v_h_x3f_6816_;
v___y_6795_ = v___x_6826_;
v___y_6796_ = v___x_6830_;
v_inv_x3f_6797_ = v___x_6840_;
v___y_6798_ = v___y_6817_;
v___y_6799_ = v___y_6818_;
v___y_6800_ = v___y_6819_;
v___y_6801_ = v___y_6820_;
v___y_6802_ = v___y_6821_;
v___y_6803_ = v___y_6822_;
v___y_6804_ = v___y_6823_;
goto v___jp_6787_;
}
}
}
}
v___jp_6160_:
{
lean_object* v_doBlockResultType_6180_; lean_object* v___x_6181_; lean_object* v___y_6182_; lean_object* v___x_6183_; lean_object* v___f_6184_; lean_object* v___x_6185_; 
v_doBlockResultType_6180_ = lean_ctor_get(v___y_6173_, 3);
v___x_6181_ = lean_box(v___y_6165_);
lean_inc(v___y_6164_);
lean_inc_ref(v_doBlockResultType_6180_);
v___y_6182_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__3___boxed), 19, 11);
lean_closure_set(v___y_6182_, 0, v___x_6181_);
lean_closure_set(v___y_6182_, 1, v___y_6169_);
lean_closure_set(v___y_6182_, 2, v___y_6161_);
lean_closure_set(v___y_6182_, 3, v_doBlockResultType_6180_);
lean_closure_set(v___y_6182_, 4, v___y_6167_);
lean_closure_set(v___y_6182_, 5, v___y_6164_);
lean_closure_set(v___y_6182_, 6, v___y_6162_);
lean_closure_set(v___y_6182_, 7, v___y_6163_);
lean_closure_set(v___y_6182_, 8, v___y_6168_);
lean_closure_set(v___y_6182_, 9, v___x_6156_);
lean_closure_set(v___y_6182_, 10, v___x_6152_);
v___x_6183_ = lean_box(v___x_6159_);
v___f_6184_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__4___boxed), 13, 4);
lean_closure_set(v___f_6184_, 0, v___y_6166_);
lean_closure_set(v___f_6184_, 1, v___y_6182_);
lean_closure_set(v___f_6184_, 2, v___x_6152_);
lean_closure_set(v___f_6184_, 3, v___x_6183_);
lean_inc_ref(v___y_6171_);
v___x_6185_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v___y_6170_, v___y_6171_, v___f_6184_, v___y_6173_, v___y_6174_, v___y_6175_, v___y_6176_, v___y_6177_, v___y_6178_, v___y_6179_);
if (lean_obj_tag(v___x_6185_) == 0)
{
lean_object* v_a_6186_; lean_object* v___x_6187_; 
v_a_6186_ = lean_ctor_get(v___x_6185_, 0);
lean_inc(v_a_6186_);
lean_dec_ref_known(v___x_6185_, 1);
lean_inc_ref(v_doBlockResultType_6180_);
v___x_6187_ = l_Lean_Elab_Do_mkBindApp(v___y_6171_, v_doBlockResultType_6180_, v_forIn_6172_, v_a_6186_, v___y_6173_, v___y_6174_, v___y_6175_, v___y_6176_, v___y_6177_, v___y_6178_, v___y_6179_);
return v___x_6187_;
}
else
{
lean_dec_ref(v_forIn_6172_);
lean_dec_ref(v___y_6171_);
return v___x_6185_;
}
}
v___jp_6188_:
{
lean_object* v___x_6218_; 
v___x_6218_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkStatePat(v___y_6215_, v___y_6202_, v___y_6216_, v___y_6213_, v___y_6211_, v___y_6214_, v___y_6210_, v___y_6217_, v___y_6199_);
lean_dec_ref(v___y_6215_);
if (lean_obj_tag(v___x_6218_) == 0)
{
lean_object* v_a_6219_; lean_object* v___x_6220_; lean_object* v_a_6221_; lean_object* v___x_6222_; lean_object* v___x_6223_; uint8_t v___x_6224_; 
v_a_6219_ = lean_ctor_get(v___x_6218_, 0);
lean_inc(v_a_6219_);
lean_dec_ref_known(v___x_6218_, 1);
v___x_6220_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_assertionLanguage_x3f_spec__0___redArg(v___y_6201_, v___y_6210_);
v_a_6221_ = lean_ctor_get(v___x_6220_, 0);
lean_inc(v_a_6221_);
lean_dec_ref(v___x_6220_);
lean_inc_ref(v___y_6207_);
v___x_6222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6222_, 0, v___y_6209_);
lean_ctor_set(v___x_6222_, 1, v___y_6212_);
lean_ctor_set(v___x_6222_, 2, v___y_6206_);
lean_ctor_set(v___x_6222_, 3, v___y_6207_);
lean_ctor_set(v___x_6222_, 4, v_a_6219_);
v___x_6223_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__1));
v___x_6224_ = l_Lean_Expr_isConstOf(v_a_6221_, v___x_6223_);
lean_dec(v_a_6221_);
if (v___x_6224_ == 0)
{
if (lean_obj_tag(v___y_6200_) == 1)
{
lean_object* v_val_6225_; lean_object* v___x_6226_; lean_object* v___x_6227_; lean_object* v_a_6228_; lean_object* v___x_6230_; uint8_t v_isShared_6231_; uint8_t v_isSharedCheck_6235_; 
lean_dec_ref_known(v___x_6222_, 5);
lean_dec_ref(v___y_6208_);
lean_dec_ref(v___y_6207_);
lean_dec(v___y_6205_);
lean_dec(v___y_6204_);
lean_dec(v___y_6203_);
lean_dec_ref(v___y_6198_);
lean_dec_ref(v___y_6197_);
lean_dec_ref(v___y_6196_);
lean_dec_ref(v___y_6195_);
lean_dec(v___y_6194_);
lean_dec_ref(v___y_6192_);
lean_dec(v___y_6190_);
lean_dec(v___y_6189_);
v_val_6225_ = lean_ctor_get(v___y_6200_, 0);
lean_inc(v_val_6225_);
lean_dec_ref_known(v___y_6200_, 1);
v___x_6226_ = lean_obj_once(&l_Lean_Elab_Do_elabDoFor___closed__3, &l_Lean_Elab_Do_elabDoFor___closed__3_once, _init_l_Lean_Elab_Do_elabDoFor___closed__3);
v___x_6227_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_checkAssertionBinders_spec__0___redArg(v_val_6225_, v___x_6226_, v___y_6216_, v___y_6213_, v___y_6211_, v___y_6214_, v___y_6210_, v___y_6217_, v___y_6199_);
lean_dec(v_val_6225_);
v_a_6228_ = lean_ctor_get(v___x_6227_, 0);
v_isSharedCheck_6235_ = !lean_is_exclusive(v___x_6227_);
if (v_isSharedCheck_6235_ == 0)
{
v___x_6230_ = v___x_6227_;
v_isShared_6231_ = v_isSharedCheck_6235_;
goto v_resetjp_6229_;
}
else
{
lean_inc(v_a_6228_);
lean_dec(v___x_6227_);
v___x_6230_ = lean_box(0);
v_isShared_6231_ = v_isSharedCheck_6235_;
goto v_resetjp_6229_;
}
v_resetjp_6229_:
{
lean_object* v___x_6233_; 
if (v_isShared_6231_ == 0)
{
v___x_6233_ = v___x_6230_;
goto v_reusejp_6232_;
}
else
{
lean_object* v_reuseFailAlloc_6234_; 
v_reuseFailAlloc_6234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6234_, 0, v_a_6228_);
v___x_6233_ = v_reuseFailAlloc_6234_;
goto v_reusejp_6232_;
}
v_reusejp_6232_:
{
return v___x_6233_;
}
}
}
else
{
lean_dec(v___y_6200_);
if (lean_obj_tag(v___y_6203_) == 1)
{
lean_object* v_val_6236_; lean_object* v___x_6237_; 
lean_dec_ref(v___y_6198_);
v_val_6236_ = lean_ctor_get(v___y_6203_, 0);
lean_inc(v_val_6236_);
lean_dec_ref_known(v___y_6203_, 1);
v___x_6237_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInPureWithInvariant(v___x_6222_, v_val_6236_, v___y_6204_, v___y_6208_, v___y_6216_, v___y_6213_, v___y_6211_, v___y_6214_, v___y_6210_, v___y_6217_, v___y_6199_);
lean_dec(v___y_6204_);
if (lean_obj_tag(v___x_6237_) == 0)
{
lean_object* v_a_6238_; 
v_a_6238_ = lean_ctor_get(v___x_6237_, 0);
lean_inc(v_a_6238_);
lean_dec_ref_known(v___x_6237_, 1);
v___y_6161_ = v___y_6189_;
v___y_6162_ = v___y_6190_;
v___y_6163_ = v___y_6192_;
v___y_6164_ = v___y_6191_;
v___y_6165_ = v___y_6193_;
v___y_6166_ = v___y_6194_;
v___y_6167_ = v___y_6195_;
v___y_6168_ = v___y_6196_;
v___y_6169_ = v___y_6197_;
v___y_6170_ = v___y_6205_;
v___y_6171_ = v___y_6207_;
v_forIn_6172_ = v_a_6238_;
v___y_6173_ = v___y_6216_;
v___y_6174_ = v___y_6213_;
v___y_6175_ = v___y_6211_;
v___y_6176_ = v___y_6214_;
v___y_6177_ = v___y_6210_;
v___y_6178_ = v___y_6217_;
v___y_6179_ = v___y_6199_;
goto v___jp_6160_;
}
else
{
lean_dec_ref(v___y_6207_);
lean_dec(v___y_6205_);
lean_dec_ref(v___y_6197_);
lean_dec_ref(v___y_6196_);
lean_dec_ref(v___y_6195_);
lean_dec(v___y_6194_);
lean_dec_ref(v___y_6192_);
lean_dec(v___y_6190_);
lean_dec(v___y_6189_);
return v___x_6237_;
}
}
else
{
lean_dec_ref_known(v___x_6222_, 5);
lean_dec_ref(v___y_6208_);
lean_dec(v___y_6204_);
lean_dec(v___y_6203_);
v___y_6161_ = v___y_6189_;
v___y_6162_ = v___y_6190_;
v___y_6163_ = v___y_6192_;
v___y_6164_ = v___y_6191_;
v___y_6165_ = v___y_6193_;
v___y_6166_ = v___y_6194_;
v___y_6167_ = v___y_6195_;
v___y_6168_ = v___y_6196_;
v___y_6169_ = v___y_6197_;
v___y_6170_ = v___y_6205_;
v___y_6171_ = v___y_6207_;
v_forIn_6172_ = v___y_6198_;
v___y_6173_ = v___y_6216_;
v___y_6174_ = v___y_6213_;
v___y_6175_ = v___y_6211_;
v___y_6176_ = v___y_6214_;
v___y_6177_ = v___y_6210_;
v___y_6178_ = v___y_6217_;
v___y_6179_ = v___y_6199_;
goto v___jp_6160_;
}
}
}
else
{
lean_object* v___x_6239_; 
lean_dec_ref(v___y_6208_);
lean_dec(v___y_6204_);
v___x_6239_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_mkForInLoopGadget(v___x_6222_, v___y_6203_, v___y_6200_, v___y_6216_, v___y_6213_, v___y_6211_, v___y_6214_, v___y_6210_, v___y_6217_, v___y_6199_);
if (lean_obj_tag(v___x_6239_) == 0)
{
lean_object* v_a_6240_; 
v_a_6240_ = lean_ctor_get(v___x_6239_, 0);
lean_inc(v_a_6240_);
lean_dec_ref_known(v___x_6239_, 1);
if (lean_obj_tag(v_a_6240_) == 1)
{
lean_object* v_val_6241_; 
lean_dec_ref(v___y_6198_);
v_val_6241_ = lean_ctor_get(v_a_6240_, 0);
lean_inc(v_val_6241_);
lean_dec_ref_known(v_a_6240_, 1);
v___y_6161_ = v___y_6189_;
v___y_6162_ = v___y_6190_;
v___y_6163_ = v___y_6192_;
v___y_6164_ = v___y_6191_;
v___y_6165_ = v___y_6193_;
v___y_6166_ = v___y_6194_;
v___y_6167_ = v___y_6195_;
v___y_6168_ = v___y_6196_;
v___y_6169_ = v___y_6197_;
v___y_6170_ = v___y_6205_;
v___y_6171_ = v___y_6207_;
v_forIn_6172_ = v_val_6241_;
v___y_6173_ = v___y_6216_;
v___y_6174_ = v___y_6213_;
v___y_6175_ = v___y_6211_;
v___y_6176_ = v___y_6214_;
v___y_6177_ = v___y_6210_;
v___y_6178_ = v___y_6217_;
v___y_6179_ = v___y_6199_;
goto v___jp_6160_;
}
else
{
lean_dec(v_a_6240_);
v___y_6161_ = v___y_6189_;
v___y_6162_ = v___y_6190_;
v___y_6163_ = v___y_6192_;
v___y_6164_ = v___y_6191_;
v___y_6165_ = v___y_6193_;
v___y_6166_ = v___y_6194_;
v___y_6167_ = v___y_6195_;
v___y_6168_ = v___y_6196_;
v___y_6169_ = v___y_6197_;
v___y_6170_ = v___y_6205_;
v___y_6171_ = v___y_6207_;
v_forIn_6172_ = v___y_6198_;
v___y_6173_ = v___y_6216_;
v___y_6174_ = v___y_6213_;
v___y_6175_ = v___y_6211_;
v___y_6176_ = v___y_6214_;
v___y_6177_ = v___y_6210_;
v___y_6178_ = v___y_6217_;
v___y_6179_ = v___y_6199_;
goto v___jp_6160_;
}
}
else
{
lean_object* v_a_6242_; lean_object* v___x_6244_; uint8_t v_isShared_6245_; uint8_t v_isSharedCheck_6249_; 
lean_dec_ref(v___y_6207_);
lean_dec(v___y_6205_);
lean_dec_ref(v___y_6198_);
lean_dec_ref(v___y_6197_);
lean_dec_ref(v___y_6196_);
lean_dec_ref(v___y_6195_);
lean_dec(v___y_6194_);
lean_dec_ref(v___y_6192_);
lean_dec(v___y_6190_);
lean_dec(v___y_6189_);
v_a_6242_ = lean_ctor_get(v___x_6239_, 0);
v_isSharedCheck_6249_ = !lean_is_exclusive(v___x_6239_);
if (v_isSharedCheck_6249_ == 0)
{
v___x_6244_ = v___x_6239_;
v_isShared_6245_ = v_isSharedCheck_6249_;
goto v_resetjp_6243_;
}
else
{
lean_inc(v_a_6242_);
lean_dec(v___x_6239_);
v___x_6244_ = lean_box(0);
v_isShared_6245_ = v_isSharedCheck_6249_;
goto v_resetjp_6243_;
}
v_resetjp_6243_:
{
lean_object* v___x_6247_; 
if (v_isShared_6245_ == 0)
{
v___x_6247_ = v___x_6244_;
goto v_reusejp_6246_;
}
else
{
lean_object* v_reuseFailAlloc_6248_; 
v_reuseFailAlloc_6248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6248_, 0, v_a_6242_);
v___x_6247_ = v_reuseFailAlloc_6248_;
goto v_reusejp_6246_;
}
v_reusejp_6246_:
{
return v___x_6247_;
}
}
}
}
}
else
{
lean_object* v_a_6250_; lean_object* v___x_6252_; uint8_t v_isShared_6253_; uint8_t v_isSharedCheck_6257_; 
lean_dec_ref(v___y_6212_);
lean_dec_ref(v___y_6209_);
lean_dec_ref(v___y_6208_);
lean_dec_ref(v___y_6207_);
lean_dec_ref(v___y_6206_);
lean_dec(v___y_6205_);
lean_dec(v___y_6204_);
lean_dec(v___y_6203_);
lean_dec_ref(v___y_6201_);
lean_dec(v___y_6200_);
lean_dec_ref(v___y_6198_);
lean_dec_ref(v___y_6197_);
lean_dec_ref(v___y_6196_);
lean_dec_ref(v___y_6195_);
lean_dec(v___y_6194_);
lean_dec_ref(v___y_6192_);
lean_dec(v___y_6190_);
lean_dec(v___y_6189_);
v_a_6250_ = lean_ctor_get(v___x_6218_, 0);
v_isSharedCheck_6257_ = !lean_is_exclusive(v___x_6218_);
if (v_isSharedCheck_6257_ == 0)
{
v___x_6252_ = v___x_6218_;
v_isShared_6253_ = v_isSharedCheck_6257_;
goto v_resetjp_6251_;
}
else
{
lean_inc(v_a_6250_);
lean_dec(v___x_6218_);
v___x_6252_ = lean_box(0);
v_isShared_6253_ = v_isSharedCheck_6257_;
goto v_resetjp_6251_;
}
v_resetjp_6251_:
{
lean_object* v___x_6255_; 
if (v_isShared_6253_ == 0)
{
v___x_6255_ = v___x_6252_;
goto v_reusejp_6254_;
}
else
{
lean_object* v_reuseFailAlloc_6256_; 
v_reuseFailAlloc_6256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6256_, 0, v_a_6250_);
v___x_6255_ = v_reuseFailAlloc_6256_;
goto v_reusejp_6254_;
}
v_reusejp_6254_:
{
return v___x_6255_;
}
}
}
}
v___jp_6258_:
{
lean_object* v___x_6296_; lean_object* v___x_6297_; lean_object* v___f_6298_; uint8_t v___x_6299_; lean_object* v___x_6300_; 
v___x_6296_ = l_Lean_instInhabitedExpr;
v___x_6297_ = lean_box(v___x_6159_);
lean_inc(v___y_6272_);
lean_inc(v___y_6261_);
lean_inc_ref(v___y_6274_);
lean_inc_ref(v___y_6269_);
v___f_6298_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__10___boxed), 24, 15);
lean_closure_set(v___f_6298_, 0, v___x_6296_);
lean_closure_set(v___f_6298_, 1, v___x_6156_);
lean_closure_set(v___f_6298_, 2, v___y_6262_);
lean_closure_set(v___f_6298_, 3, v___y_6269_);
lean_closure_set(v___f_6298_, 4, v___y_6274_);
lean_closure_set(v___f_6298_, 5, v___y_6261_);
lean_closure_set(v___f_6298_, 6, v___y_6270_);
lean_closure_set(v___f_6298_, 7, v___y_6271_);
lean_closure_set(v___f_6298_, 8, v___y_6268_);
lean_closure_set(v___f_6298_, 9, v___y_6259_);
lean_closure_set(v___f_6298_, 10, v___x_6297_);
lean_closure_set(v___f_6298_, 11, v___y_6272_);
lean_closure_set(v___f_6298_, 12, v___y_6267_);
lean_closure_set(v___f_6298_, 13, v___y_6266_);
lean_closure_set(v___f_6298_, 14, v___x_6152_);
v___x_6299_ = 0;
v___x_6300_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(v___y_6295_, v___f_6298_, v___x_6299_, v___y_6293_, v___y_6289_, v___y_6286_, v___y_6290_, v___y_6285_, v___y_6294_, v___y_6275_);
if (lean_obj_tag(v___x_6300_) == 0)
{
lean_object* v_a_6301_; lean_object* v___x_6302_; 
v_a_6301_ = lean_ctor_get(v___x_6300_, 0);
lean_inc_n(v_a_6301_, 2);
lean_dec_ref_known(v___x_6300_, 1);
v___x_6302_ = l_Lean_Expr_app___override(v___y_6288_, v_a_6301_);
if (lean_obj_tag(v___y_6279_) == 0)
{
if (v___y_6291_ == 0)
{
v___y_6189_ = v___y_6260_;
v___y_6190_ = v___y_6261_;
v___y_6191_ = v___y_6264_;
v___y_6192_ = v___y_6263_;
v___y_6193_ = v___y_6265_;
v___y_6194_ = v___y_6272_;
v___y_6195_ = v___y_6269_;
v___y_6196_ = v___y_6273_;
v___y_6197_ = v___y_6274_;
v___y_6198_ = v___x_6302_;
v___y_6199_ = v___y_6275_;
v___y_6200_ = v___y_6276_;
v___y_6201_ = v___y_6277_;
v___y_6202_ = v___y_6278_;
v___y_6203_ = v___y_6279_;
v___y_6204_ = v___y_6280_;
v___y_6205_ = v___y_6281_;
v___y_6206_ = v_a_6301_;
v___y_6207_ = v___y_6282_;
v___y_6208_ = v___y_6283_;
v___y_6209_ = v___y_6284_;
v___y_6210_ = v___y_6285_;
v___y_6211_ = v___y_6286_;
v___y_6212_ = v___y_6287_;
v___y_6213_ = v___y_6289_;
v___y_6214_ = v___y_6290_;
v___y_6215_ = v___y_6292_;
v___y_6216_ = v___y_6293_;
v___y_6217_ = v___y_6294_;
goto v___jp_6188_;
}
else
{
if (lean_obj_tag(v___y_6276_) == 0)
{
lean_dec(v_a_6301_);
lean_dec_ref(v___y_6292_);
lean_dec_ref(v___y_6287_);
lean_dec_ref(v___y_6284_);
lean_dec_ref(v___y_6283_);
lean_dec(v___y_6280_);
lean_dec_ref(v___y_6277_);
v___y_6161_ = v___y_6260_;
v___y_6162_ = v___y_6261_;
v___y_6163_ = v___y_6263_;
v___y_6164_ = v___y_6264_;
v___y_6165_ = v___y_6265_;
v___y_6166_ = v___y_6272_;
v___y_6167_ = v___y_6269_;
v___y_6168_ = v___y_6273_;
v___y_6169_ = v___y_6274_;
v___y_6170_ = v___y_6281_;
v___y_6171_ = v___y_6282_;
v_forIn_6172_ = v___x_6302_;
v___y_6173_ = v___y_6293_;
v___y_6174_ = v___y_6289_;
v___y_6175_ = v___y_6286_;
v___y_6176_ = v___y_6290_;
v___y_6177_ = v___y_6285_;
v___y_6178_ = v___y_6294_;
v___y_6179_ = v___y_6275_;
goto v___jp_6160_;
}
else
{
v___y_6189_ = v___y_6260_;
v___y_6190_ = v___y_6261_;
v___y_6191_ = v___y_6264_;
v___y_6192_ = v___y_6263_;
v___y_6193_ = v___y_6265_;
v___y_6194_ = v___y_6272_;
v___y_6195_ = v___y_6269_;
v___y_6196_ = v___y_6273_;
v___y_6197_ = v___y_6274_;
v___y_6198_ = v___x_6302_;
v___y_6199_ = v___y_6275_;
v___y_6200_ = v___y_6276_;
v___y_6201_ = v___y_6277_;
v___y_6202_ = v___y_6278_;
v___y_6203_ = v___y_6279_;
v___y_6204_ = v___y_6280_;
v___y_6205_ = v___y_6281_;
v___y_6206_ = v_a_6301_;
v___y_6207_ = v___y_6282_;
v___y_6208_ = v___y_6283_;
v___y_6209_ = v___y_6284_;
v___y_6210_ = v___y_6285_;
v___y_6211_ = v___y_6286_;
v___y_6212_ = v___y_6287_;
v___y_6213_ = v___y_6289_;
v___y_6214_ = v___y_6290_;
v___y_6215_ = v___y_6292_;
v___y_6216_ = v___y_6293_;
v___y_6217_ = v___y_6294_;
goto v___jp_6188_;
}
}
}
else
{
v___y_6189_ = v___y_6260_;
v___y_6190_ = v___y_6261_;
v___y_6191_ = v___y_6264_;
v___y_6192_ = v___y_6263_;
v___y_6193_ = v___y_6265_;
v___y_6194_ = v___y_6272_;
v___y_6195_ = v___y_6269_;
v___y_6196_ = v___y_6273_;
v___y_6197_ = v___y_6274_;
v___y_6198_ = v___x_6302_;
v___y_6199_ = v___y_6275_;
v___y_6200_ = v___y_6276_;
v___y_6201_ = v___y_6277_;
v___y_6202_ = v___y_6278_;
v___y_6203_ = v___y_6279_;
v___y_6204_ = v___y_6280_;
v___y_6205_ = v___y_6281_;
v___y_6206_ = v_a_6301_;
v___y_6207_ = v___y_6282_;
v___y_6208_ = v___y_6283_;
v___y_6209_ = v___y_6284_;
v___y_6210_ = v___y_6285_;
v___y_6211_ = v___y_6286_;
v___y_6212_ = v___y_6287_;
v___y_6213_ = v___y_6289_;
v___y_6214_ = v___y_6290_;
v___y_6215_ = v___y_6292_;
v___y_6216_ = v___y_6293_;
v___y_6217_ = v___y_6294_;
goto v___jp_6188_;
}
}
else
{
lean_dec_ref(v___y_6292_);
lean_dec_ref(v___y_6288_);
lean_dec_ref(v___y_6287_);
lean_dec_ref(v___y_6284_);
lean_dec_ref(v___y_6283_);
lean_dec_ref(v___y_6282_);
lean_dec(v___y_6281_);
lean_dec(v___y_6280_);
lean_dec(v___y_6279_);
lean_dec_ref(v___y_6277_);
lean_dec(v___y_6276_);
lean_dec_ref(v___y_6274_);
lean_dec_ref(v___y_6273_);
lean_dec(v___y_6272_);
lean_dec_ref(v___y_6269_);
lean_dec_ref(v___y_6263_);
lean_dec(v___y_6261_);
lean_dec(v___y_6260_);
return v___x_6300_;
}
}
v___jp_6303_:
{
lean_object* v___x_6341_; lean_object* v___x_6342_; lean_object* v___x_6343_; lean_object* v___x_6344_; 
v___x_6341_ = l_Lean_TSyntax_getId(v___y_6323_);
lean_dec(v___y_6323_);
v___x_6342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6342_, 0, v___x_6341_);
lean_ctor_set(v___x_6342_, 1, v___y_6328_);
v___x_6343_ = lean_mk_empty_array_with_capacity(v___x_6152_);
v___x_6344_ = lean_array_push(v___x_6343_, v___x_6342_);
lean_inc(v___y_6312_);
v___y_6259_ = v___y_6304_;
v___y_6260_ = v___y_6305_;
v___y_6261_ = v___y_6306_;
v___y_6262_ = v___y_6307_;
v___y_6263_ = v___y_6308_;
v___y_6264_ = v___y_6309_;
v___y_6265_ = v___y_6310_;
v___y_6266_ = v___y_6311_;
v___y_6267_ = v___y_6312_;
v___y_6268_ = v___y_6313_;
v___y_6269_ = v___y_6314_;
v___y_6270_ = v___y_6315_;
v___y_6271_ = v___y_6316_;
v___y_6272_ = v___y_6317_;
v___y_6273_ = v___y_6318_;
v___y_6274_ = v___y_6319_;
v___y_6275_ = v___y_6320_;
v___y_6276_ = v___y_6321_;
v___y_6277_ = v___y_6322_;
v___y_6278_ = v___y_6324_;
v___y_6279_ = v___y_6325_;
v___y_6280_ = v___y_6326_;
v___y_6281_ = v___y_6312_;
v___y_6282_ = v___y_6327_;
v___y_6283_ = v___y_6329_;
v___y_6284_ = v___y_6330_;
v___y_6285_ = v___y_6331_;
v___y_6286_ = v___y_6332_;
v___y_6287_ = v___y_6334_;
v___y_6288_ = v___y_6333_;
v___y_6289_ = v___y_6335_;
v___y_6290_ = v___y_6336_;
v___y_6291_ = v___y_6339_;
v___y_6292_ = v___y_6338_;
v___y_6293_ = v___y_6337_;
v___y_6294_ = v___y_6340_;
v___y_6295_ = v___x_6344_;
goto v___jp_6258_;
}
v___jp_6345_:
{
lean_object* v___x_6389_; lean_object* v___x_6390_; 
v___x_6389_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17));
v___x_6390_ = l_Lean_Core_mkFreshUserName(v___x_6389_, v___y_6387_, v___y_6388_);
if (lean_obj_tag(v___x_6390_) == 0)
{
if (lean_obj_tag(v___y_6372_) == 1)
{
if (lean_obj_tag(v_snd_6381_) == 1)
{
lean_object* v_a_6391_; lean_object* v_val_6392_; lean_object* v_val_6393_; lean_object* v___f_6394_; lean_object* v___x_6395_; lean_object* v___x_6396_; lean_object* v___x_6397_; lean_object* v___x_6398_; lean_object* v___x_6399_; lean_object* v___x_6400_; lean_object* v___x_6401_; 
lean_dec_ref(v___y_6374_);
v_a_6391_ = lean_ctor_get(v___x_6390_, 0);
lean_inc_n(v_a_6391_, 2);
lean_dec_ref_known(v___x_6390_, 1);
v_val_6392_ = lean_ctor_get(v___y_6372_, 0);
v_val_6393_ = lean_ctor_get(v_snd_6381_, 0);
lean_inc(v_val_6393_);
lean_dec_ref_known(v_snd_6381_, 1);
v___f_6394_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__11___boxed), 16, 7);
lean_closure_set(v___f_6394_, 0, v___y_6361_);
lean_closure_set(v___f_6394_, 1, v___y_6363_);
lean_closure_set(v___f_6394_, 2, v___x_6156_);
lean_closure_set(v___f_6394_, 3, v___y_6358_);
lean_closure_set(v___f_6394_, 4, v___y_6348_);
lean_closure_set(v___f_6394_, 5, v_val_6393_);
lean_closure_set(v___f_6394_, 6, v___y_6360_);
v___x_6395_ = l_Lean_TSyntax_getId(v___y_6369_);
lean_dec(v___y_6369_);
v___x_6396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6396_, 0, v___x_6395_);
lean_ctor_set(v___x_6396_, 1, v___y_6379_);
v___x_6397_ = l_Lean_TSyntax_getId(v_val_6392_);
v___x_6398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6398_, 0, v___x_6397_);
lean_ctor_set(v___x_6398_, 1, v___f_6394_);
v___x_6399_ = lean_mk_empty_array_with_capacity(v___y_6376_);
v___x_6400_ = lean_array_push(v___x_6399_, v___x_6396_);
v___x_6401_ = lean_array_push(v___x_6400_, v___x_6398_);
lean_inc_ref(v___y_6357_);
v___y_6259_ = v___y_6346_;
v___y_6260_ = v___y_6347_;
v___y_6261_ = v___y_6349_;
v___y_6262_ = v___y_6350_;
v___y_6263_ = v___y_6351_;
v___y_6264_ = v___y_6352_;
v___y_6265_ = v___y_6353_;
v___y_6266_ = v___y_6354_;
v___y_6267_ = v_a_6391_;
v___y_6268_ = v___y_6355_;
v___y_6269_ = v___y_6356_;
v___y_6270_ = v___y_6357_;
v___y_6271_ = v___y_6359_;
v___y_6272_ = v___y_6362_;
v___y_6273_ = v___y_6365_;
v___y_6274_ = v___y_6366_;
v___y_6275_ = v___y_6388_;
v___y_6276_ = v___y_6367_;
v___y_6277_ = v___y_6368_;
v___y_6278_ = v___y_6370_;
v___y_6279_ = v___y_6371_;
v___y_6280_ = v___y_6372_;
v___y_6281_ = v_a_6391_;
v___y_6282_ = v___y_6357_;
v___y_6283_ = v___y_6373_;
v___y_6284_ = v___y_6375_;
v___y_6285_ = v___y_6386_;
v___y_6286_ = v___y_6384_;
v___y_6287_ = v___y_6364_;
v___y_6288_ = v_fst_6380_;
v___y_6289_ = v___y_6383_;
v___y_6290_ = v___y_6385_;
v___y_6291_ = v___y_6377_;
v___y_6292_ = v___y_6378_;
v___y_6293_ = v___y_6382_;
v___y_6294_ = v___y_6387_;
v___y_6295_ = v___x_6401_;
goto v___jp_6258_;
}
else
{
lean_object* v_a_6402_; 
lean_dec(v_snd_6381_);
lean_dec_ref(v___y_6379_);
lean_dec(v___y_6363_);
lean_dec(v___y_6361_);
lean_dec_ref(v___y_6360_);
lean_dec_ref(v___y_6358_);
lean_dec_ref(v___y_6348_);
v_a_6402_ = lean_ctor_get(v___x_6390_, 0);
lean_inc(v_a_6402_);
lean_dec_ref_known(v___x_6390_, 1);
lean_inc_ref(v___y_6357_);
v___y_6304_ = v___y_6346_;
v___y_6305_ = v___y_6347_;
v___y_6306_ = v___y_6349_;
v___y_6307_ = v___y_6350_;
v___y_6308_ = v___y_6351_;
v___y_6309_ = v___y_6352_;
v___y_6310_ = v___y_6353_;
v___y_6311_ = v___y_6354_;
v___y_6312_ = v_a_6402_;
v___y_6313_ = v___y_6355_;
v___y_6314_ = v___y_6356_;
v___y_6315_ = v___y_6357_;
v___y_6316_ = v___y_6359_;
v___y_6317_ = v___y_6362_;
v___y_6318_ = v___y_6365_;
v___y_6319_ = v___y_6366_;
v___y_6320_ = v___y_6388_;
v___y_6321_ = v___y_6367_;
v___y_6322_ = v___y_6368_;
v___y_6323_ = v___y_6369_;
v___y_6324_ = v___y_6370_;
v___y_6325_ = v___y_6371_;
v___y_6326_ = v___y_6372_;
v___y_6327_ = v___y_6357_;
v___y_6328_ = v___y_6374_;
v___y_6329_ = v___y_6373_;
v___y_6330_ = v___y_6375_;
v___y_6331_ = v___y_6386_;
v___y_6332_ = v___y_6384_;
v___y_6333_ = v_fst_6380_;
v___y_6334_ = v___y_6364_;
v___y_6335_ = v___y_6383_;
v___y_6336_ = v___y_6385_;
v___y_6337_ = v___y_6382_;
v___y_6338_ = v___y_6378_;
v___y_6339_ = v___y_6377_;
v___y_6340_ = v___y_6387_;
goto v___jp_6303_;
}
}
else
{
lean_object* v_a_6403_; 
lean_dec(v_snd_6381_);
lean_dec_ref(v___y_6379_);
lean_dec(v___y_6363_);
lean_dec(v___y_6361_);
lean_dec_ref(v___y_6360_);
lean_dec_ref(v___y_6358_);
lean_dec_ref(v___y_6348_);
v_a_6403_ = lean_ctor_get(v___x_6390_, 0);
lean_inc(v_a_6403_);
lean_dec_ref_known(v___x_6390_, 1);
lean_inc_ref(v___y_6357_);
v___y_6304_ = v___y_6346_;
v___y_6305_ = v___y_6347_;
v___y_6306_ = v___y_6349_;
v___y_6307_ = v___y_6350_;
v___y_6308_ = v___y_6351_;
v___y_6309_ = v___y_6352_;
v___y_6310_ = v___y_6353_;
v___y_6311_ = v___y_6354_;
v___y_6312_ = v_a_6403_;
v___y_6313_ = v___y_6355_;
v___y_6314_ = v___y_6356_;
v___y_6315_ = v___y_6357_;
v___y_6316_ = v___y_6359_;
v___y_6317_ = v___y_6362_;
v___y_6318_ = v___y_6365_;
v___y_6319_ = v___y_6366_;
v___y_6320_ = v___y_6388_;
v___y_6321_ = v___y_6367_;
v___y_6322_ = v___y_6368_;
v___y_6323_ = v___y_6369_;
v___y_6324_ = v___y_6370_;
v___y_6325_ = v___y_6371_;
v___y_6326_ = v___y_6372_;
v___y_6327_ = v___y_6357_;
v___y_6328_ = v___y_6374_;
v___y_6329_ = v___y_6373_;
v___y_6330_ = v___y_6375_;
v___y_6331_ = v___y_6386_;
v___y_6332_ = v___y_6384_;
v___y_6333_ = v_fst_6380_;
v___y_6334_ = v___y_6364_;
v___y_6335_ = v___y_6383_;
v___y_6336_ = v___y_6385_;
v___y_6337_ = v___y_6382_;
v___y_6338_ = v___y_6378_;
v___y_6339_ = v___y_6377_;
v___y_6340_ = v___y_6387_;
goto v___jp_6303_;
}
}
else
{
lean_object* v_a_6404_; lean_object* v___x_6406_; uint8_t v_isShared_6407_; uint8_t v_isSharedCheck_6411_; 
lean_dec(v_snd_6381_);
lean_dec_ref(v_fst_6380_);
lean_dec_ref(v___y_6379_);
lean_dec_ref(v___y_6378_);
lean_dec_ref(v___y_6375_);
lean_dec_ref(v___y_6374_);
lean_dec_ref(v___y_6373_);
lean_dec(v___y_6372_);
lean_dec(v___y_6371_);
lean_dec(v___y_6369_);
lean_dec_ref(v___y_6368_);
lean_dec(v___y_6367_);
lean_dec_ref(v___y_6366_);
lean_dec_ref(v___y_6365_);
lean_dec_ref(v___y_6364_);
lean_dec(v___y_6363_);
lean_dec(v___y_6362_);
lean_dec(v___y_6361_);
lean_dec_ref(v___y_6360_);
lean_dec_ref(v___y_6359_);
lean_dec_ref(v___y_6358_);
lean_dec_ref(v___y_6357_);
lean_dec_ref(v___y_6356_);
lean_dec(v___y_6355_);
lean_dec(v___y_6354_);
lean_dec_ref(v___y_6351_);
lean_dec(v___y_6350_);
lean_dec(v___y_6349_);
lean_dec_ref(v___y_6348_);
lean_dec(v___y_6347_);
lean_dec(v___y_6346_);
v_a_6404_ = lean_ctor_get(v___x_6390_, 0);
v_isSharedCheck_6411_ = !lean_is_exclusive(v___x_6390_);
if (v_isSharedCheck_6411_ == 0)
{
v___x_6406_ = v___x_6390_;
v_isShared_6407_ = v_isSharedCheck_6411_;
goto v_resetjp_6405_;
}
else
{
lean_inc(v_a_6404_);
lean_dec(v___x_6390_);
v___x_6406_ = lean_box(0);
v_isShared_6407_ = v_isSharedCheck_6411_;
goto v_resetjp_6405_;
}
v_resetjp_6405_:
{
lean_object* v___x_6409_; 
if (v_isShared_6407_ == 0)
{
v___x_6409_ = v___x_6406_;
goto v_reusejp_6408_;
}
else
{
lean_object* v_reuseFailAlloc_6410_; 
v_reuseFailAlloc_6410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6410_, 0, v_a_6404_);
v___x_6409_ = v_reuseFailAlloc_6410_;
goto v_reusejp_6408_;
}
v_reusejp_6408_:
{
return v___x_6409_;
}
}
}
}
v___jp_6412_:
{
lean_object* v___x_6452_; lean_object* v___x_6453_; 
v___x_6452_ = lean_box(0);
lean_inc_ref(v___y_6422_);
lean_inc(v___y_6429_);
lean_inc_ref(v___y_6433_);
lean_inc(v___y_6430_);
lean_inc_ref(v___y_6439_);
lean_inc(v___y_6442_);
lean_inc_ref(v___y_6443_);
v___x_6453_ = lean_apply_8(v___y_6422_, v___x_6452_, v___y_6443_, v___y_6442_, v___y_6439_, v___y_6430_, v___y_6433_, v___y_6429_, lean_box(0));
if (lean_obj_tag(v___x_6453_) == 0)
{
lean_object* v_a_6454_; lean_object* v_m_6455_; lean_object* v_u_6456_; lean_object* v_v_6457_; lean_object* v___x_6458_; 
v_a_6454_ = lean_ctor_get(v___x_6453_, 0);
lean_inc(v_a_6454_);
lean_dec_ref_known(v___x_6453_, 1);
v_m_6455_ = lean_ctor_get(v___y_6444_, 0);
v_u_6456_ = lean_ctor_get(v___y_6444_, 1);
v_v_6457_ = lean_ctor_get(v___y_6444_, 2);
lean_inc(v_u_6456_);
v___x_6458_ = l_Lean_Meta_mkProdMkN(v_a_6454_, v_u_6456_, v___y_6439_, v___y_6430_, v___y_6433_, v___y_6429_);
if (lean_obj_tag(v___x_6458_) == 0)
{
lean_object* v_a_6459_; 
v_a_6459_ = lean_ctor_get(v___x_6458_, 0);
lean_inc(v_a_6459_);
lean_dec_ref_known(v___x_6458_, 1);
if (lean_obj_tag(v___y_6446_) == 0)
{
lean_object* v_fst_6460_; lean_object* v_snd_6461_; lean_object* v___x_6463_; uint8_t v_isShared_6464_; uint8_t v_isSharedCheck_6480_; 
v_fst_6460_ = lean_ctor_get(v_a_6459_, 0);
v_snd_6461_ = lean_ctor_get(v_a_6459_, 1);
v_isSharedCheck_6480_ = !lean_is_exclusive(v_a_6459_);
if (v_isSharedCheck_6480_ == 0)
{
v___x_6463_ = v_a_6459_;
v_isShared_6464_ = v_isSharedCheck_6480_;
goto v_resetjp_6462_;
}
else
{
lean_inc(v_snd_6461_);
lean_inc(v_fst_6460_);
lean_dec(v_a_6459_);
v___x_6463_ = lean_box(0);
v_isShared_6464_ = v_isSharedCheck_6480_;
goto v_resetjp_6462_;
}
v_resetjp_6462_:
{
lean_object* v___x_6465_; lean_object* v___x_6466_; lean_object* v___x_6468_; 
v___x_6465_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__5));
v___x_6466_ = lean_box(0);
lean_inc(v_v_6457_);
if (v_isShared_6464_ == 0)
{
lean_ctor_set_tag(v___x_6463_, 1);
lean_ctor_set(v___x_6463_, 1, v___x_6466_);
lean_ctor_set(v___x_6463_, 0, v_v_6457_);
v___x_6468_ = v___x_6463_;
goto v_reusejp_6467_;
}
else
{
lean_object* v_reuseFailAlloc_6479_; 
v_reuseFailAlloc_6479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6479_, 0, v_v_6457_);
lean_ctor_set(v_reuseFailAlloc_6479_, 1, v___x_6466_);
v___x_6468_ = v_reuseFailAlloc_6479_;
goto v_reusejp_6467_;
}
v_reusejp_6467_:
{
lean_object* v___x_6469_; lean_object* v___x_6470_; lean_object* v___x_6471_; lean_object* v___x_6472_; lean_object* v___x_6473_; lean_object* v___x_6474_; 
lean_inc(v_u_6456_);
v___x_6469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6469_, 0, v_u_6456_);
lean_ctor_set(v___x_6469_, 1, v___x_6468_);
v___x_6470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6470_, 0, v___y_6448_);
lean_ctor_set(v___x_6470_, 1, v___x_6469_);
v___x_6471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6471_, 0, v___y_6435_);
lean_ctor_set(v___x_6471_, 1, v___x_6470_);
lean_inc_ref(v___x_6471_);
v___x_6472_ = l_Lean_mkConst(v___x_6465_, v___x_6471_);
lean_inc_ref(v___y_6431_);
lean_inc_ref(v___y_6440_);
lean_inc_ref(v_m_6455_);
v___x_6473_ = l_Lean_mkApp3(v___x_6472_, v_m_6455_, v___y_6440_, v___y_6431_);
v___x_6474_ = l_Lean_Elab_Term_mkInstMVar(v___x_6473_, v___x_6452_, v___y_6443_, v___y_6442_, v___y_6439_, v___y_6430_, v___y_6433_, v___y_6429_);
if (lean_obj_tag(v___x_6474_) == 0)
{
lean_object* v_a_6475_; lean_object* v___x_6476_; lean_object* v___x_6477_; lean_object* v___x_6478_; 
v_a_6475_ = lean_ctor_get(v___x_6474_, 0);
lean_inc(v_a_6475_);
lean_dec_ref_known(v___x_6474_, 1);
v___x_6476_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__7));
v___x_6477_ = l_Lean_mkConst(v___x_6476_, v___x_6471_);
lean_inc(v_fst_6460_);
lean_inc_ref(v___y_6434_);
lean_inc(v_snd_6461_);
lean_inc_ref(v___y_6431_);
lean_inc_ref(v___y_6440_);
lean_inc_ref(v_m_6455_);
v___x_6478_ = l_Lean_mkApp7(v___x_6477_, v_m_6455_, v___y_6440_, v___y_6431_, v_a_6475_, v_snd_6461_, v___y_6434_, v_fst_6460_);
lean_inc(v_u_6456_);
v___y_6346_ = v___y_6413_;
v___y_6347_ = v___y_6414_;
v___y_6348_ = v___y_6415_;
v___y_6349_ = v_u_6456_;
v___y_6350_ = v___y_6416_;
v___y_6351_ = v___y_6417_;
v___y_6352_ = v_v_6457_;
v___y_6353_ = v___y_6418_;
v___y_6354_ = v___y_6419_;
v___y_6355_ = v___x_6452_;
v___y_6356_ = v___y_6420_;
v___y_6357_ = v_snd_6461_;
v___y_6358_ = v___y_6421_;
v___y_6359_ = v___y_6422_;
v___y_6360_ = v___y_6423_;
v___y_6361_ = v___y_6424_;
v___y_6362_ = v___y_6451_;
v___y_6363_ = v___y_6425_;
v___y_6364_ = v_fst_6460_;
v___y_6365_ = v___y_6426_;
v___y_6366_ = v___y_6427_;
v___y_6367_ = v___y_6441_;
v___y_6368_ = v___y_6440_;
v___y_6369_ = v___y_6428_;
v___y_6370_ = v___y_6418_;
v___y_6371_ = v___y_6445_;
v___y_6372_ = v___y_6446_;
v___y_6373_ = v___y_6431_;
v___y_6374_ = v___y_6432_;
v___y_6375_ = v___y_6434_;
v___y_6376_ = v___y_6436_;
v___y_6377_ = v___y_6437_;
v___y_6378_ = v___y_6449_;
v___y_6379_ = v___y_6438_;
v_fst_6380_ = v___x_6478_;
v_snd_6381_ = v___x_6452_;
v___y_6382_ = v___y_6450_;
v___y_6383_ = v___y_6443_;
v___y_6384_ = v___y_6442_;
v___y_6385_ = v___y_6439_;
v___y_6386_ = v___y_6430_;
v___y_6387_ = v___y_6433_;
v___y_6388_ = v___y_6429_;
goto v___jp_6345_;
}
else
{
lean_dec_ref_known(v___x_6471_, 2);
lean_dec(v_snd_6461_);
lean_dec(v_fst_6460_);
lean_dec(v___y_6451_);
lean_dec_ref(v___y_6449_);
lean_dec(v___y_6445_);
lean_dec(v___y_6441_);
lean_dec_ref(v___y_6440_);
lean_dec_ref(v___y_6438_);
lean_dec_ref(v___y_6434_);
lean_dec_ref(v___y_6432_);
lean_dec_ref(v___y_6431_);
lean_dec(v___y_6428_);
lean_dec_ref(v___y_6427_);
lean_dec_ref(v___y_6426_);
lean_dec(v___y_6425_);
lean_dec(v___y_6424_);
lean_dec_ref(v___y_6423_);
lean_dec_ref(v___y_6422_);
lean_dec_ref(v___y_6421_);
lean_dec_ref(v___y_6420_);
lean_dec(v___y_6419_);
lean_dec_ref(v___y_6417_);
lean_dec(v___y_6416_);
lean_dec_ref(v___y_6415_);
lean_dec(v___y_6414_);
lean_dec(v___y_6413_);
return v___x_6474_;
}
}
}
}
else
{
lean_object* v_fst_6481_; lean_object* v_snd_6482_; lean_object* v___x_6484_; uint8_t v_isShared_6485_; uint8_t v_isSharedCheck_6517_; 
v_fst_6481_ = lean_ctor_get(v_a_6459_, 0);
v_snd_6482_ = lean_ctor_get(v_a_6459_, 1);
v_isSharedCheck_6517_ = !lean_is_exclusive(v_a_6459_);
if (v_isSharedCheck_6517_ == 0)
{
v___x_6484_ = v_a_6459_;
v_isShared_6485_ = v_isSharedCheck_6517_;
goto v_resetjp_6483_;
}
else
{
lean_inc(v_snd_6482_);
lean_inc(v_fst_6481_);
lean_dec(v_a_6459_);
v___x_6484_ = lean_box(0);
v_isShared_6485_ = v_isSharedCheck_6517_;
goto v_resetjp_6483_;
}
v_resetjp_6483_:
{
lean_object* v___x_6486_; lean_object* v___x_6487_; lean_object* v___x_6489_; 
v___x_6486_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__8));
v___x_6487_ = lean_box(0);
lean_inc(v___y_6435_);
if (v_isShared_6485_ == 0)
{
lean_ctor_set_tag(v___x_6484_, 1);
lean_ctor_set(v___x_6484_, 1, v___x_6487_);
lean_ctor_set(v___x_6484_, 0, v___y_6435_);
v___x_6489_ = v___x_6484_;
goto v_reusejp_6488_;
}
else
{
lean_object* v_reuseFailAlloc_6516_; 
v_reuseFailAlloc_6516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6516_, 0, v___y_6435_);
lean_ctor_set(v_reuseFailAlloc_6516_, 1, v___x_6487_);
v___x_6489_ = v_reuseFailAlloc_6516_;
goto v_reusejp_6488_;
}
v_reusejp_6488_:
{
lean_object* v___x_6490_; lean_object* v___x_6491_; lean_object* v___x_6492_; lean_object* v___x_6493_; lean_object* v___x_6494_; lean_object* v___x_6495_; 
lean_inc(v___y_6448_);
v___x_6490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6490_, 0, v___y_6448_);
lean_ctor_set(v___x_6490_, 1, v___x_6489_);
v___x_6491_ = l_Lean_mkConst(v___x_6486_, v___x_6490_);
lean_inc_ref(v___y_6440_);
lean_inc_ref(v___y_6431_);
v___x_6492_ = l_Lean_mkAppB(v___x_6491_, v___y_6431_, v___y_6440_);
v___x_6493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6493_, 0, v___x_6492_);
v___x_6494_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__10));
v___x_6495_ = l_Lean_Meta_mkFreshExprMVar(v___x_6493_, v___y_6447_, v___x_6494_, v___y_6439_, v___y_6430_, v___y_6433_, v___y_6429_);
if (lean_obj_tag(v___x_6495_) == 0)
{
lean_object* v_a_6496_; lean_object* v___x_6497_; lean_object* v___x_6498_; lean_object* v___x_6499_; lean_object* v___x_6500_; lean_object* v___x_6501_; lean_object* v___x_6502_; lean_object* v___x_6503_; lean_object* v___x_6504_; 
v_a_6496_ = lean_ctor_get(v___x_6495_, 0);
lean_inc_n(v_a_6496_, 2);
lean_dec_ref_known(v___x_6495_, 1);
v___x_6497_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__12));
lean_inc(v_v_6457_);
v___x_6498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6498_, 0, v_v_6457_);
lean_ctor_set(v___x_6498_, 1, v___x_6487_);
lean_inc(v_u_6456_);
v___x_6499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6499_, 0, v_u_6456_);
lean_ctor_set(v___x_6499_, 1, v___x_6498_);
v___x_6500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6500_, 0, v___y_6448_);
lean_ctor_set(v___x_6500_, 1, v___x_6499_);
v___x_6501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6501_, 0, v___y_6435_);
lean_ctor_set(v___x_6501_, 1, v___x_6500_);
lean_inc_ref(v___x_6501_);
v___x_6502_ = l_Lean_mkConst(v___x_6497_, v___x_6501_);
lean_inc_ref(v___y_6431_);
lean_inc_ref(v___y_6440_);
lean_inc_ref(v_m_6455_);
v___x_6503_ = l_Lean_mkApp4(v___x_6502_, v_m_6455_, v___y_6440_, v___y_6431_, v_a_6496_);
v___x_6504_ = l_Lean_Elab_Term_mkInstMVar(v___x_6503_, v___x_6452_, v___y_6443_, v___y_6442_, v___y_6439_, v___y_6430_, v___y_6433_, v___y_6429_);
if (lean_obj_tag(v___x_6504_) == 0)
{
lean_object* v_a_6505_; lean_object* v___x_6507_; uint8_t v_isShared_6508_; uint8_t v_isSharedCheck_6515_; 
v_a_6505_ = lean_ctor_get(v___x_6504_, 0);
v_isSharedCheck_6515_ = !lean_is_exclusive(v___x_6504_);
if (v_isSharedCheck_6515_ == 0)
{
v___x_6507_ = v___x_6504_;
v_isShared_6508_ = v_isSharedCheck_6515_;
goto v_resetjp_6506_;
}
else
{
lean_inc(v_a_6505_);
lean_dec(v___x_6504_);
v___x_6507_ = lean_box(0);
v_isShared_6508_ = v_isSharedCheck_6515_;
goto v_resetjp_6506_;
}
v_resetjp_6506_:
{
lean_object* v___x_6509_; lean_object* v___x_6510_; lean_object* v___x_6511_; lean_object* v___x_6513_; 
v___x_6509_ = ((lean_object*)(l_Lean_Elab_Do_elabDoFor___closed__14));
v___x_6510_ = l_Lean_mkConst(v___x_6509_, v___x_6501_);
lean_inc(v_fst_6481_);
lean_inc_ref(v___y_6434_);
lean_inc(v_snd_6482_);
lean_inc(v_a_6496_);
lean_inc_ref(v___y_6431_);
lean_inc_ref(v___y_6440_);
lean_inc_ref(v_m_6455_);
v___x_6511_ = l_Lean_mkApp8(v___x_6510_, v_m_6455_, v___y_6440_, v___y_6431_, v_a_6496_, v_a_6505_, v_snd_6482_, v___y_6434_, v_fst_6481_);
if (v_isShared_6508_ == 0)
{
lean_ctor_set_tag(v___x_6507_, 1);
lean_ctor_set(v___x_6507_, 0, v_a_6496_);
v___x_6513_ = v___x_6507_;
goto v_reusejp_6512_;
}
else
{
lean_object* v_reuseFailAlloc_6514_; 
v_reuseFailAlloc_6514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6514_, 0, v_a_6496_);
v___x_6513_ = v_reuseFailAlloc_6514_;
goto v_reusejp_6512_;
}
v_reusejp_6512_:
{
lean_inc(v_u_6456_);
v___y_6346_ = v___y_6413_;
v___y_6347_ = v___y_6414_;
v___y_6348_ = v___y_6415_;
v___y_6349_ = v_u_6456_;
v___y_6350_ = v___y_6416_;
v___y_6351_ = v___y_6417_;
v___y_6352_ = v_v_6457_;
v___y_6353_ = v___y_6418_;
v___y_6354_ = v___y_6419_;
v___y_6355_ = v___x_6452_;
v___y_6356_ = v___y_6420_;
v___y_6357_ = v_snd_6482_;
v___y_6358_ = v___y_6421_;
v___y_6359_ = v___y_6422_;
v___y_6360_ = v___y_6423_;
v___y_6361_ = v___y_6424_;
v___y_6362_ = v___y_6451_;
v___y_6363_ = v___y_6425_;
v___y_6364_ = v_fst_6481_;
v___y_6365_ = v___y_6426_;
v___y_6366_ = v___y_6427_;
v___y_6367_ = v___y_6441_;
v___y_6368_ = v___y_6440_;
v___y_6369_ = v___y_6428_;
v___y_6370_ = v___y_6418_;
v___y_6371_ = v___y_6445_;
v___y_6372_ = v___y_6446_;
v___y_6373_ = v___y_6431_;
v___y_6374_ = v___y_6432_;
v___y_6375_ = v___y_6434_;
v___y_6376_ = v___y_6436_;
v___y_6377_ = v___y_6437_;
v___y_6378_ = v___y_6449_;
v___y_6379_ = v___y_6438_;
v_fst_6380_ = v___x_6511_;
v_snd_6381_ = v___x_6513_;
v___y_6382_ = v___y_6450_;
v___y_6383_ = v___y_6443_;
v___y_6384_ = v___y_6442_;
v___y_6385_ = v___y_6439_;
v___y_6386_ = v___y_6430_;
v___y_6387_ = v___y_6433_;
v___y_6388_ = v___y_6429_;
goto v___jp_6345_;
}
}
}
else
{
lean_dec_ref_known(v___x_6501_, 2);
lean_dec(v_a_6496_);
lean_dec(v_snd_6482_);
lean_dec_ref_known(v___y_6446_, 1);
lean_dec(v_fst_6481_);
lean_dec(v___y_6451_);
lean_dec_ref(v___y_6449_);
lean_dec(v___y_6445_);
lean_dec(v___y_6441_);
lean_dec_ref(v___y_6440_);
lean_dec_ref(v___y_6438_);
lean_dec_ref(v___y_6434_);
lean_dec_ref(v___y_6432_);
lean_dec_ref(v___y_6431_);
lean_dec(v___y_6428_);
lean_dec_ref(v___y_6427_);
lean_dec_ref(v___y_6426_);
lean_dec(v___y_6425_);
lean_dec(v___y_6424_);
lean_dec_ref(v___y_6423_);
lean_dec_ref(v___y_6422_);
lean_dec_ref(v___y_6421_);
lean_dec_ref(v___y_6420_);
lean_dec(v___y_6419_);
lean_dec_ref(v___y_6417_);
lean_dec(v___y_6416_);
lean_dec_ref(v___y_6415_);
lean_dec(v___y_6414_);
lean_dec(v___y_6413_);
return v___x_6504_;
}
}
else
{
lean_dec(v_snd_6482_);
lean_dec_ref_known(v___y_6446_, 1);
lean_dec(v_fst_6481_);
lean_dec(v___y_6451_);
lean_dec_ref(v___y_6449_);
lean_dec(v___y_6448_);
lean_dec(v___y_6445_);
lean_dec(v___y_6441_);
lean_dec_ref(v___y_6440_);
lean_dec_ref(v___y_6438_);
lean_dec(v___y_6435_);
lean_dec_ref(v___y_6434_);
lean_dec_ref(v___y_6432_);
lean_dec_ref(v___y_6431_);
lean_dec(v___y_6428_);
lean_dec_ref(v___y_6427_);
lean_dec_ref(v___y_6426_);
lean_dec(v___y_6425_);
lean_dec(v___y_6424_);
lean_dec_ref(v___y_6423_);
lean_dec_ref(v___y_6422_);
lean_dec_ref(v___y_6421_);
lean_dec_ref(v___y_6420_);
lean_dec(v___y_6419_);
lean_dec_ref(v___y_6417_);
lean_dec(v___y_6416_);
lean_dec_ref(v___y_6415_);
lean_dec(v___y_6414_);
lean_dec(v___y_6413_);
return v___x_6495_;
}
}
}
}
}
else
{
lean_object* v_a_6518_; lean_object* v___x_6520_; uint8_t v_isShared_6521_; uint8_t v_isSharedCheck_6525_; 
lean_dec(v___y_6451_);
lean_dec_ref(v___y_6449_);
lean_dec(v___y_6448_);
lean_dec(v___y_6446_);
lean_dec(v___y_6445_);
lean_dec(v___y_6441_);
lean_dec_ref(v___y_6440_);
lean_dec_ref(v___y_6438_);
lean_dec(v___y_6435_);
lean_dec_ref(v___y_6434_);
lean_dec_ref(v___y_6432_);
lean_dec_ref(v___y_6431_);
lean_dec(v___y_6428_);
lean_dec_ref(v___y_6427_);
lean_dec_ref(v___y_6426_);
lean_dec(v___y_6425_);
lean_dec(v___y_6424_);
lean_dec_ref(v___y_6423_);
lean_dec_ref(v___y_6422_);
lean_dec_ref(v___y_6421_);
lean_dec_ref(v___y_6420_);
lean_dec(v___y_6419_);
lean_dec_ref(v___y_6417_);
lean_dec(v___y_6416_);
lean_dec_ref(v___y_6415_);
lean_dec(v___y_6414_);
lean_dec(v___y_6413_);
v_a_6518_ = lean_ctor_get(v___x_6458_, 0);
v_isSharedCheck_6525_ = !lean_is_exclusive(v___x_6458_);
if (v_isSharedCheck_6525_ == 0)
{
v___x_6520_ = v___x_6458_;
v_isShared_6521_ = v_isSharedCheck_6525_;
goto v_resetjp_6519_;
}
else
{
lean_inc(v_a_6518_);
lean_dec(v___x_6458_);
v___x_6520_ = lean_box(0);
v_isShared_6521_ = v_isSharedCheck_6525_;
goto v_resetjp_6519_;
}
v_resetjp_6519_:
{
lean_object* v___x_6523_; 
if (v_isShared_6521_ == 0)
{
v___x_6523_ = v___x_6520_;
goto v_reusejp_6522_;
}
else
{
lean_object* v_reuseFailAlloc_6524_; 
v_reuseFailAlloc_6524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6524_, 0, v_a_6518_);
v___x_6523_ = v_reuseFailAlloc_6524_;
goto v_reusejp_6522_;
}
v_reusejp_6522_:
{
return v___x_6523_;
}
}
}
}
else
{
lean_object* v_a_6526_; lean_object* v___x_6528_; uint8_t v_isShared_6529_; uint8_t v_isSharedCheck_6533_; 
lean_dec(v___y_6451_);
lean_dec_ref(v___y_6449_);
lean_dec(v___y_6448_);
lean_dec(v___y_6446_);
lean_dec(v___y_6445_);
lean_dec(v___y_6441_);
lean_dec_ref(v___y_6440_);
lean_dec_ref(v___y_6438_);
lean_dec(v___y_6435_);
lean_dec_ref(v___y_6434_);
lean_dec_ref(v___y_6432_);
lean_dec_ref(v___y_6431_);
lean_dec(v___y_6428_);
lean_dec_ref(v___y_6427_);
lean_dec_ref(v___y_6426_);
lean_dec(v___y_6425_);
lean_dec(v___y_6424_);
lean_dec_ref(v___y_6423_);
lean_dec_ref(v___y_6422_);
lean_dec_ref(v___y_6421_);
lean_dec_ref(v___y_6420_);
lean_dec(v___y_6419_);
lean_dec_ref(v___y_6417_);
lean_dec(v___y_6416_);
lean_dec_ref(v___y_6415_);
lean_dec(v___y_6414_);
lean_dec(v___y_6413_);
v_a_6526_ = lean_ctor_get(v___x_6453_, 0);
v_isSharedCheck_6533_ = !lean_is_exclusive(v___x_6453_);
if (v_isSharedCheck_6533_ == 0)
{
v___x_6528_ = v___x_6453_;
v_isShared_6529_ = v_isSharedCheck_6533_;
goto v_resetjp_6527_;
}
else
{
lean_inc(v_a_6526_);
lean_dec(v___x_6453_);
v___x_6528_ = lean_box(0);
v_isShared_6529_ = v_isSharedCheck_6533_;
goto v_resetjp_6527_;
}
v_resetjp_6527_:
{
lean_object* v___x_6531_; 
if (v_isShared_6529_ == 0)
{
v___x_6531_ = v___x_6528_;
goto v_reusejp_6530_;
}
else
{
lean_object* v_reuseFailAlloc_6532_; 
v_reuseFailAlloc_6532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6532_, 0, v_a_6526_);
v___x_6531_ = v_reuseFailAlloc_6532_;
goto v_reusejp_6530_;
}
v_reusejp_6530_:
{
return v___x_6531_;
}
}
}
}
v___jp_6534_:
{
uint8_t v_returnsEarly_6573_; lean_object* v___x_6574_; lean_object* v___x_6575_; lean_object* v___f_6576_; 
v_returnsEarly_6573_ = lean_ctor_get_uint8(v___y_6570_, sizeof(void*)*2 + 2);
lean_dec_ref(v___y_6570_);
v___x_6574_ = lean_box(v_returnsEarly_6573_);
v___x_6575_ = lean_box(v___y_6548_);
lean_inc_ref(v___y_6542_);
lean_inc_ref(v___y_6540_);
lean_inc_ref(v___y_6572_);
v___f_6576_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___lam__1___boxed), 14, 6);
lean_closure_set(v___f_6576_, 0, v___y_6572_);
lean_closure_set(v___f_6576_, 1, v___y_6540_);
lean_closure_set(v___f_6576_, 2, v___x_6574_);
lean_closure_set(v___f_6576_, 3, v___x_6156_);
lean_closure_set(v___f_6576_, 4, v___y_6542_);
lean_closure_set(v___f_6576_, 5, v___x_6575_);
if (v_returnsEarly_6573_ == 0)
{
size_t v_sz_6577_; size_t v___x_6578_; lean_object* v___x_6579_; lean_object* v___x_6580_; 
lean_dec(v___y_6551_);
v_sz_6577_ = lean_array_size(v___y_6572_);
v___x_6578_ = ((size_t)0ULL);
lean_inc_ref_n(v___y_6572_, 2);
v___x_6579_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__5(v_sz_6577_, v___x_6578_, v___y_6572_);
v___x_6580_ = lean_array_to_list(v___x_6579_);
v___y_6413_ = v___y_6535_;
v___y_6414_ = v___y_6536_;
v___y_6415_ = v___y_6537_;
v___y_6416_ = v___y_6538_;
v___y_6417_ = v___y_6539_;
v___y_6418_ = v_returnsEarly_6573_;
v___y_6419_ = v___y_6541_;
v___y_6420_ = v___y_6542_;
v___y_6421_ = v___y_6544_;
v___y_6422_ = v___f_6576_;
v___y_6423_ = v___y_6545_;
v___y_6424_ = v___y_6546_;
v___y_6425_ = v___y_6547_;
v___y_6426_ = v___y_6572_;
v___y_6427_ = v___y_6550_;
v___y_6428_ = v___y_6553_;
v___y_6429_ = v___y_6552_;
v___y_6430_ = v___y_6554_;
v___y_6431_ = v___y_6555_;
v___y_6432_ = v___y_6543_;
v___y_6433_ = v___y_6556_;
v___y_6434_ = v___y_6557_;
v___y_6435_ = v___y_6558_;
v___y_6436_ = v___y_6559_;
v___y_6437_ = v___y_6560_;
v___y_6438_ = v___y_6549_;
v___y_6439_ = v___y_6561_;
v___y_6440_ = v___y_6562_;
v___y_6441_ = v___y_6563_;
v___y_6442_ = v___y_6564_;
v___y_6443_ = v___y_6565_;
v___y_6444_ = v___y_6540_;
v___y_6445_ = v___y_6566_;
v___y_6446_ = v___y_6567_;
v___y_6447_ = v___y_6568_;
v___y_6448_ = v___y_6569_;
v___y_6449_ = v___y_6572_;
v___y_6450_ = v___y_6571_;
v___y_6451_ = v___x_6580_;
goto v___jp_6412_;
}
else
{
size_t v_sz_6581_; size_t v___x_6582_; lean_object* v___x_6583_; lean_object* v___x_6584_; lean_object* v___x_6585_; 
v_sz_6581_ = lean_array_size(v___y_6572_);
v___x_6582_ = ((size_t)0ULL);
lean_inc_ref_n(v___y_6572_, 2);
v___x_6583_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__5(v_sz_6581_, v___x_6582_, v___y_6572_);
v___x_6584_ = lean_array_to_list(v___x_6583_);
v___x_6585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6585_, 0, v___y_6551_);
lean_ctor_set(v___x_6585_, 1, v___x_6584_);
v___y_6413_ = v___y_6535_;
v___y_6414_ = v___y_6536_;
v___y_6415_ = v___y_6537_;
v___y_6416_ = v___y_6538_;
v___y_6417_ = v___y_6539_;
v___y_6418_ = v_returnsEarly_6573_;
v___y_6419_ = v___y_6541_;
v___y_6420_ = v___y_6542_;
v___y_6421_ = v___y_6544_;
v___y_6422_ = v___f_6576_;
v___y_6423_ = v___y_6545_;
v___y_6424_ = v___y_6546_;
v___y_6425_ = v___y_6547_;
v___y_6426_ = v___y_6572_;
v___y_6427_ = v___y_6550_;
v___y_6428_ = v___y_6553_;
v___y_6429_ = v___y_6552_;
v___y_6430_ = v___y_6554_;
v___y_6431_ = v___y_6555_;
v___y_6432_ = v___y_6543_;
v___y_6433_ = v___y_6556_;
v___y_6434_ = v___y_6557_;
v___y_6435_ = v___y_6558_;
v___y_6436_ = v___y_6559_;
v___y_6437_ = v___y_6560_;
v___y_6438_ = v___y_6549_;
v___y_6439_ = v___y_6561_;
v___y_6440_ = v___y_6562_;
v___y_6441_ = v___y_6563_;
v___y_6442_ = v___y_6564_;
v___y_6443_ = v___y_6565_;
v___y_6444_ = v___y_6540_;
v___y_6445_ = v___y_6566_;
v___y_6446_ = v___y_6567_;
v___y_6447_ = v___y_6568_;
v___y_6448_ = v___y_6569_;
v___y_6449_ = v___y_6572_;
v___y_6450_ = v___y_6571_;
v___y_6451_ = v___x_6585_;
goto v___jp_6412_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoFor___boxed(lean_object* v_stx_6849_, lean_object* v_dec_6850_, lean_object* v_a_6851_, lean_object* v_a_6852_, lean_object* v_a_6853_, lean_object* v_a_6854_, lean_object* v_a_6855_, lean_object* v_a_6856_, lean_object* v_a_6857_, lean_object* v_a_6858_){
_start:
{
lean_object* v_res_6859_; 
v_res_6859_ = l_Lean_Elab_Do_elabDoFor(v_stx_6849_, v_dec_6850_, v_a_6851_, v_a_6852_, v_a_6853_, v_a_6854_, v_a_6855_, v_a_6856_, v_a_6857_);
lean_dec(v_a_6857_);
lean_dec_ref(v_a_6856_);
lean_dec(v_a_6855_);
lean_dec_ref(v_a_6854_);
lean_dec(v_a_6853_);
lean_dec_ref(v_a_6852_);
lean_dec_ref(v_a_6851_);
return v_res_6859_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1(lean_object* v_00_u03b1_6860_, lean_object* v_msg_6861_, lean_object* v___y_6862_, lean_object* v___y_6863_, lean_object* v___y_6864_, lean_object* v___y_6865_, lean_object* v___y_6866_, lean_object* v___y_6867_){
_start:
{
lean_object* v___x_6869_; 
v___x_6869_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___redArg(v_msg_6861_, v___y_6862_, v___y_6863_, v___y_6864_, v___y_6865_, v___y_6866_, v___y_6867_);
return v___x_6869_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1___boxed(lean_object* v_00_u03b1_6870_, lean_object* v_msg_6871_, lean_object* v___y_6872_, lean_object* v___y_6873_, lean_object* v___y_6874_, lean_object* v___y_6875_, lean_object* v___y_6876_, lean_object* v___y_6877_, lean_object* v___y_6878_){
_start:
{
lean_object* v_res_6879_; 
v_res_6879_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1(v_00_u03b1_6870_, v_msg_6871_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_, v___y_6877_);
lean_dec(v___y_6877_);
lean_dec_ref(v___y_6876_);
lean_dec(v___y_6875_);
lean_dec_ref(v___y_6874_);
lean_dec(v___y_6873_);
lean_dec_ref(v___y_6872_);
return v_res_6879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2(lean_object* v_00_u03b1_6880_, lean_object* v_name_6881_, lean_object* v_type_6882_, lean_object* v_k_6883_, lean_object* v___y_6884_, lean_object* v___y_6885_, lean_object* v___y_6886_, lean_object* v___y_6887_, lean_object* v___y_6888_, lean_object* v___y_6889_, lean_object* v___y_6890_){
_start:
{
lean_object* v___x_6892_; 
v___x_6892_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(v_name_6881_, v_type_6882_, v_k_6883_, v___y_6884_, v___y_6885_, v___y_6886_, v___y_6887_, v___y_6888_, v___y_6889_, v___y_6890_);
return v___x_6892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2___boxed(lean_object* v_00_u03b1_6893_, lean_object* v_name_6894_, lean_object* v_type_6895_, lean_object* v_k_6896_, lean_object* v___y_6897_, lean_object* v___y_6898_, lean_object* v___y_6899_, lean_object* v___y_6900_, lean_object* v___y_6901_, lean_object* v___y_6902_, lean_object* v___y_6903_, lean_object* v___y_6904_){
_start:
{
lean_object* v_res_6905_; 
v_res_6905_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__2(v_00_u03b1_6893_, v_name_6894_, v_type_6895_, v_k_6896_, v___y_6897_, v___y_6898_, v___y_6899_, v___y_6900_, v___y_6901_, v___y_6902_, v___y_6903_);
lean_dec(v___y_6903_);
lean_dec_ref(v___y_6902_);
lean_dec(v___y_6901_);
lean_dec_ref(v___y_6900_);
lean_dec(v___y_6899_);
lean_dec_ref(v___y_6898_);
lean_dec_ref(v___y_6897_);
return v_res_6905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1(lean_object* v_msgData_6906_, lean_object* v_macroStack_6907_, lean_object* v___y_6908_, lean_object* v___y_6909_, lean_object* v___y_6910_, lean_object* v___y_6911_, lean_object* v___y_6912_, lean_object* v___y_6913_){
_start:
{
lean_object* v___x_6915_; 
v___x_6915_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___redArg(v_msgData_6906_, v_macroStack_6907_, v___y_6912_);
return v___x_6915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1___boxed(lean_object* v_msgData_6916_, lean_object* v_macroStack_6917_, lean_object* v___y_6918_, lean_object* v___y_6919_, lean_object* v___y_6920_, lean_object* v___y_6921_, lean_object* v___y_6922_, lean_object* v___y_6923_, lean_object* v___y_6924_){
_start:
{
lean_object* v_res_6925_; 
v_res_6925_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__1_spec__1(v_msgData_6916_, v_macroStack_6917_, v___y_6918_, v___y_6919_, v___y_6920_, v___y_6921_, v___y_6922_, v___y_6923_);
lean_dec(v___y_6923_);
lean_dec_ref(v___y_6922_);
lean_dec(v___y_6921_);
lean_dec_ref(v___y_6920_);
lean_dec(v___y_6919_);
lean_dec_ref(v___y_6918_);
return v_res_6925_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14(lean_object* v_ref_6926_, lean_object* v_msgData_6927_, uint8_t v_severity_6928_, uint8_t v_isSilent_6929_, lean_object* v___y_6930_, lean_object* v___y_6931_, lean_object* v___y_6932_, lean_object* v___y_6933_, lean_object* v___y_6934_, lean_object* v___y_6935_, lean_object* v___y_6936_){
_start:
{
lean_object* v___x_6938_; 
v___x_6938_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___redArg(v_ref_6926_, v_msgData_6927_, v_severity_6928_, v_isSilent_6929_, v___y_6933_, v___y_6934_, v___y_6935_, v___y_6936_);
return v___x_6938_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14___boxed(lean_object* v_ref_6939_, lean_object* v_msgData_6940_, lean_object* v_severity_6941_, lean_object* v_isSilent_6942_, lean_object* v___y_6943_, lean_object* v___y_6944_, lean_object* v___y_6945_, lean_object* v___y_6946_, lean_object* v___y_6947_, lean_object* v___y_6948_, lean_object* v___y_6949_, lean_object* v___y_6950_){
_start:
{
uint8_t v_severity_boxed_6951_; uint8_t v_isSilent_boxed_6952_; lean_object* v_res_6953_; 
v_severity_boxed_6951_ = lean_unbox(v_severity_6941_);
v_isSilent_boxed_6952_ = lean_unbox(v_isSilent_6942_);
v_res_6953_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_Do_warnIntrinsicExperimental___at___00Lean_Elab_Do_elabDoFor_spec__7_spec__11_spec__14(v_ref_6939_, v_msgData_6940_, v_severity_boxed_6951_, v_isSilent_boxed_6952_, v___y_6943_, v___y_6944_, v___y_6945_, v___y_6946_, v___y_6947_, v___y_6948_, v___y_6949_);
lean_dec(v___y_6949_);
lean_dec_ref(v___y_6948_);
lean_dec(v___y_6947_);
lean_dec_ref(v___y_6946_);
lean_dec(v___y_6945_);
lean_dec_ref(v___y_6944_);
lean_dec_ref(v___y_6943_);
lean_dec(v_ref_6939_);
return v_res_6953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1(){
_start:
{
lean_object* v___x_6961_; lean_object* v___x_6962_; lean_object* v___x_6963_; lean_object* v___x_6964_; lean_object* v___x_6965_; 
v___x_6961_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_6962_ = ((lean_object*)(l_Lean_Elab_Do_expandDoFor___closed__1));
v___x_6963_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1));
v___x_6964_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoFor___boxed), 10, 0);
v___x_6965_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6961_, v___x_6962_, v___x_6963_, v___x_6964_);
return v___x_6965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___boxed(lean_object* v_a_6966_){
_start:
{
lean_object* v_res_6967_; 
v_res_6967_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1();
return v_res_6967_;
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
lean_object* runtime_initialize_Std_WP_Gadget_ForIn(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_BuiltinDo_For(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_WP_Gadget_ForIn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_BuiltinDo_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Do(uint8_t builtin);
lean_object* initialize_Std_WP_Gadget_ForIn(uint8_t builtin);
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
res = initialize_Std_WP_Gadget_ForIn(builtin);
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
