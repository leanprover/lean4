// Lean compiler output
// Module: Lean.Elab.BuiltinDo.Forward
// Imports: public import Lean.Elab.Do.Basic meta import Lean.Parser.Do import Lean.Elab.Do.Control import Lean.Elab.Do.InferControlInfo import Lean.Elab.Binders
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
lean_object* l_Lean_Elab_Term_elabFunBinders___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_FindMVar_main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Elab_Do_EffectForwarder_lift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Do_elabDoSeq(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_Forward_matchApp_x3f(lean_object*);
lean_object* l_Lean_Core_withFreshMacroScope___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_EffectForwarder_ofCont(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_EffectForwarder_restoreCont(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_mkBindUnlessPure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_checked_assign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandFunBinders___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_elabDoForward___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 136, .m_capacity = 136, .m_length = 133, .m_data = "`do←` may only appear as the last argument of a function application inside an enclosing `do` block, optionally inside a `fun` binder"};
static const lean_object* l_Lean_Elab_Do_elabDoForward___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Do_elabDoForward___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Do_elabDoForward___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_elabDoForward___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoForward___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoForward___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoForward(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoForward___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doForward"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(207, 164, 175, 48, 233, 61, 15, 76)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__4_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__6_value;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "elabDoForward"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(86, 191, 102, 116, 164, 35, 128, 94)}};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 32, .m_data = "` is not a valid `do←` wrapper: "};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__3;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 148, .m_data = ". The wrapper must have type `(… → m α) → m α` for some `α` that is universally quantified in the wrapper's signature and does not appear elsewhere."};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 48, .m_data = "`α` appears in the forwarded body's input type `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 62, .m_data = "the forwarded body's `α` differs from the wrapper's return `α`"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 53, .m_data = "`α` appears in an applied explicit argument of type `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 43, .m_data = "its return type pins `α` to a concrete type"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__0 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__1;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "its return type `"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__2 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__3;
static const lean_string_object l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 26, .m_data = "` is not of the form `m α`"};
static const lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__4 = (const lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "syntheticHole"};
static const lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(218, 189, 67, 60, 211, 196, 112, 165)}};
static const lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "forwarded"};
static const lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__4;
static const lean_ctor_object l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(125, 152, 115, 51, 73, 98, 174, 67)}};
static const lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__5_value;
static const lean_string_object l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__7_value;
static const lean_string_object l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__9 = (const lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__0;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__1;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__4;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__5_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__5_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__6 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__6_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__8;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__10;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__11;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__12 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__12_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__12_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__17_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__18;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__21_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__22 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__22_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "the lifted body's type does not match the wrapper's body slot type"};
static const lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__1;
static const lean_string_object l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__2 = (const lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__3 = (const lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__4 = (const lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__4_value;
static const lean_string_object l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 84, .m_capacity = 84, .m_length = 81, .m_data = "A `do←` binder must be a variable. Bind a variable and `match` on it in the body."};
static const lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__5 = (const lean_object*)&l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__2(lean_object* v_opts_1_, lean_object* v_opt_2_){
_start:
{
lean_object* v_name_3_; lean_object* v_defValue_4_; lean_object* v_map_5_; lean_object* v___x_6_; 
v_name_3_ = lean_ctor_get(v_opt_2_, 0);
v_defValue_4_ = lean_ctor_get(v_opt_2_, 1);
v_map_5_ = lean_ctor_get(v_opts_1_, 0);
v___x_6_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5_, v_name_3_);
if (lean_obj_tag(v___x_6_) == 0)
{
uint8_t v___x_7_; 
v___x_7_ = lean_unbox(v_defValue_4_);
return v___x_7_;
}
else
{
lean_object* v_val_8_; 
v_val_8_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_val_8_);
lean_dec_ref_known(v___x_6_, 1);
if (lean_obj_tag(v_val_8_) == 1)
{
uint8_t v_v_9_; 
v_v_9_ = lean_ctor_get_uint8(v_val_8_, 0);
lean_dec_ref_known(v_val_8_, 0);
return v_v_9_;
}
else
{
uint8_t v___x_10_; 
lean_dec(v_val_8_);
v___x_10_ = lean_unbox(v_defValue_4_);
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__2___boxed(lean_object* v_opts_11_, lean_object* v_opt_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__2(v_opts_11_, v_opt_12_);
lean_dec_ref(v_opt_12_);
lean_dec_ref(v_opts_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_box(1);
v___x_16_ = l_Lean_MessageData_ofFormat(v___x_15_);
return v___x_16_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__2));
v___x_21_ = l_Lean_MessageData_ofFormat(v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3(lean_object* v_x_22_, lean_object* v_x_23_){
_start:
{
if (lean_obj_tag(v_x_23_) == 0)
{
return v_x_22_;
}
else
{
lean_object* v_head_24_; lean_object* v_tail_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_47_; 
v_head_24_ = lean_ctor_get(v_x_23_, 0);
v_tail_25_ = lean_ctor_get(v_x_23_, 1);
v_isSharedCheck_47_ = !lean_is_exclusive(v_x_23_);
if (v_isSharedCheck_47_ == 0)
{
v___x_27_ = v_x_23_;
v_isShared_28_ = v_isSharedCheck_47_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_tail_25_);
lean_inc(v_head_24_);
lean_dec(v_x_23_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_47_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v_before_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_45_; 
v_before_29_ = lean_ctor_get(v_head_24_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v_head_24_);
if (v_isSharedCheck_45_ == 0)
{
lean_object* v_unused_46_; 
v_unused_46_ = lean_ctor_get(v_head_24_, 1);
lean_dec(v_unused_46_);
v___x_31_ = v_head_24_;
v_isShared_32_ = v_isSharedCheck_45_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_before_29_);
lean_dec(v_head_24_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_45_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v___x_33_; lean_object* v___x_35_; 
v___x_33_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_32_ == 0)
{
lean_ctor_set_tag(v___x_31_, 7);
lean_ctor_set(v___x_31_, 1, v___x_33_);
lean_ctor_set(v___x_31_, 0, v_x_22_);
v___x_35_ = v___x_31_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_x_22_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v___x_33_);
v___x_35_ = v_reuseFailAlloc_44_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
lean_object* v___x_36_; lean_object* v___x_38_; 
v___x_36_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__3);
if (v_isShared_28_ == 0)
{
lean_ctor_set_tag(v___x_27_, 7);
lean_ctor_set(v___x_27_, 1, v___x_36_);
lean_ctor_set(v___x_27_, 0, v___x_35_);
v___x_38_ = v___x_27_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v___x_35_);
lean_ctor_set(v_reuseFailAlloc_43_, 1, v___x_36_);
v___x_38_ = v_reuseFailAlloc_43_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_39_ = l_Lean_MessageData_ofSyntax(v_before_29_);
v___x_40_ = l_Lean_indentD(v___x_39_);
v___x_41_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_41_, 0, v___x_38_);
lean_ctor_set(v___x_41_, 1, v___x_40_);
v_x_22_ = v___x_41_;
v_x_23_ = v_tail_25_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___closed__1));
v___x_52_ = l_Lean_MessageData_ofFormat(v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg(lean_object* v_msgData_53_, lean_object* v_macroStack_54_, lean_object* v___y_55_){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; uint8_t v___x_59_; 
v___x_57_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_55_);
v___x_58_ = l_Lean_Elab_pp_macroStack;
v___x_59_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__2(v___x_57_, v___x_58_);
lean_dec_ref(v___x_57_);
if (v___x_59_ == 0)
{
lean_object* v___x_60_; 
lean_dec(v_macroStack_54_);
v___x_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_60_, 0, v_msgData_53_);
return v___x_60_;
}
else
{
if (lean_obj_tag(v_macroStack_54_) == 0)
{
lean_object* v___x_61_; 
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v_msgData_53_);
return v___x_61_;
}
else
{
lean_object* v_head_62_; lean_object* v_after_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_78_; 
v_head_62_ = lean_ctor_get(v_macroStack_54_, 0);
lean_inc(v_head_62_);
v_after_63_ = lean_ctor_get(v_head_62_, 1);
v_isSharedCheck_78_ = !lean_is_exclusive(v_head_62_);
if (v_isSharedCheck_78_ == 0)
{
lean_object* v_unused_79_; 
v_unused_79_ = lean_ctor_get(v_head_62_, 0);
lean_dec(v_unused_79_);
v___x_65_ = v_head_62_;
v_isShared_66_ = v_isSharedCheck_78_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_after_63_);
lean_dec(v_head_62_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_78_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_67_; lean_object* v___x_69_; 
v___x_67_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_66_ == 0)
{
lean_ctor_set_tag(v___x_65_, 7);
lean_ctor_set(v___x_65_, 1, v___x_67_);
lean_ctor_set(v___x_65_, 0, v_msgData_53_);
v___x_69_ = v___x_65_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_msgData_53_);
lean_ctor_set(v_reuseFailAlloc_77_, 1, v___x_67_);
v___x_69_ = v_reuseFailAlloc_77_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v_msgData_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_70_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___closed__2);
v___x_71_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_69_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
v___x_72_ = l_Lean_MessageData_ofSyntax(v_after_63_);
v___x_73_ = l_Lean_indentD(v___x_72_);
v_msgData_74_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_74_, 0, v___x_71_);
lean_ctor_set(v_msgData_74_, 1, v___x_73_);
v___x_75_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3(v_msgData_74_, v_macroStack_54_);
v___x_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
return v___x_76_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_80_, lean_object* v_macroStack_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg(v_msgData_80_, v_macroStack_81_, v___y_82_);
lean_dec_ref(v___y_82_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0(lean_object* v_msgData_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v___x_91_; lean_object* v_env_92_; lean_object* v___x_93_; lean_object* v_toCold_94_; lean_object* v_mctx_95_; lean_object* v_lctx_96_; lean_object* v_options_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_91_ = lean_st_ref_get(v___y_89_);
v_env_92_ = lean_ctor_get(v___x_91_, 0);
lean_inc_ref(v_env_92_);
lean_dec(v___x_91_);
v___x_93_ = lean_st_ref_get(v___y_87_);
v_toCold_94_ = lean_ctor_get(v___y_88_, 0);
v_mctx_95_ = lean_ctor_get(v___x_93_, 0);
lean_inc_ref(v_mctx_95_);
lean_dec(v___x_93_);
v_lctx_96_ = lean_ctor_get(v___y_86_, 2);
v_options_97_ = lean_ctor_get(v_toCold_94_, 2);
lean_inc_ref(v_options_97_);
lean_inc_ref(v_lctx_96_);
v___x_98_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_98_, 0, v_env_92_);
lean_ctor_set(v___x_98_, 1, v_mctx_95_);
lean_ctor_set(v___x_98_, 2, v_lctx_96_);
lean_ctor_set(v___x_98_, 3, v_options_97_);
v___x_99_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set(v___x_99_, 1, v_msgData_85_);
v___x_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0___boxed(lean_object* v_msgData_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0(v_msgData_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg(lean_object* v_msg_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v_ref_116_; lean_object* v_macroStack_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v_a_120_; lean_object* v___x_121_; lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_130_; 
v_ref_116_ = lean_ctor_get(v___y_113_, 2);
v_macroStack_117_ = lean_ctor_get(v___y_109_, 1);
v___x_118_ = l_Lean_Elab_getBetterRef(v_ref_116_, v_macroStack_117_);
v___x_119_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0(v_msg_108_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
v_a_120_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_a_120_);
lean_dec_ref(v___x_119_);
lean_inc(v_macroStack_117_);
v___x_121_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg(v_a_120_, v_macroStack_117_, v___y_113_);
v_a_122_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_130_ == 0)
{
v___x_124_ = v___x_121_;
v_isShared_125_ = v_isSharedCheck_130_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v___x_121_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_130_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_126_; lean_object* v___x_128_; 
v___x_126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_118_);
lean_ctor_set(v___x_126_, 1, v_a_122_);
if (v_isShared_125_ == 0)
{
lean_ctor_set_tag(v___x_124_, 1);
lean_ctor_set(v___x_124_, 0, v___x_126_);
v___x_128_ = v___x_124_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_126_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg___boxed(lean_object* v_msg_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg(v_msg_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
return v_res_139_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoForward___redArg___closed__1(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = ((lean_object*)(l_Lean_Elab_Do_elabDoForward___redArg___closed__0));
v___x_142_ = l_Lean_stringToMessageData(v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoForward___redArg(lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lean_obj_once(&l_Lean_Elab_Do_elabDoForward___redArg___closed__1, &l_Lean_Elab_Do_elabDoForward___redArg___closed__1_once, _init_l_Lean_Elab_Do_elabDoForward___redArg___closed__1);
v___x_151_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg(v___x_150_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoForward___redArg___boxed(lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_Elab_Do_elabDoForward___redArg(v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_);
lean_dec(v_a_157_);
lean_dec_ref(v_a_156_);
lean_dec(v_a_155_);
lean_dec_ref(v_a_154_);
lean_dec(v_a_153_);
lean_dec_ref(v_a_152_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoForward(lean_object* v_x_160_, lean_object* v_x_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Lean_Elab_Do_elabDoForward___redArg(v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoForward___boxed(lean_object* v_x_170_, lean_object* v_x_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_Elab_Do_elabDoForward(v_x_170_, v_x_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_);
lean_dec(v_a_177_);
lean_dec_ref(v_a_176_);
lean_dec(v_a_175_);
lean_dec_ref(v_a_174_);
lean_dec(v_a_173_);
lean_dec_ref(v_a_172_);
lean_dec(v_x_171_);
lean_dec(v_x_170_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0(lean_object* v_00_u03b1_180_, lean_object* v_msg_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg(v_msg_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___boxed(lean_object* v_00_u03b1_190_, lean_object* v_msg_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0(v_00_u03b1_190_, v_msg_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1(lean_object* v_msgData_200_, lean_object* v_macroStack_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg(v_msgData_200_, v_macroStack_201_, v___y_206_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___boxed(lean_object* v_msgData_210_, lean_object* v_macroStack_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1(v_msgData_210_, v_macroStack_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1(){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_238_ = l_Lean_Elab_Term_termElabAttribute;
v___x_239_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__4));
v___x_240_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__8));
v___x_241_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoForward___boxed), 9, 0);
v___x_242_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_238_, v___x_239_, v___x_240_, v___x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___boxed(lean_object* v_a_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1();
return v_res_244_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__0));
v___x_247_ = l_Lean_stringToMessageData(v___x_246_);
return v___x_247_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__3(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__2));
v___x_250_ = l_Lean_stringToMessageData(v___x_249_);
return v___x_250_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__5(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__4));
v___x_253_ = l_Lean_stringToMessageData(v___x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint(lean_object* v_headApp_254_, lean_object* v_reason_255_){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_256_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1);
v___x_257_ = l_Lean_MessageData_ofSyntax(v_headApp_254_);
v___x_258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_256_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__3, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__3);
v___x_260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_258_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
v___x_261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v_reason_255_);
v___x_262_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__5, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__5_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__5);
v___x_263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_261_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(lean_object* v_e_264_, lean_object* v___y_265_){
_start:
{
uint8_t v___x_267_; 
v___x_267_ = l_Lean_Expr_hasMVar(v_e_264_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; 
v___x_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_268_, 0, v_e_264_);
return v___x_268_;
}
else
{
lean_object* v___x_269_; lean_object* v_mctx_270_; lean_object* v___x_271_; lean_object* v_fst_272_; lean_object* v_snd_273_; lean_object* v___x_274_; lean_object* v_cache_275_; lean_object* v_zetaDeltaFVarIds_276_; lean_object* v_postponed_277_; lean_object* v_diag_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_287_; 
v___x_269_ = lean_st_ref_get(v___y_265_);
v_mctx_270_ = lean_ctor_get(v___x_269_, 0);
lean_inc_ref(v_mctx_270_);
lean_dec(v___x_269_);
v___x_271_ = l_Lean_instantiateMVarsCore(v_mctx_270_, v_e_264_);
v_fst_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_fst_272_);
v_snd_273_ = lean_ctor_get(v___x_271_, 1);
lean_inc(v_snd_273_);
lean_dec_ref(v___x_271_);
v___x_274_ = lean_st_ref_take(v___y_265_);
v_cache_275_ = lean_ctor_get(v___x_274_, 1);
v_zetaDeltaFVarIds_276_ = lean_ctor_get(v___x_274_, 2);
v_postponed_277_ = lean_ctor_get(v___x_274_, 3);
v_diag_278_ = lean_ctor_get(v___x_274_, 4);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_274_);
if (v_isSharedCheck_287_ == 0)
{
lean_object* v_unused_288_; 
v_unused_288_ = lean_ctor_get(v___x_274_, 0);
lean_dec(v_unused_288_);
v___x_280_ = v___x_274_;
v_isShared_281_ = v_isSharedCheck_287_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_diag_278_);
lean_inc(v_postponed_277_);
lean_inc(v_zetaDeltaFVarIds_276_);
lean_inc(v_cache_275_);
lean_dec(v___x_274_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_287_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v_snd_273_);
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_snd_273_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_cache_275_);
lean_ctor_set(v_reuseFailAlloc_286_, 2, v_zetaDeltaFVarIds_276_);
lean_ctor_set(v_reuseFailAlloc_286_, 3, v_postponed_277_);
lean_ctor_set(v_reuseFailAlloc_286_, 4, v_diag_278_);
v___x_283_ = v_reuseFailAlloc_286_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_st_ref_put(v___y_265_, v___x_283_);
v___x_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_285_, 0, v_fst_272_);
return v___x_285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg___boxed(lean_object* v_e_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_e_289_, v___y_290_);
lean_dec(v___y_290_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1(lean_object* v_e_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_e_293_, v___y_295_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___boxed(lean_object* v_e_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1(v_e_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___lam__0(lean_object* v_k_307_, lean_object* v_b_308_, lean_object* v_c_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v___x_315_; 
lean_inc(v___y_313_);
lean_inc_ref(v___y_312_);
lean_inc(v___y_311_);
lean_inc_ref(v___y_310_);
v___x_315_ = lean_apply_7(v_k_307_, v_b_308_, v_c_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, lean_box(0));
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___lam__0___boxed(lean_object* v_k_316_, lean_object* v_b_317_, lean_object* v_c_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___lam__0(v_k_316_, v_b_317_, v_c_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg(lean_object* v_type_325_, lean_object* v_k_326_, uint8_t v_cleanupAnnotations_327_, uint8_t v_whnfType_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v___f_334_; lean_object* v___x_335_; 
v___f_334_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_334_, 0, v_k_326_);
v___x_335_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_325_, v___f_334_, v_cleanupAnnotations_327_, v_whnfType_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_343_; 
v_a_336_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_343_ == 0)
{
v___x_338_ = v___x_335_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_335_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_a_336_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
v_a_344_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_335_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_335_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___boxed(lean_object* v_type_352_, lean_object* v_k_353_, lean_object* v_cleanupAnnotations_354_, lean_object* v_whnfType_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_361_; uint8_t v_whnfType_boxed_362_; lean_object* v_res_363_; 
v_cleanupAnnotations_boxed_361_ = lean_unbox(v_cleanupAnnotations_354_);
v_whnfType_boxed_362_ = lean_unbox(v_whnfType_355_);
v_res_363_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg(v_type_352_, v_k_353_, v_cleanupAnnotations_boxed_361_, v_whnfType_boxed_362_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4(lean_object* v_00_u03b1_364_, lean_object* v_type_365_, lean_object* v_k_366_, uint8_t v_cleanupAnnotations_367_, uint8_t v_whnfType_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg(v_type_365_, v_k_366_, v_cleanupAnnotations_367_, v_whnfType_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___boxed(lean_object* v_00_u03b1_375_, lean_object* v_type_376_, lean_object* v_k_377_, lean_object* v_cleanupAnnotations_378_, lean_object* v_whnfType_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_385_; uint8_t v_whnfType_boxed_386_; lean_object* v_res_387_; 
v_cleanupAnnotations_boxed_385_ = lean_unbox(v_cleanupAnnotations_378_);
v_whnfType_boxed_386_ = lean_unbox(v_whnfType_379_);
v_res_387_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4(v_00_u03b1_375_, v_type_376_, v_k_377_, v_cleanupAnnotations_boxed_385_, v_whnfType_boxed_386_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(lean_object* v_msg_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v_ref_394_; lean_object* v___x_395_; lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_404_; 
v_ref_394_ = lean_ctor_get(v___y_391_, 2);
v___x_395_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0(v_msg_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
v_a_396_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_404_ == 0)
{
v___x_398_ = v___x_395_;
v_isShared_399_ = v_isSharedCheck_404_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_395_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_404_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_400_; lean_object* v___x_402_; 
lean_inc(v_ref_394_);
v___x_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_400_, 0, v_ref_394_);
lean_ctor_set(v___x_400_, 1, v_a_396_);
if (v_isShared_399_ == 0)
{
lean_ctor_set_tag(v___x_398_, 1);
lean_ctor_set(v___x_398_, 0, v___x_400_);
v___x_402_ = v___x_398_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg___boxed(lean_object* v_msg_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v_msg_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0(lean_object* v_headApp_412_, lean_object* v_00_u03b1_413_, lean_object* v_reason_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint(v_headApp_412_, v_reason_414_);
v___x_421_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v___x_420_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0___boxed(lean_object* v_headApp_422_, lean_object* v_00_u03b1_423_, lean_object* v_reason_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0(v_headApp_422_, v_00_u03b1_423_, v_reason_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
return v_res_430_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0(lean_object* v_arg_431_, lean_object* v_x_432_){
_start:
{
lean_object* v___x_433_; uint8_t v___x_434_; 
v___x_433_ = l_Lean_Expr_mvarId_x21(v_arg_431_);
v___x_434_ = l_Lean_instBEqMVarId_beq(v_x_432_, v___x_433_);
lean_dec(v___x_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0___boxed(lean_object* v_arg_435_, lean_object* v_x_436_){
_start:
{
uint8_t v_res_437_; lean_object* v_r_438_; 
v_res_437_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0(v_arg_435_, v_x_436_);
lean_dec(v_x_436_);
lean_dec_ref(v_arg_435_);
v_r_438_ = lean_box(v_res_437_);
return v_r_438_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__0));
v___x_441_ = l_Lean_stringToMessageData(v___x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4(lean_object* v_arg_442_, lean_object* v_headApp_443_, lean_object* v_as_444_, size_t v_sz_445_, size_t v_i_446_, lean_object* v_b_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v_a_454_; uint8_t v___x_458_; 
v___x_458_ = lean_usize_dec_lt(v_i_446_, v_sz_445_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; 
lean_dec(v_headApp_443_);
lean_dec_ref(v_arg_442_);
v___x_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_459_, 0, v_b_447_);
return v___x_459_;
}
else
{
lean_object* v___f_460_; lean_object* v___x_461_; lean_object* v_a_462_; lean_object* v___x_463_; 
lean_inc_ref(v_arg_442_);
v___f_460_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_460_, 0, v_arg_442_);
v___x_461_ = lean_box(0);
v_a_462_ = lean_array_uget_borrowed(v_as_444_, v_i_446_);
lean_inc(v___y_451_);
lean_inc_ref(v___y_450_);
lean_inc(v___y_449_);
lean_inc_ref(v___y_448_);
lean_inc(v_a_462_);
v___x_463_ = lean_infer_type(v_a_462_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v_a_464_; lean_object* v___x_465_; 
v_a_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc_n(v_a_464_, 2);
lean_dec_ref_known(v___x_463_, 1);
v___x_465_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_a_464_, v___y_449_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v_a_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_a_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_a_466_);
lean_dec_ref_known(v___x_465_, 1);
v___x_467_ = lean_box(0);
v___x_468_ = l_Lean_FindMVar_main(v___f_460_, v_a_466_, v___x_467_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_dec(v_a_464_);
v_a_454_ = v___x_461_;
goto v___jp_453_;
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
lean_dec_ref_known(v___x_468_, 1);
v___x_469_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1);
v___x_470_ = l_Lean_MessageData_ofExpr(v_a_464_);
v___x_471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_469_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
v___x_472_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1);
v___x_473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_471_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
lean_inc(v_headApp_443_);
v___x_474_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint(v_headApp_443_, v___x_473_);
v___x_475_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v___x_474_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_dec_ref_known(v___x_475_, 1);
v_a_454_ = v___x_461_;
goto v___jp_453_;
}
else
{
lean_dec(v_headApp_443_);
lean_dec_ref(v_arg_442_);
return v___x_475_;
}
}
}
else
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
lean_dec(v_a_464_);
lean_dec_ref(v___f_460_);
lean_dec(v_headApp_443_);
lean_dec_ref(v_arg_442_);
v_a_476_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_483_ == 0)
{
v___x_478_ = v___x_465_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_465_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_476_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
else
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
lean_dec_ref(v___f_460_);
lean_dec(v_headApp_443_);
lean_dec_ref(v_arg_442_);
v_a_484_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_463_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_463_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_a_484_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
v___jp_453_:
{
size_t v___x_455_; size_t v___x_456_; 
v___x_455_ = ((size_t)1ULL);
v___x_456_ = lean_usize_add(v_i_446_, v___x_455_);
v_i_446_ = v___x_456_;
v_b_447_ = v_a_454_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___boxed(lean_object* v_arg_492_, lean_object* v_headApp_493_, lean_object* v_as_494_, lean_object* v_sz_495_, lean_object* v_i_496_, lean_object* v_b_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
size_t v_sz_boxed_503_; size_t v_i_boxed_504_; lean_object* v_res_505_; 
v_sz_boxed_503_ = lean_unbox_usize(v_sz_495_);
lean_dec(v_sz_495_);
v_i_boxed_504_ = lean_unbox_usize(v_i_496_);
lean_dec(v_i_496_);
v_res_505_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4(v_arg_492_, v_headApp_493_, v_as_494_, v_sz_boxed_503_, v_i_boxed_504_, v_b_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec_ref(v_as_494_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3(lean_object* v_arg_506_, lean_object* v_headApp_507_, lean_object* v_as_508_, size_t v_sz_509_, size_t v_i_510_, lean_object* v_b_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v_a_518_; uint8_t v___x_522_; 
v___x_522_ = lean_usize_dec_lt(v_i_510_, v_sz_509_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; 
lean_dec(v_headApp_507_);
lean_dec_ref(v_arg_506_);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v_b_511_);
return v___x_523_;
}
else
{
lean_object* v___f_524_; lean_object* v___x_525_; lean_object* v_a_526_; lean_object* v___x_527_; 
lean_inc_ref(v_arg_506_);
v___f_524_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_524_, 0, v_arg_506_);
v___x_525_ = lean_box(0);
v_a_526_ = lean_array_uget_borrowed(v_as_508_, v_i_510_);
lean_inc(v___y_515_);
lean_inc_ref(v___y_514_);
lean_inc(v___y_513_);
lean_inc_ref(v___y_512_);
lean_inc(v_a_526_);
v___x_527_ = lean_infer_type(v_a_526_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_529_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc_n(v_a_528_, 2);
lean_dec_ref_known(v___x_527_, 1);
v___x_529_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_a_528_, v___y_513_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_a_530_);
lean_dec_ref_known(v___x_529_, 1);
v___x_531_ = lean_box(0);
v___x_532_ = l_Lean_FindMVar_main(v___f_524_, v_a_530_, v___x_531_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_dec(v_a_528_);
v_a_518_ = v___x_525_;
goto v___jp_517_;
}
else
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
lean_dec_ref_known(v___x_532_, 1);
v___x_533_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1);
v___x_534_ = l_Lean_MessageData_ofExpr(v_a_528_);
v___x_535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v___x_536_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1);
v___x_537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
lean_inc(v_headApp_507_);
v___x_538_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint(v_headApp_507_, v___x_537_);
v___x_539_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v___x_538_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_dec_ref_known(v___x_539_, 1);
v_a_518_ = v___x_525_;
goto v___jp_517_;
}
else
{
lean_dec(v_headApp_507_);
lean_dec_ref(v_arg_506_);
return v___x_539_;
}
}
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_dec(v_a_528_);
lean_dec_ref(v___f_524_);
lean_dec(v_headApp_507_);
lean_dec_ref(v_arg_506_);
v_a_540_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_529_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_529_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
else
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
lean_dec_ref(v___f_524_);
lean_dec(v_headApp_507_);
lean_dec_ref(v_arg_506_);
v_a_548_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v___x_527_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_527_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_a_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
v___jp_517_:
{
size_t v___x_519_; size_t v___x_520_; lean_object* v___x_521_; 
v___x_519_ = ((size_t)1ULL);
v___x_520_ = lean_usize_add(v_i_510_, v___x_519_);
v___x_521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4(v_arg_506_, v_headApp_507_, v_as_508_, v_sz_509_, v___x_520_, v_a_518_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
return v___x_521_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3___boxed(lean_object* v_arg_556_, lean_object* v_headApp_557_, lean_object* v_as_558_, lean_object* v_sz_559_, lean_object* v_i_560_, lean_object* v_b_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
size_t v_sz_boxed_567_; size_t v_i_boxed_568_; lean_object* v_res_569_; 
v_sz_boxed_567_ = lean_unbox_usize(v_sz_559_);
lean_dec(v_sz_559_);
v_i_boxed_568_ = lean_unbox_usize(v_i_560_);
lean_dec(v_i_560_);
v_res_569_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3(v_arg_556_, v_headApp_557_, v_as_558_, v_sz_boxed_567_, v_i_boxed_568_, v_b_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec_ref(v_as_558_);
return v_res_569_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__1(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__0));
v___x_572_ = l_Lean_stringToMessageData(v___x_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1(lean_object* v_arg_573_, lean_object* v_headApp_574_, lean_object* v_a_575_, lean_object* v_reject_576_, lean_object* v_args_577_, lean_object* v_body_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v___x_597_; lean_object* v_a_598_; lean_object* v___x_599_; 
v___x_597_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_body_578_, v___y_580_);
v_a_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_a_598_);
lean_dec_ref(v___x_597_);
v___x_599_ = l_Lean_Meta_whnfD(v_a_598_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; lean_object* v___x_601_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_a_600_);
lean_dec_ref_known(v___x_599_, 1);
v___x_601_ = l_Lean_Meta_isExprDefEq(v_a_575_, v_a_600_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; uint8_t v___x_603_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_a_602_);
lean_dec_ref_known(v___x_601_, 1);
v___x_603_ = lean_unbox(v_a_602_);
lean_dec(v_a_602_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__1);
lean_inc(v___y_582_);
lean_inc_ref(v___y_581_);
lean_inc(v___y_580_);
lean_inc_ref(v___y_579_);
v___x_605_ = lean_apply_7(v_reject_576_, lean_box(0), v___x_604_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, lean_box(0));
if (lean_obj_tag(v___x_605_) == 0)
{
lean_dec_ref_known(v___x_605_, 1);
goto v___jp_584_;
}
else
{
lean_dec(v_headApp_574_);
lean_dec_ref(v_arg_573_);
return v___x_605_;
}
}
else
{
lean_dec_ref(v_reject_576_);
goto v___jp_584_;
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec_ref(v_reject_576_);
lean_dec(v_headApp_574_);
lean_dec_ref(v_arg_573_);
v_a_606_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_601_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_601_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
else
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
lean_dec_ref(v_reject_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_headApp_574_);
lean_dec_ref(v_arg_573_);
v_a_614_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___x_599_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_599_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_614_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
v___jp_584_:
{
lean_object* v___x_585_; size_t v_sz_586_; size_t v___x_587_; lean_object* v___x_588_; 
v___x_585_ = lean_box(0);
v_sz_586_ = lean_array_size(v_args_577_);
v___x_587_ = ((size_t)0ULL);
v___x_588_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3(v_arg_573_, v_headApp_574_, v_args_577_, v_sz_586_, v___x_587_, v___x_585_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_595_ == 0)
{
lean_object* v_unused_596_; 
v_unused_596_ = lean_ctor_get(v___x_588_, 0);
lean_dec(v_unused_596_);
v___x_590_ = v___x_588_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_dec(v___x_588_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v___x_585_);
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_585_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
else
{
return v___x_588_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___boxed(lean_object* v_arg_622_, lean_object* v_headApp_623_, lean_object* v_a_624_, lean_object* v_reject_625_, lean_object* v_args_626_, lean_object* v_body_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1(v_arg_622_, v_headApp_623_, v_a_624_, v_reject_625_, v_args_626_, v_body_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec_ref(v_args_626_);
return v_res_633_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__0));
v___x_636_ = l_Lean_stringToMessageData(v___x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2(lean_object* v_forwarded_637_, lean_object* v_arg_638_, lean_object* v_headApp_639_, lean_object* v_as_640_, size_t v_sz_641_, size_t v_i_642_, lean_object* v_b_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v_a_650_; uint8_t v___x_654_; 
v___x_654_ = lean_usize_dec_lt(v_i_642_, v_sz_641_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; 
lean_dec(v_headApp_639_);
lean_dec_ref(v_arg_638_);
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v_b_643_);
return v___x_655_;
}
else
{
lean_object* v_a_656_; lean_object* v_fst_657_; lean_object* v_snd_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_718_; 
v_a_656_ = lean_array_uget(v_as_640_, v_i_642_);
v_fst_657_ = lean_ctor_get(v_a_656_, 0);
v_snd_658_ = lean_ctor_get(v_a_656_, 1);
v_isSharedCheck_718_ = !lean_is_exclusive(v_a_656_);
if (v_isSharedCheck_718_ == 0)
{
v___x_660_ = v_a_656_;
v_isShared_661_ = v_isSharedCheck_718_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_snd_658_);
lean_inc(v_fst_657_);
lean_dec(v_a_656_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_718_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___f_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
lean_inc_ref(v_arg_638_);
v___f_662_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_662_, 0, v_arg_638_);
v___x_663_ = lean_box(0);
v___x_664_ = l_Lean_Expr_fvarId_x21(v_fst_657_);
lean_dec(v_fst_657_);
v___x_665_ = l_Lean_FVarId_getDecl___redArg(v___x_664_, v___y_644_, v___y_646_, v___y_647_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; uint8_t v___x_667_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_a_666_);
lean_dec_ref_known(v___x_665_, 1);
v___x_667_ = l_Lean_LocalDecl_binderInfo(v_a_666_);
lean_dec(v_a_666_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; 
v___x_668_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_snd_658_, v___y_645_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; uint8_t v___x_670_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
lean_dec_ref_known(v___x_668_, 1);
v___x_670_ = lean_expr_eqv(v_a_669_, v_forwarded_637_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; 
lean_inc(v___y_647_);
lean_inc_ref(v___y_646_);
lean_inc(v___y_645_);
lean_inc_ref(v___y_644_);
v___x_671_ = lean_infer_type(v_a_669_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v___x_673_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc_n(v_a_672_, 2);
lean_dec_ref_known(v___x_671_, 1);
v___x_673_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_a_672_, v___y_645_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_a_674_);
lean_dec_ref_known(v___x_673_, 1);
v___x_675_ = lean_box(0);
v___x_676_ = l_Lean_FindMVar_main(v___f_662_, v_a_674_, v___x_675_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_dec(v_a_672_);
lean_del_object(v___x_660_);
v_a_650_ = v___x_663_;
goto v___jp_649_;
}
else
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_680_; 
lean_dec_ref_known(v___x_676_, 1);
v___x_677_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1);
v___x_678_ = l_Lean_MessageData_ofExpr(v_a_672_);
if (v_isShared_661_ == 0)
{
lean_ctor_set_tag(v___x_660_, 7);
lean_ctor_set(v___x_660_, 1, v___x_678_);
lean_ctor_set(v___x_660_, 0, v___x_677_);
v___x_680_ = v___x_660_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_677_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v___x_678_);
v___x_680_ = v_reuseFailAlloc_685_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_681_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1);
v___x_682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_680_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
lean_inc(v_headApp_639_);
v___x_683_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint(v_headApp_639_, v___x_682_);
v___x_684_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v___x_683_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_dec_ref_known(v___x_684_, 1);
v_a_650_ = v___x_663_;
goto v___jp_649_;
}
else
{
lean_dec(v_headApp_639_);
lean_dec_ref(v_arg_638_);
return v___x_684_;
}
}
}
}
else
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_693_; 
lean_dec(v_a_672_);
lean_dec_ref(v___f_662_);
lean_del_object(v___x_660_);
lean_dec(v_headApp_639_);
lean_dec_ref(v_arg_638_);
v_a_686_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_693_ == 0)
{
v___x_688_ = v___x_673_;
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_673_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_689_ == 0)
{
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_686_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
else
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_701_; 
lean_dec_ref(v___f_662_);
lean_del_object(v___x_660_);
lean_dec(v_headApp_639_);
lean_dec_ref(v_arg_638_);
v_a_694_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_701_ == 0)
{
v___x_696_ = v___x_671_;
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_671_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_694_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
else
{
lean_dec(v_a_669_);
lean_dec_ref(v___f_662_);
lean_del_object(v___x_660_);
v_a_650_ = v___x_663_;
goto v___jp_649_;
}
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
lean_dec_ref(v___f_662_);
lean_del_object(v___x_660_);
lean_dec(v_headApp_639_);
lean_dec_ref(v_arg_638_);
v_a_702_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___x_668_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_668_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
else
{
lean_dec_ref(v___f_662_);
lean_del_object(v___x_660_);
lean_dec(v_snd_658_);
v_a_650_ = v___x_663_;
goto v___jp_649_;
}
}
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
lean_dec_ref(v___f_662_);
lean_del_object(v___x_660_);
lean_dec(v_snd_658_);
lean_dec(v_headApp_639_);
lean_dec_ref(v_arg_638_);
v_a_710_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_665_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_665_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_710_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
}
v___jp_649_:
{
size_t v___x_651_; size_t v___x_652_; 
v___x_651_ = ((size_t)1ULL);
v___x_652_ = lean_usize_add(v_i_642_, v___x_651_);
v_i_642_ = v___x_652_;
v_b_643_ = v_a_650_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___boxed(lean_object* v_forwarded_719_, lean_object* v_arg_720_, lean_object* v_headApp_721_, lean_object* v_as_722_, lean_object* v_sz_723_, lean_object* v_i_724_, lean_object* v_b_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
size_t v_sz_boxed_731_; size_t v_i_boxed_732_; lean_object* v_res_733_; 
v_sz_boxed_731_ = lean_unbox_usize(v_sz_723_);
lean_dec(v_sz_723_);
v_i_boxed_732_ = lean_unbox_usize(v_i_724_);
lean_dec(v_i_724_);
v_res_733_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2(v_forwarded_719_, v_arg_720_, v_headApp_721_, v_as_722_, v_sz_boxed_731_, v_i_boxed_732_, v_b_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec_ref(v_as_722_);
lean_dec_ref(v_forwarded_719_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2(lean_object* v_forwarded_734_, lean_object* v_arg_735_, lean_object* v_headApp_736_, lean_object* v_as_737_, size_t v_sz_738_, size_t v_i_739_, lean_object* v_b_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_a_747_; uint8_t v___x_751_; 
v___x_751_ = lean_usize_dec_lt(v_i_739_, v_sz_738_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; 
lean_dec(v_headApp_736_);
lean_dec_ref(v_arg_735_);
v___x_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_752_, 0, v_b_740_);
return v___x_752_;
}
else
{
lean_object* v_a_753_; lean_object* v_fst_754_; lean_object* v_snd_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_815_; 
v_a_753_ = lean_array_uget(v_as_737_, v_i_739_);
v_fst_754_ = lean_ctor_get(v_a_753_, 0);
v_snd_755_ = lean_ctor_get(v_a_753_, 1);
v_isSharedCheck_815_ = !lean_is_exclusive(v_a_753_);
if (v_isSharedCheck_815_ == 0)
{
v___x_757_ = v_a_753_;
v_isShared_758_ = v_isSharedCheck_815_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_snd_755_);
lean_inc(v_fst_754_);
lean_dec(v_a_753_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_815_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___f_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
lean_inc_ref(v_arg_735_);
v___f_759_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_759_, 0, v_arg_735_);
v___x_760_ = lean_box(0);
v___x_761_ = l_Lean_Expr_fvarId_x21(v_fst_754_);
lean_dec(v_fst_754_);
v___x_762_ = l_Lean_FVarId_getDecl___redArg(v___x_761_, v___y_741_, v___y_743_, v___y_744_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; uint8_t v___x_764_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_a_763_);
lean_dec_ref_known(v___x_762_, 1);
v___x_764_ = l_Lean_LocalDecl_binderInfo(v_a_763_);
lean_dec(v_a_763_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_snd_755_, v___y_742_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; uint8_t v___x_767_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_765_, 1);
v___x_767_ = lean_expr_eqv(v_a_766_, v_forwarded_734_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; 
lean_inc(v___y_744_);
lean_inc_ref(v___y_743_);
lean_inc(v___y_742_);
lean_inc_ref(v___y_741_);
v___x_768_ = lean_infer_type(v_a_766_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; lean_object* v___x_770_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc_n(v_a_769_, 2);
lean_dec_ref_known(v___x_768_, 1);
v___x_770_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_a_769_, v___y_742_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_771_);
lean_dec_ref_known(v___x_770_, 1);
v___x_772_ = lean_box(0);
v___x_773_ = l_Lean_FindMVar_main(v___f_759_, v_a_771_, v___x_772_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_dec(v_a_769_);
lean_del_object(v___x_757_);
v_a_747_ = v___x_760_;
goto v___jp_746_;
}
else
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_777_; 
lean_dec_ref_known(v___x_773_, 1);
v___x_774_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1);
v___x_775_ = l_Lean_MessageData_ofExpr(v_a_769_);
if (v_isShared_758_ == 0)
{
lean_ctor_set_tag(v___x_757_, 7);
lean_ctor_set(v___x_757_, 1, v___x_775_);
lean_ctor_set(v___x_757_, 0, v___x_774_);
v___x_777_ = v___x_757_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v___x_775_);
v___x_777_ = v_reuseFailAlloc_782_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_778_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1);
v___x_779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_777_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
lean_inc(v_headApp_736_);
v___x_780_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint(v_headApp_736_, v___x_779_);
v___x_781_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v___x_780_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_dec_ref_known(v___x_781_, 1);
v_a_747_ = v___x_760_;
goto v___jp_746_;
}
else
{
lean_dec(v_headApp_736_);
lean_dec_ref(v_arg_735_);
return v___x_781_;
}
}
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec(v_a_769_);
lean_dec_ref(v___f_759_);
lean_del_object(v___x_757_);
lean_dec(v_headApp_736_);
lean_dec_ref(v_arg_735_);
v_a_783_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_770_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_770_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_dec_ref(v___f_759_);
lean_del_object(v___x_757_);
lean_dec(v_headApp_736_);
lean_dec_ref(v_arg_735_);
v_a_791_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_768_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_768_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
else
{
lean_dec(v_a_766_);
lean_dec_ref(v___f_759_);
lean_del_object(v___x_757_);
v_a_747_ = v___x_760_;
goto v___jp_746_;
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec_ref(v___f_759_);
lean_del_object(v___x_757_);
lean_dec(v_headApp_736_);
lean_dec_ref(v_arg_735_);
v_a_799_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_765_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_765_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
else
{
lean_dec_ref(v___f_759_);
lean_del_object(v___x_757_);
lean_dec(v_snd_755_);
v_a_747_ = v___x_760_;
goto v___jp_746_;
}
}
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
lean_dec_ref(v___f_759_);
lean_del_object(v___x_757_);
lean_dec(v_snd_755_);
lean_dec(v_headApp_736_);
lean_dec_ref(v_arg_735_);
v_a_807_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_762_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_762_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
}
v___jp_746_:
{
size_t v___x_748_; size_t v___x_749_; lean_object* v___x_750_; 
v___x_748_ = ((size_t)1ULL);
v___x_749_ = lean_usize_add(v_i_739_, v___x_748_);
v___x_750_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2(v_forwarded_734_, v_arg_735_, v_headApp_736_, v_as_737_, v_sz_738_, v___x_749_, v_a_747_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
return v___x_750_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___boxed(lean_object* v_forwarded_816_, lean_object* v_arg_817_, lean_object* v_headApp_818_, lean_object* v_as_819_, lean_object* v_sz_820_, lean_object* v_i_821_, lean_object* v_b_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
size_t v_sz_boxed_828_; size_t v_i_boxed_829_; lean_object* v_res_830_; 
v_sz_boxed_828_ = lean_unbox_usize(v_sz_820_);
lean_dec(v_sz_820_);
v_i_boxed_829_ = lean_unbox_usize(v_i_821_);
lean_dec(v_i_821_);
v_res_830_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2(v_forwarded_816_, v_arg_817_, v_headApp_818_, v_as_819_, v_sz_boxed_828_, v_i_boxed_829_, v_b_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec_ref(v_as_819_);
lean_dec_ref(v_forwarded_816_);
return v_res_830_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___closed__0(void){
_start:
{
lean_object* v___x_831_; lean_object* v_dummy_832_; 
v___x_831_ = lean_box(0);
v_dummy_832_ = l_Lean_Expr_sort___override(v___x_831_);
return v_dummy_832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2(lean_object* v_probeExpr_833_, lean_object* v_forwarded_834_, lean_object* v_arg_835_, lean_object* v_headApp_836_, lean_object* v_fvars_837_, lean_object* v_x_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_dummy_844_; lean_object* v_nargs_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; size_t v_sz_852_; size_t v___x_853_; lean_object* v___x_854_; 
v_dummy_844_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___closed__0, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___closed__0_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___closed__0);
v_nargs_845_ = l_Lean_Expr_getAppNumArgs(v_probeExpr_833_);
lean_inc(v_nargs_845_);
v___x_846_ = lean_mk_array(v_nargs_845_, v_dummy_844_);
v___x_847_ = lean_unsigned_to_nat(1u);
v___x_848_ = lean_nat_sub(v_nargs_845_, v___x_847_);
lean_dec(v_nargs_845_);
v___x_849_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_probeExpr_833_, v___x_846_, v___x_848_);
v___x_850_ = l_Array_zip___redArg(v_fvars_837_, v___x_849_);
lean_dec_ref(v___x_849_);
v___x_851_ = lean_box(0);
v_sz_852_ = lean_array_size(v___x_850_);
v___x_853_ = ((size_t)0ULL);
v___x_854_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2(v_forwarded_834_, v_arg_835_, v_headApp_836_, v___x_850_, v_sz_852_, v___x_853_, v___x_851_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
lean_dec_ref(v___x_850_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_861_ == 0)
{
lean_object* v_unused_862_; 
v_unused_862_ = lean_ctor_get(v___x_854_, 0);
lean_dec(v_unused_862_);
v___x_856_ = v___x_854_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_dec(v___x_854_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v___x_851_);
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_851_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
else
{
return v___x_854_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___boxed(lean_object* v_probeExpr_863_, lean_object* v_forwarded_864_, lean_object* v_arg_865_, lean_object* v_headApp_866_, lean_object* v_fvars_867_, lean_object* v_x_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2(v_probeExpr_863_, v_forwarded_864_, v_arg_865_, v_headApp_866_, v_fvars_867_, v_x_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec_ref(v_x_868_);
lean_dec_ref(v_fvars_867_);
lean_dec_ref(v_forwarded_864_);
return v_res_874_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__1(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__0));
v___x_877_ = l_Lean_stringToMessageData(v___x_876_);
return v___x_877_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__3(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__2));
v___x_880_ = l_Lean_stringToMessageData(v___x_879_);
return v___x_880_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__5(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__4));
v___x_883_ = l_Lean_stringToMessageData(v___x_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder(lean_object* v_headApp_884_, lean_object* v_forwarded_885_, lean_object* v_probeExpr_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v_reject_892_; lean_object* v___x_893_; 
lean_inc(v_headApp_884_);
v_reject_892_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0___boxed), 8, 1);
lean_closure_set(v_reject_892_, 0, v_headApp_884_);
lean_inc(v_a_890_);
lean_inc_ref(v_a_889_);
lean_inc(v_a_888_);
lean_inc_ref(v_a_887_);
lean_inc_ref(v_probeExpr_886_);
v___x_893_ = lean_infer_type(v_probeExpr_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v___x_895_; lean_object* v_a_896_; lean_object* v___x_897_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_a_894_);
lean_dec_ref_known(v___x_893_, 1);
v___x_895_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_a_894_, v_a_888_);
v_a_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_a_896_);
lean_dec_ref(v___x_895_);
v___x_897_ = l_Lean_Meta_whnfD(v_a_896_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_a_898_);
lean_dec_ref_known(v___x_897_, 1);
if (lean_obj_tag(v_a_898_) == 5)
{
lean_object* v_arg_899_; lean_object* v___f_900_; lean_object* v___f_901_; lean_object* v___y_903_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_906_; uint8_t v___x_931_; 
v_arg_899_ = lean_ctor_get(v_a_898_, 1);
lean_inc_ref_n(v_arg_899_, 3);
lean_inc_n(v_headApp_884_, 2);
v___f_900_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___boxed), 11, 4);
lean_closure_set(v___f_900_, 0, v_arg_899_);
lean_closure_set(v___f_900_, 1, v_headApp_884_);
lean_closure_set(v___f_900_, 2, v_a_898_);
lean_closure_set(v___f_900_, 3, v_reject_892_);
lean_inc_ref(v_forwarded_885_);
lean_inc_ref(v_probeExpr_886_);
v___f_901_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___boxed), 11, 4);
lean_closure_set(v___f_901_, 0, v_probeExpr_886_);
lean_closure_set(v___f_901_, 1, v_forwarded_885_);
lean_closure_set(v___f_901_, 2, v_arg_899_);
lean_closure_set(v___f_901_, 3, v_headApp_884_);
v___x_931_ = l_Lean_Expr_isMVar(v_arg_899_);
lean_dec_ref(v_arg_899_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; lean_object* v___x_933_; 
lean_dec_ref(v___f_901_);
lean_dec_ref(v___f_900_);
lean_dec_ref(v_probeExpr_886_);
lean_dec_ref(v_forwarded_885_);
v___x_932_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__1);
v___x_933_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0(v_headApp_884_, lean_box(0), v___x_932_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
return v___x_933_;
}
else
{
lean_dec(v_headApp_884_);
v___y_903_ = v_a_887_;
v___y_904_ = v_a_888_;
v___y_905_ = v_a_889_;
v___y_906_ = v_a_890_;
goto v___jp_902_;
}
v___jp_902_:
{
lean_object* v___x_907_; 
lean_inc(v___y_906_);
lean_inc_ref(v___y_905_);
lean_inc(v___y_904_);
lean_inc_ref(v___y_903_);
v___x_907_ = lean_infer_type(v_forwarded_885_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; uint8_t v___x_909_; lean_object* v___x_910_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_a_908_);
lean_dec_ref_known(v___x_907_, 1);
v___x_909_ = 0;
v___x_910_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg(v_a_908_, v___f_900_, v___x_909_, v___x_909_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v___x_911_; lean_object* v___x_912_; 
lean_dec_ref_known(v___x_910_, 1);
v___x_911_ = l_Lean_Expr_getAppFn(v_probeExpr_886_);
lean_dec_ref(v_probeExpr_886_);
lean_inc(v___y_906_);
lean_inc_ref(v___y_905_);
lean_inc(v___y_904_);
lean_inc_ref(v___y_903_);
v___x_912_ = lean_infer_type(v___x_911_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v___x_914_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_913_);
lean_dec_ref_known(v___x_912_, 1);
v___x_914_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg(v_a_913_, v___f_901_, v___x_909_, v___x_909_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
return v___x_914_;
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec_ref(v___f_901_);
v_a_915_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_912_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_912_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
else
{
lean_dec_ref(v___f_901_);
lean_dec_ref(v_probeExpr_886_);
return v___x_910_;
}
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
lean_dec_ref(v___f_901_);
lean_dec_ref(v___f_900_);
lean_dec_ref(v_probeExpr_886_);
v_a_923_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_907_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_907_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
else
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
lean_dec_ref(v_reject_892_);
lean_dec_ref(v_probeExpr_886_);
lean_dec_ref(v_forwarded_885_);
v___x_934_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__3, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__3);
v___x_935_ = l_Lean_MessageData_ofExpr(v_a_898_);
v___x_936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_934_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__5, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__5_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__5);
v___x_938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_936_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
v___x_939_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0(v_headApp_884_, lean_box(0), v___x_938_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
return v___x_939_;
}
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec_ref(v_reject_892_);
lean_dec_ref(v_probeExpr_886_);
lean_dec_ref(v_forwarded_885_);
lean_dec(v_headApp_884_);
v_a_940_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_897_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_897_);
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
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
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
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec_ref(v_reject_892_);
lean_dec_ref(v_probeExpr_886_);
lean_dec_ref(v_forwarded_885_);
lean_dec(v_headApp_884_);
v_a_948_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_893_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_893_);
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
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___boxed(lean_object* v_headApp_956_, lean_object* v_forwarded_957_, lean_object* v_probeExpr_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder(v_headApp_956_, v_forwarded_957_, v_probeExpr_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0(lean_object* v_00_u03b1_965_, lean_object* v_msg_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v_msg_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___boxed(lean_object* v_00_u03b1_973_, lean_object* v_msg_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0(v_00_u03b1_973_, v_msg_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___redArg(lean_object* v_e_981_, lean_object* v___y_982_){
_start:
{
uint8_t v___x_984_; 
v___x_984_ = l_Lean_Expr_hasMVar(v_e_981_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; 
v___x_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_985_, 0, v_e_981_);
return v___x_985_;
}
else
{
lean_object* v___x_986_; lean_object* v_mctx_987_; lean_object* v___x_988_; lean_object* v_fst_989_; lean_object* v_snd_990_; lean_object* v___x_991_; lean_object* v_cache_992_; lean_object* v_zetaDeltaFVarIds_993_; lean_object* v_postponed_994_; lean_object* v_diag_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1004_; 
v___x_986_ = lean_st_ref_get(v___y_982_);
v_mctx_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc_ref(v_mctx_987_);
lean_dec(v___x_986_);
v___x_988_ = l_Lean_instantiateMVarsCore(v_mctx_987_, v_e_981_);
v_fst_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_fst_989_);
v_snd_990_ = lean_ctor_get(v___x_988_, 1);
lean_inc(v_snd_990_);
lean_dec_ref(v___x_988_);
v___x_991_ = lean_st_ref_take(v___y_982_);
v_cache_992_ = lean_ctor_get(v___x_991_, 1);
v_zetaDeltaFVarIds_993_ = lean_ctor_get(v___x_991_, 2);
v_postponed_994_ = lean_ctor_get(v___x_991_, 3);
v_diag_995_ = lean_ctor_get(v___x_991_, 4);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1004_ == 0)
{
lean_object* v_unused_1005_; 
v_unused_1005_ = lean_ctor_get(v___x_991_, 0);
lean_dec(v_unused_1005_);
v___x_997_ = v___x_991_;
v_isShared_998_ = v_isSharedCheck_1004_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_diag_995_);
lean_inc(v_postponed_994_);
lean_inc(v_zetaDeltaFVarIds_993_);
lean_inc(v_cache_992_);
lean_dec(v___x_991_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1004_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v_snd_990_);
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_snd_990_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v_cache_992_);
lean_ctor_set(v_reuseFailAlloc_1003_, 2, v_zetaDeltaFVarIds_993_);
lean_ctor_set(v_reuseFailAlloc_1003_, 3, v_postponed_994_);
lean_ctor_set(v_reuseFailAlloc_1003_, 4, v_diag_995_);
v___x_1000_ = v_reuseFailAlloc_1003_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = lean_st_ref_put(v___y_982_, v___x_1000_);
v___x_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1002_, 0, v_fst_989_);
return v___x_1002_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___redArg___boxed(lean_object* v_e_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___redArg(v_e_1006_, v___y_1007_);
lean_dec(v___y_1007_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1(lean_object* v_e_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___redArg(v_e_1010_, v___y_1014_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___boxed(lean_object* v_e_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1(v_e_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
return v_res_1027_;
}
}
static lean_object* _init_l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__3));
v___x_1037_ = l_String_toRawSubstring_x27(v___x_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0(lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_fst_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v_toCold_1057_; lean_object* v_ref_1058_; lean_object* v_quotContext_1059_; lean_object* v_currMacroScope_1060_; uint8_t v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; uint8_t v___x_1073_; lean_object* v___x_1074_; 
v_toCold_1057_ = lean_ctor_get(v___y_1054_, 0);
v_ref_1058_ = lean_ctor_get(v___y_1054_, 2);
v_quotContext_1059_ = lean_ctor_get(v_toCold_1057_, 8);
v_currMacroScope_1060_ = lean_ctor_get(v_toCold_1057_, 9);
v___x_1061_ = 0;
v___x_1062_ = l_Lean_SourceInfo_fromRef(v_ref_1058_, v___x_1061_);
v___x_1063_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__1));
v___x_1064_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__2));
lean_inc_n(v___x_1062_, 3);
v___x_1065_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1062_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = lean_obj_once(&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__4, &l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__4_once, _init_l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__4);
v___x_1067_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__5));
lean_inc(v_currMacroScope_1060_);
lean_inc(v_quotContext_1059_);
v___x_1068_ = l_Lean_addMacroScope(v_quotContext_1059_, v___x_1067_, v_currMacroScope_1060_);
v___x_1069_ = lean_box(0);
v___x_1070_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1062_);
lean_ctor_set(v___x_1070_, 1, v___x_1066_);
lean_ctor_set(v___x_1070_, 2, v___x_1068_);
lean_ctor_set(v___x_1070_, 3, v___x_1069_);
v___x_1071_ = l_Lean_Syntax_node2(v___x_1062_, v___x_1063_, v___x_1065_, v___x_1070_);
v___x_1072_ = lean_box(0);
v___x_1073_ = 1;
lean_inc(v___x_1071_);
v___x_1074_ = l_Lean_Elab_Term_elabTerm(v___x_1071_, v___x_1072_, v___x_1073_, v___x_1073_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v___y_1054_, v___y_1055_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_a_1075_);
lean_dec_ref_known(v___x_1074_, 1);
v___x_1076_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__7));
v___x_1077_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__9));
lean_inc(v___x_1062_);
v___x_1078_ = l_Lean_Syntax_node1(v___x_1062_, v___x_1077_, v___x_1071_);
v___x_1079_ = l_Lean_Syntax_node2(v___x_1062_, v___x_1076_, v_fst_1053_, v___x_1078_);
v___x_1080_ = l_Lean_Elab_Term_elabTerm(v___x_1079_, v___x_1072_, v___x_1073_, v___x_1073_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v___y_1054_, v___y_1055_);
lean_dec_ref(v___y_1054_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1089_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1083_ = v___x_1080_;
v_isShared_1084_ = v_isSharedCheck_1089_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1080_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1089_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1085_, 0, v_a_1075_);
lean_ctor_set(v___x_1085_, 1, v_a_1081_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v___x_1085_);
v___x_1087_ = v___x_1083_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1085_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
lean_dec(v_a_1075_);
v_a_1090_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1080_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1080_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_dec(v___x_1071_);
lean_dec(v___x_1062_);
lean_dec_ref(v___y_1054_);
lean_dec(v_fst_1053_);
v_a_1098_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1074_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1074_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___boxed(lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_fst_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0(v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_fst_1110_, v___y_1111_, v___y_1112_);
lean_dec(v___y_1112_);
lean_dec(v_a_1109_);
lean_dec_ref(v_a_1108_);
lean_dec(v_a_1107_);
lean_dec_ref(v_a_1106_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__1(lean_object* v_body_1115_, lean_object* v_cont_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
uint8_t v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = 1;
v___x_1126_ = l_Lean_Elab_Do_elabDoSeq(v_body_1115_, v_cont_1116_, v___x_1125_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__1___boxed(lean_object* v_body_1127_, lean_object* v_cont_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__1(v_body_1127_, v_cont_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec_ref(v___y_1129_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__2(lean_object* v_a_1138_, lean_object* v___f_1139_, lean_object* v_a_1140_, lean_object* v_bsExpr_1141_, lean_object* v_x_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Lean_Elab_Do_EffectForwarder_lift(v_a_1138_, v___f_1139_, v_a_1140_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1151_; uint8_t v___x_1152_; uint8_t v___x_1153_; uint8_t v___x_1154_; lean_object* v___x_1155_; 
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_a_1151_);
lean_dec_ref_known(v___x_1150_, 1);
v___x_1152_ = 0;
v___x_1153_ = 1;
v___x_1154_ = 1;
v___x_1155_ = l_Lean_Meta_mkLambdaFVars(v_bsExpr_1141_, v_a_1151_, v___x_1152_, v___x_1153_, v___x_1152_, v___x_1153_, v___x_1154_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
return v___x_1155_;
}
else
{
return v___x_1150_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__2___boxed(lean_object* v_a_1156_, lean_object* v___f_1157_, lean_object* v_a_1158_, lean_object* v_bsExpr_1159_, lean_object* v_x_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__2(v_a_1156_, v___f_1157_, v_a_1158_, v_bsExpr_1159_, v_x_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v_x_1160_);
lean_dec_ref(v_bsExpr_1159_);
lean_dec_ref(v_a_1158_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__3(lean_object* v_a_1169_, lean_object* v_fst_1170_, lean_object* v___f_1171_, lean_object* v_____r_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1180_, 0, v_a_1169_);
v___x_1181_ = l_Lean_Elab_Term_elabFunBinders___redArg(v_fst_1170_, v___x_1180_, v___f_1171_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__3___boxed(lean_object* v_a_1182_, lean_object* v_fst_1183_, lean_object* v___f_1184_, lean_object* v_____r_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__3(v_a_1182_, v_fst_1183_, v___f_1184_, v_____r_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec_ref(v_fst_1183_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0___redArg(lean_object* v_msg_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v_ref_1200_; lean_object* v___x_1201_; lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1210_; 
v_ref_1200_ = lean_ctor_get(v___y_1197_, 2);
v___x_1201_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0(v_msg_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
v_a_1202_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1204_ = v___x_1201_;
v_isShared_1205_ = v_isSharedCheck_1210_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1201_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1210_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1206_; lean_object* v___x_1208_; 
lean_inc(v_ref_1200_);
v___x_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1206_, 0, v_ref_1200_);
lean_ctor_set(v___x_1206_, 1, v_a_1202_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set_tag(v___x_1204_, 1);
lean_ctor_set(v___x_1204_, 0, v___x_1206_);
v___x_1208_ = v___x_1204_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1206_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0___redArg___boxed(lean_object* v_msg_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0___redArg(v_msg_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__2(size_t v_sz_1218_, size_t v_i_1219_, lean_object* v_bs_1220_){
_start:
{
uint8_t v___x_1221_; 
v___x_1221_ = lean_usize_dec_lt(v_i_1219_, v_sz_1218_);
if (v___x_1221_ == 0)
{
return v_bs_1220_;
}
else
{
lean_object* v_v_1222_; lean_object* v___x_1223_; lean_object* v_bs_x27_1224_; size_t v___x_1225_; size_t v___x_1226_; lean_object* v___x_1227_; 
v_v_1222_ = lean_array_uget(v_bs_1220_, v_i_1219_);
v___x_1223_ = lean_unsigned_to_nat(0u);
v_bs_x27_1224_ = lean_array_uset(v_bs_1220_, v_i_1219_, v___x_1223_);
v___x_1225_ = ((size_t)1ULL);
v___x_1226_ = lean_usize_add(v_i_1219_, v___x_1225_);
v___x_1227_ = lean_array_uset(v_bs_x27_1224_, v_i_1219_, v_v_1222_);
v_i_1219_ = v___x_1226_;
v_bs_1220_ = v___x_1227_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__2___boxed(lean_object* v_sz_1229_, lean_object* v_i_1230_, lean_object* v_bs_1231_){
_start:
{
size_t v_sz_boxed_1232_; size_t v_i_boxed_1233_; lean_object* v_res_1234_; 
v_sz_boxed_1232_ = lean_unbox_usize(v_sz_1229_);
lean_dec(v_sz_1229_);
v_i_boxed_1233_ = lean_unbox_usize(v_i_1230_);
lean_dec(v_i_1230_);
v_res_1234_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__2(v_sz_boxed_1232_, v_i_boxed_1233_, v_bs_1231_);
return v_res_1234_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16___redArg(lean_object* v_keys_1235_, lean_object* v_i_1236_, lean_object* v_k_1237_){
_start:
{
lean_object* v___x_1238_; uint8_t v___x_1239_; 
v___x_1238_ = lean_array_get_size(v_keys_1235_);
v___x_1239_ = lean_nat_dec_lt(v_i_1236_, v___x_1238_);
if (v___x_1239_ == 0)
{
lean_dec(v_i_1236_);
return v___x_1239_;
}
else
{
lean_object* v_k_x27_1240_; uint8_t v___x_1241_; 
v_k_x27_1240_ = lean_array_fget_borrowed(v_keys_1235_, v_i_1236_);
v___x_1241_ = l_Lean_instBEqExtraModUse_beq(v_k_1237_, v_k_x27_1240_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1242_ = lean_unsigned_to_nat(1u);
v___x_1243_ = lean_nat_add(v_i_1236_, v___x_1242_);
lean_dec(v_i_1236_);
v_i_1236_ = v___x_1243_;
goto _start;
}
else
{
lean_dec(v_i_1236_);
return v___x_1239_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16___redArg___boxed(lean_object* v_keys_1245_, lean_object* v_i_1246_, lean_object* v_k_1247_){
_start:
{
uint8_t v_res_1248_; lean_object* v_r_1249_; 
v_res_1248_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16___redArg(v_keys_1245_, v_i_1246_, v_k_1247_);
lean_dec_ref(v_k_1247_);
lean_dec_ref(v_keys_1245_);
v_r_1249_ = lean_box(v_res_1248_);
return v_r_1249_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13___redArg(lean_object* v_x_1250_, size_t v_x_1251_, lean_object* v_x_1252_){
_start:
{
if (lean_obj_tag(v_x_1250_) == 0)
{
lean_object* v_es_1253_; lean_object* v___x_1254_; size_t v___x_1255_; size_t v___x_1256_; lean_object* v_j_1257_; lean_object* v___x_1258_; 
v_es_1253_ = lean_ctor_get(v_x_1250_, 0);
v___x_1254_ = lean_box(2);
v___x_1255_ = ((size_t)31ULL);
v___x_1256_ = lean_usize_land(v_x_1251_, v___x_1255_);
v_j_1257_ = lean_usize_to_nat(v___x_1256_);
v___x_1258_ = lean_array_get_borrowed(v___x_1254_, v_es_1253_, v_j_1257_);
lean_dec(v_j_1257_);
switch(lean_obj_tag(v___x_1258_))
{
case 0:
{
lean_object* v_key_1259_; uint8_t v___x_1260_; 
v_key_1259_ = lean_ctor_get(v___x_1258_, 0);
v___x_1260_ = l_Lean_instBEqExtraModUse_beq(v_x_1252_, v_key_1259_);
return v___x_1260_;
}
case 1:
{
lean_object* v_node_1261_; size_t v___x_1262_; size_t v___x_1263_; 
v_node_1261_ = lean_ctor_get(v___x_1258_, 0);
v___x_1262_ = ((size_t)5ULL);
v___x_1263_ = lean_usize_shift_right(v_x_1251_, v___x_1262_);
v_x_1250_ = v_node_1261_;
v_x_1251_ = v___x_1263_;
goto _start;
}
default: 
{
uint8_t v___x_1265_; 
v___x_1265_ = 0;
return v___x_1265_;
}
}
}
else
{
lean_object* v_ks_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; 
v_ks_1266_ = lean_ctor_get(v_x_1250_, 0);
v___x_1267_ = lean_unsigned_to_nat(0u);
v___x_1268_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16___redArg(v_ks_1266_, v___x_1267_, v_x_1252_);
return v___x_1268_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13___redArg___boxed(lean_object* v_x_1269_, lean_object* v_x_1270_, lean_object* v_x_1271_){
_start:
{
size_t v_x_28298__boxed_1272_; uint8_t v_res_1273_; lean_object* v_r_1274_; 
v_x_28298__boxed_1272_ = lean_unbox_usize(v_x_1270_);
lean_dec(v_x_1270_);
v_res_1273_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13___redArg(v_x_1269_, v_x_28298__boxed_1272_, v_x_1271_);
lean_dec_ref(v_x_1271_);
lean_dec_ref(v_x_1269_);
v_r_1274_ = lean_box(v_res_1273_);
return v_r_1274_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9___redArg(lean_object* v_x_1275_, lean_object* v_x_1276_){
_start:
{
uint64_t v___x_1277_; size_t v___x_1278_; uint8_t v___x_1279_; 
v___x_1277_ = l_Lean_instHashableExtraModUse_hash(v_x_1276_);
v___x_1278_ = lean_uint64_to_usize(v___x_1277_);
v___x_1279_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13___redArg(v_x_1275_, v___x_1278_, v_x_1276_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9___redArg___boxed(lean_object* v_x_1280_, lean_object* v_x_1281_){
_start:
{
uint8_t v_res_1282_; lean_object* v_r_1283_; 
v_res_1282_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9___redArg(v_x_1280_, v_x_1281_);
lean_dec_ref(v_x_1281_);
lean_dec_ref(v_x_1280_);
v_r_1283_ = lean_box(v_res_1282_);
return v_r_1283_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1284_; double v___x_1285_; 
v___x_1284_ = lean_unsigned_to_nat(0u);
v___x_1285_ = lean_float_of_nat(v___x_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg(lean_object* v_cls_1289_, lean_object* v_msg_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v_ref_1296_; lean_object* v___x_1297_; lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1343_; 
v_ref_1296_ = lean_ctor_get(v___y_1293_, 2);
v___x_1297_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0(v_msg_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1300_ = v___x_1297_;
v_isShared_1301_ = v_isSharedCheck_1343_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1297_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1343_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1302_; lean_object* v_traceState_1303_; lean_object* v_env_1304_; lean_object* v_nextMacroScope_1305_; lean_object* v_ngen_1306_; lean_object* v_auxDeclNGen_1307_; lean_object* v_cache_1308_; lean_object* v_recordedDeps_1309_; lean_object* v_messages_1310_; lean_object* v_infoState_1311_; lean_object* v_snapshotTasks_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1342_; 
v___x_1302_ = lean_st_ref_take(v___y_1294_);
v_traceState_1303_ = lean_ctor_get(v___x_1302_, 4);
v_env_1304_ = lean_ctor_get(v___x_1302_, 0);
v_nextMacroScope_1305_ = lean_ctor_get(v___x_1302_, 1);
v_ngen_1306_ = lean_ctor_get(v___x_1302_, 2);
v_auxDeclNGen_1307_ = lean_ctor_get(v___x_1302_, 3);
v_cache_1308_ = lean_ctor_get(v___x_1302_, 5);
v_recordedDeps_1309_ = lean_ctor_get(v___x_1302_, 6);
v_messages_1310_ = lean_ctor_get(v___x_1302_, 7);
v_infoState_1311_ = lean_ctor_get(v___x_1302_, 8);
v_snapshotTasks_1312_ = lean_ctor_get(v___x_1302_, 9);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1314_ = v___x_1302_;
v_isShared_1315_ = v_isSharedCheck_1342_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_snapshotTasks_1312_);
lean_inc(v_infoState_1311_);
lean_inc(v_messages_1310_);
lean_inc(v_recordedDeps_1309_);
lean_inc(v_cache_1308_);
lean_inc(v_traceState_1303_);
lean_inc(v_auxDeclNGen_1307_);
lean_inc(v_ngen_1306_);
lean_inc(v_nextMacroScope_1305_);
lean_inc(v_env_1304_);
lean_dec(v___x_1302_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1342_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
uint64_t v_tid_1316_; lean_object* v_traces_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1341_; 
v_tid_1316_ = lean_ctor_get_uint64(v_traceState_1303_, sizeof(void*)*1);
v_traces_1317_ = lean_ctor_get(v_traceState_1303_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v_traceState_1303_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1319_ = v_traceState_1303_;
v_isShared_1320_ = v_isSharedCheck_1341_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_traces_1317_);
lean_dec(v_traceState_1303_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1341_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; double v___x_1323_; uint8_t v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1332_; 
v___x_1321_ = lean_box(0);
v___x_1322_ = lean_box(0);
v___x_1323_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___closed__0);
v___x_1324_ = 0;
v___x_1325_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___closed__1));
v___x_1326_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1326_, 0, v_cls_1289_);
lean_ctor_set(v___x_1326_, 1, v___x_1322_);
lean_ctor_set(v___x_1326_, 2, v___x_1325_);
lean_ctor_set_float(v___x_1326_, sizeof(void*)*3, v___x_1323_);
lean_ctor_set_float(v___x_1326_, sizeof(void*)*3 + 8, v___x_1323_);
lean_ctor_set_uint8(v___x_1326_, sizeof(void*)*3 + 16, v___x_1324_);
v___x_1327_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___closed__2));
v___x_1328_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1326_);
lean_ctor_set(v___x_1328_, 1, v_a_1298_);
lean_ctor_set(v___x_1328_, 2, v___x_1327_);
lean_inc(v_ref_1296_);
v___x_1329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1329_, 0, v_ref_1296_);
lean_ctor_set(v___x_1329_, 1, v___x_1328_);
v___x_1330_ = l_Lean_PersistentArray_push___redArg(v_traces_1317_, v___x_1329_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 0, v___x_1330_);
v___x_1332_ = v___x_1319_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1330_);
lean_ctor_set_uint64(v_reuseFailAlloc_1340_, sizeof(void*)*1, v_tid_1316_);
v___x_1332_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
lean_object* v___x_1334_; 
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 4, v___x_1332_);
v___x_1334_ = v___x_1314_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_env_1304_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_nextMacroScope_1305_);
lean_ctor_set(v_reuseFailAlloc_1339_, 2, v_ngen_1306_);
lean_ctor_set(v_reuseFailAlloc_1339_, 3, v_auxDeclNGen_1307_);
lean_ctor_set(v_reuseFailAlloc_1339_, 4, v___x_1332_);
lean_ctor_set(v_reuseFailAlloc_1339_, 5, v_cache_1308_);
lean_ctor_set(v_reuseFailAlloc_1339_, 6, v_recordedDeps_1309_);
lean_ctor_set(v_reuseFailAlloc_1339_, 7, v_messages_1310_);
lean_ctor_set(v_reuseFailAlloc_1339_, 8, v_infoState_1311_);
lean_ctor_set(v_reuseFailAlloc_1339_, 9, v_snapshotTasks_1312_);
v___x_1334_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1335_ = lean_st_ref_put(v___y_1294_, v___x_1334_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 0, v___x_1321_);
v___x_1337_ = v___x_1300_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1321_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___boxed(lean_object* v_cls_1344_, lean_object* v_msg_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg(v_cls_1344_, v_msg_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
return v_res_1351_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__0(void){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1352_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__1(void){
_start:
{
lean_object* v___x_1353_; 
v___x_1353_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1353_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__2(void){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__1);
v___x_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
return v___x_1355_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__3(void){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__2);
v___x_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1356_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
return v___x_1357_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__4(void){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__2);
v___x_1359_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
lean_ctor_set(v___x_1359_, 1, v___x_1358_);
lean_ctor_set(v___x_1359_, 2, v___x_1358_);
lean_ctor_set(v___x_1359_, 3, v___x_1358_);
lean_ctor_set(v___x_1359_, 4, v___x_1358_);
lean_ctor_set(v___x_1359_, 5, v___x_1358_);
return v___x_1359_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__8(void){
_start:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__7));
v___x_1365_ = l_Lean_stringToMessageData(v___x_1364_);
return v___x_1365_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__10(void){
_start:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__9));
v___x_1368_ = l_Lean_stringToMessageData(v___x_1367_);
return v___x_1368_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__11(void){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___closed__1));
v___x_1370_ = l_Lean_stringToMessageData(v___x_1369_);
return v___x_1370_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__14(void){
_start:
{
lean_object* v_cls_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v_cls_1374_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__6));
v___x_1375_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__13));
v___x_1376_ = l_Lean_Name_append(v___x_1375_, v_cls_1374_);
return v___x_1376_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__16(void){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1378_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__15));
v___x_1379_ = l_Lean_stringToMessageData(v___x_1378_);
return v___x_1379_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__18(void){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__17));
v___x_1382_ = l_Lean_stringToMessageData(v___x_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6(lean_object* v_mod_1387_, uint8_t v_isMeta_1388_, lean_object* v_hint_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v_env_1399_; uint8_t v_isExporting_1400_; lean_object* v_entry_1401_; lean_object* v___x_1402_; lean_object* v_env_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___x_1450_; uint8_t v___x_1451_; 
v___x_1397_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__0);
v___x_1398_ = lean_st_ref_get(v___y_1395_);
v_env_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc_ref(v_env_1399_);
lean_dec(v___x_1398_);
v_isExporting_1400_ = lean_ctor_get_uint8(v_env_1399_, sizeof(void*)*8);
lean_dec_ref(v_env_1399_);
lean_inc(v_mod_1387_);
v_entry_1401_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1401_, 0, v_mod_1387_);
lean_ctor_set_uint8(v_entry_1401_, sizeof(void*)*1, v_isExporting_1400_);
lean_ctor_set_uint8(v_entry_1401_, sizeof(void*)*1 + 1, v_isMeta_1388_);
v___x_1402_ = lean_st_ref_get(v___y_1395_);
v_env_1403_ = lean_ctor_get(v___x_1402_, 0);
lean_inc_ref(v_env_1403_);
lean_dec(v___x_1402_);
v___x_1404_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1405_ = lean_box(1);
v___x_1406_ = lean_box(0);
v___x_1450_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1397_, v___x_1404_, v_env_1403_, v___x_1405_, v___x_1406_);
v___x_1451_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9___redArg(v___x_1450_, v_entry_1401_);
lean_dec(v___x_1450_);
if (v___x_1451_ == 0)
{
lean_object* v_toCold_1452_; lean_object* v_options_1453_; uint8_t v_hasTrace_1454_; 
v_toCold_1452_ = lean_ctor_get(v___y_1394_, 0);
v_options_1453_ = lean_ctor_get(v_toCold_1452_, 2);
v_hasTrace_1454_ = lean_ctor_get_uint8(v_options_1453_, sizeof(void*)*1);
if (v_hasTrace_1454_ == 0)
{
lean_dec(v_hint_1389_);
lean_dec(v_mod_1387_);
v___y_1408_ = v___y_1393_;
v___y_1409_ = v___y_1395_;
goto v___jp_1407_;
}
else
{
lean_object* v_inheritedTraceOptions_1455_; lean_object* v_cls_1456_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___x_1476_; uint8_t v___x_1477_; 
v_inheritedTraceOptions_1455_ = lean_ctor_get(v_toCold_1452_, 11);
v_cls_1456_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__6));
v___x_1476_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__14);
v___x_1477_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1455_, v_options_1453_, v___x_1476_);
if (v___x_1477_ == 0)
{
lean_dec(v_hint_1389_);
lean_dec(v_mod_1387_);
v___y_1408_ = v___y_1393_;
v___y_1409_ = v___y_1395_;
goto v___jp_1407_;
}
else
{
lean_object* v___x_1478_; lean_object* v___y_1480_; 
v___x_1478_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__16);
if (v_isExporting_1400_ == 0)
{
lean_object* v___x_1487_; 
v___x_1487_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__21));
v___y_1480_ = v___x_1487_;
goto v___jp_1479_;
}
else
{
lean_object* v___x_1488_; 
v___x_1488_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__22));
v___y_1480_ = v___x_1488_;
goto v___jp_1479_;
}
v___jp_1479_:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
lean_inc_ref(v___y_1480_);
v___x_1481_ = l_Lean_stringToMessageData(v___y_1480_);
v___x_1482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1478_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
v___x_1483_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__18);
v___x_1484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1482_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
if (v_isMeta_1388_ == 0)
{
lean_object* v___x_1485_; 
v___x_1485_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__19));
v___y_1463_ = v___x_1484_;
v___y_1464_ = v___x_1485_;
goto v___jp_1462_;
}
else
{
lean_object* v___x_1486_; 
v___x_1486_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__20));
v___y_1463_ = v___x_1484_;
v___y_1464_ = v___x_1486_;
goto v___jp_1462_;
}
}
}
v___jp_1457_:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___y_1458_);
lean_ctor_set(v___x_1460_, 1, v___y_1459_);
v___x_1461_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg(v_cls_1456_, v___x_1460_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_dec_ref_known(v___x_1461_, 1);
v___y_1408_ = v___y_1393_;
v___y_1409_ = v___y_1395_;
goto v___jp_1407_;
}
else
{
lean_dec_ref_known(v_entry_1401_, 1);
return v___x_1461_;
}
}
v___jp_1462_:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; uint8_t v___x_1471_; 
lean_inc_ref(v___y_1464_);
v___x_1465_ = l_Lean_stringToMessageData(v___y_1464_);
v___x_1466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1466_, 0, v___y_1463_);
lean_ctor_set(v___x_1466_, 1, v___x_1465_);
v___x_1467_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__8);
v___x_1468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1466_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
v___x_1469_ = l_Lean_MessageData_ofName(v_mod_1387_);
v___x_1470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1468_);
lean_ctor_set(v___x_1470_, 1, v___x_1469_);
v___x_1471_ = l_Lean_Name_isAnonymous(v_hint_1389_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1472_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__10);
v___x_1473_ = l_Lean_MessageData_ofName(v_hint_1389_);
v___x_1474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1472_);
lean_ctor_set(v___x_1474_, 1, v___x_1473_);
v___y_1458_ = v___x_1470_;
v___y_1459_ = v___x_1474_;
goto v___jp_1457_;
}
else
{
lean_object* v___x_1475_; 
lean_dec(v_hint_1389_);
v___x_1475_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__11);
v___y_1458_ = v___x_1470_;
v___y_1459_ = v___x_1475_;
goto v___jp_1457_;
}
}
}
}
else
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
lean_dec_ref_known(v_entry_1401_, 1);
lean_dec(v_hint_1389_);
lean_dec(v_mod_1387_);
v___x_1489_ = lean_box(0);
v___x_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1490_, 0, v___x_1489_);
return v___x_1490_;
}
v___jp_1407_:
{
lean_object* v___x_1410_; lean_object* v_toEnvExtension_1411_; lean_object* v_env_1412_; lean_object* v_nextMacroScope_1413_; lean_object* v_ngen_1414_; lean_object* v_auxDeclNGen_1415_; lean_object* v_traceState_1416_; lean_object* v_recordedDeps_1417_; lean_object* v_messages_1418_; lean_object* v_infoState_1419_; lean_object* v_snapshotTasks_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1448_; 
v___x_1410_ = lean_st_ref_take(v___y_1409_);
v_toEnvExtension_1411_ = lean_ctor_get(v___x_1404_, 0);
v_env_1412_ = lean_ctor_get(v___x_1410_, 0);
v_nextMacroScope_1413_ = lean_ctor_get(v___x_1410_, 1);
v_ngen_1414_ = lean_ctor_get(v___x_1410_, 2);
v_auxDeclNGen_1415_ = lean_ctor_get(v___x_1410_, 3);
v_traceState_1416_ = lean_ctor_get(v___x_1410_, 4);
v_recordedDeps_1417_ = lean_ctor_get(v___x_1410_, 6);
v_messages_1418_ = lean_ctor_get(v___x_1410_, 7);
v_infoState_1419_ = lean_ctor_get(v___x_1410_, 8);
v_snapshotTasks_1420_ = lean_ctor_get(v___x_1410_, 9);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1448_ == 0)
{
lean_object* v_unused_1449_; 
v_unused_1449_ = lean_ctor_get(v___x_1410_, 5);
lean_dec(v_unused_1449_);
v___x_1422_ = v___x_1410_;
v_isShared_1423_ = v_isSharedCheck_1448_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_snapshotTasks_1420_);
lean_inc(v_infoState_1419_);
lean_inc(v_messages_1418_);
lean_inc(v_recordedDeps_1417_);
lean_inc(v_traceState_1416_);
lean_inc(v_auxDeclNGen_1415_);
lean_inc(v_ngen_1414_);
lean_inc(v_nextMacroScope_1413_);
lean_inc(v_env_1412_);
lean_dec(v___x_1410_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1448_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v_asyncMode_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1428_; 
v_asyncMode_1424_ = lean_ctor_get(v_toEnvExtension_1411_, 2);
v___x_1425_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1404_, v_env_1412_, v_entry_1401_, v_asyncMode_1424_, v___x_1406_);
v___x_1426_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__3);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 5, v___x_1426_);
lean_ctor_set(v___x_1422_, 0, v___x_1425_);
v___x_1428_ = v___x_1422_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1425_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_nextMacroScope_1413_);
lean_ctor_set(v_reuseFailAlloc_1447_, 2, v_ngen_1414_);
lean_ctor_set(v_reuseFailAlloc_1447_, 3, v_auxDeclNGen_1415_);
lean_ctor_set(v_reuseFailAlloc_1447_, 4, v_traceState_1416_);
lean_ctor_set(v_reuseFailAlloc_1447_, 5, v___x_1426_);
lean_ctor_set(v_reuseFailAlloc_1447_, 6, v_recordedDeps_1417_);
lean_ctor_set(v_reuseFailAlloc_1447_, 7, v_messages_1418_);
lean_ctor_set(v_reuseFailAlloc_1447_, 8, v_infoState_1419_);
lean_ctor_set(v_reuseFailAlloc_1447_, 9, v_snapshotTasks_1420_);
v___x_1428_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v_mctx_1431_; lean_object* v_zetaDeltaFVarIds_1432_; lean_object* v_postponed_1433_; lean_object* v_diag_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1445_; 
v___x_1429_ = lean_st_ref_put(v___y_1409_, v___x_1428_);
v___x_1430_ = lean_st_ref_take(v___y_1408_);
v_mctx_1431_ = lean_ctor_get(v___x_1430_, 0);
v_zetaDeltaFVarIds_1432_ = lean_ctor_get(v___x_1430_, 2);
v_postponed_1433_ = lean_ctor_get(v___x_1430_, 3);
v_diag_1434_ = lean_ctor_get(v___x_1430_, 4);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1445_ == 0)
{
lean_object* v_unused_1446_; 
v_unused_1446_ = lean_ctor_get(v___x_1430_, 1);
lean_dec(v_unused_1446_);
v___x_1436_ = v___x_1430_;
v_isShared_1437_ = v_isSharedCheck_1445_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_diag_1434_);
lean_inc(v_postponed_1433_);
lean_inc(v_zetaDeltaFVarIds_1432_);
lean_inc(v_mctx_1431_);
lean_dec(v___x_1430_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1445_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1441_; 
v___x_1438_ = lean_box(0);
v___x_1439_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__4);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 1, v___x_1439_);
v___x_1441_ = v___x_1436_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_mctx_1431_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v___x_1439_);
lean_ctor_set(v_reuseFailAlloc_1444_, 2, v_zetaDeltaFVarIds_1432_);
lean_ctor_set(v_reuseFailAlloc_1444_, 3, v_postponed_1433_);
lean_ctor_set(v_reuseFailAlloc_1444_, 4, v_diag_1434_);
v___x_1441_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1442_ = lean_st_ref_put(v___y_1408_, v___x_1441_);
v___x_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1438_);
return v___x_1443_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___boxed(lean_object* v_mod_1491_, lean_object* v_isMeta_1492_, lean_object* v_hint_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
uint8_t v_isMeta_boxed_1501_; lean_object* v_res_1502_; 
v_isMeta_boxed_1501_ = lean_unbox(v_isMeta_1492_);
v_res_1502_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6(v_mod_1491_, v_isMeta_boxed_1501_, v_hint_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__7(lean_object* v___x_1503_, lean_object* v_declName_1504_, lean_object* v_as_1505_, size_t v_sz_1506_, size_t v_i_1507_, lean_object* v_b_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
uint8_t v___x_1516_; 
v___x_1516_ = lean_usize_dec_lt(v_i_1507_, v_sz_1506_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; 
lean_dec(v_declName_1504_);
v___x_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1517_, 0, v_b_1508_);
return v___x_1517_;
}
else
{
lean_object* v___x_1518_; lean_object* v_modules_1519_; lean_object* v___x_1520_; lean_object* v_a_1521_; lean_object* v___x_1522_; lean_object* v_toImport_1523_; lean_object* v_module_1524_; lean_object* v___x_1525_; uint8_t v___x_1526_; lean_object* v___x_1527_; 
v___x_1518_ = l_Lean_Environment_header(v___x_1503_);
v_modules_1519_ = lean_ctor_get(v___x_1518_, 3);
lean_inc_ref(v_modules_1519_);
lean_dec_ref(v___x_1518_);
v___x_1520_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1521_ = lean_array_uget_borrowed(v_as_1505_, v_i_1507_);
v___x_1522_ = lean_array_get(v___x_1520_, v_modules_1519_, v_a_1521_);
lean_dec_ref(v_modules_1519_);
v_toImport_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc_ref(v_toImport_1523_);
lean_dec(v___x_1522_);
v_module_1524_ = lean_ctor_get(v_toImport_1523_, 0);
lean_inc(v_module_1524_);
lean_dec_ref(v_toImport_1523_);
v___x_1525_ = lean_box(0);
v___x_1526_ = 0;
lean_inc(v_declName_1504_);
v___x_1527_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6(v_module_1524_, v___x_1526_, v_declName_1504_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
if (lean_obj_tag(v___x_1527_) == 0)
{
size_t v___x_1528_; size_t v___x_1529_; 
lean_dec_ref_known(v___x_1527_, 1);
v___x_1528_ = ((size_t)1ULL);
v___x_1529_ = lean_usize_add(v_i_1507_, v___x_1528_);
v_i_1507_ = v___x_1529_;
v_b_1508_ = v___x_1525_;
goto _start;
}
else
{
lean_dec(v_declName_1504_);
return v___x_1527_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__7___boxed(lean_object* v___x_1531_, lean_object* v_declName_1532_, lean_object* v_as_1533_, lean_object* v_sz_1534_, lean_object* v_i_1535_, lean_object* v_b_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
size_t v_sz_boxed_1544_; size_t v_i_boxed_1545_; lean_object* v_res_1546_; 
v_sz_boxed_1544_ = lean_unbox_usize(v_sz_1534_);
lean_dec(v_sz_1534_);
v_i_boxed_1545_ = lean_unbox_usize(v_i_1535_);
lean_dec(v_i_1535_);
v_res_1546_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__7(v___x_1531_, v_declName_1532_, v_as_1533_, v_sz_boxed_1544_, v_i_boxed_1545_, v_b_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec_ref(v_as_1533_);
lean_dec_ref(v___x_1531_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12___redArg(lean_object* v_a_1547_, lean_object* v_x_1548_){
_start:
{
if (lean_obj_tag(v_x_1548_) == 0)
{
lean_object* v___x_1549_; 
v___x_1549_ = lean_box(0);
return v___x_1549_;
}
else
{
lean_object* v_key_1550_; lean_object* v_value_1551_; lean_object* v_tail_1552_; uint8_t v___x_1553_; 
v_key_1550_ = lean_ctor_get(v_x_1548_, 0);
v_value_1551_ = lean_ctor_get(v_x_1548_, 1);
v_tail_1552_ = lean_ctor_get(v_x_1548_, 2);
v___x_1553_ = lean_name_eq(v_key_1550_, v_a_1547_);
if (v___x_1553_ == 0)
{
v_x_1548_ = v_tail_1552_;
goto _start;
}
else
{
lean_object* v___x_1555_; 
lean_inc(v_value_1551_);
v___x_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1555_, 0, v_value_1551_);
return v___x_1555_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12___redArg___boxed(lean_object* v_a_1556_, lean_object* v_x_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12___redArg(v_a_1556_, v_x_1557_);
lean_dec(v_x_1557_);
lean_dec(v_a_1556_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8___redArg(lean_object* v_m_1559_, lean_object* v_a_1560_){
_start:
{
lean_object* v_buckets_1561_; lean_object* v___x_1562_; uint64_t v___y_1564_; 
v_buckets_1561_ = lean_ctor_get(v_m_1559_, 1);
v___x_1562_ = lean_array_get_size(v_buckets_1561_);
if (lean_obj_tag(v_a_1560_) == 0)
{
uint64_t v___x_1578_; 
v___x_1578_ = 1723ULL;
v___y_1564_ = v___x_1578_;
goto v___jp_1563_;
}
else
{
uint64_t v_hash_1579_; 
v_hash_1579_ = lean_ctor_get_uint64(v_a_1560_, sizeof(void*)*2);
v___y_1564_ = v_hash_1579_;
goto v___jp_1563_;
}
v___jp_1563_:
{
uint64_t v___x_1565_; uint64_t v___x_1566_; uint64_t v_fold_1567_; uint64_t v___x_1568_; uint64_t v___x_1569_; uint64_t v___x_1570_; size_t v___x_1571_; size_t v___x_1572_; size_t v___x_1573_; size_t v___x_1574_; size_t v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1565_ = 32ULL;
v___x_1566_ = lean_uint64_shift_right(v___y_1564_, v___x_1565_);
v_fold_1567_ = lean_uint64_xor(v___y_1564_, v___x_1566_);
v___x_1568_ = 16ULL;
v___x_1569_ = lean_uint64_shift_right(v_fold_1567_, v___x_1568_);
v___x_1570_ = lean_uint64_xor(v_fold_1567_, v___x_1569_);
v___x_1571_ = lean_uint64_to_usize(v___x_1570_);
v___x_1572_ = lean_usize_of_nat(v___x_1562_);
v___x_1573_ = ((size_t)1ULL);
v___x_1574_ = lean_usize_sub(v___x_1572_, v___x_1573_);
v___x_1575_ = lean_usize_land(v___x_1571_, v___x_1574_);
v___x_1576_ = lean_array_uget_borrowed(v_buckets_1561_, v___x_1575_);
v___x_1577_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12___redArg(v_a_1560_, v___x_1576_);
return v___x_1577_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_m_1580_, lean_object* v_a_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8___redArg(v_m_1580_, v_a_1581_);
lean_dec(v_a_1581_);
lean_dec_ref(v_m_1580_);
return v_res_1582_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5(lean_object* v_declName_1586_, uint8_t v_isMeta_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v_env_1600_; lean_object* v___y_1602_; lean_object* v___x_1615_; 
v___x_1595_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5___closed__0);
v___x_1596_ = lean_st_ref_get(v___y_1593_);
v_env_1600_ = lean_ctor_get(v___x_1596_, 0);
lean_inc_ref(v_env_1600_);
lean_dec(v___x_1596_);
v___x_1615_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1600_, v_declName_1586_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_dec_ref(v_env_1600_);
lean_dec(v_declName_1586_);
goto v___jp_1597_;
}
else
{
lean_object* v_val_1616_; lean_object* v___x_1617_; lean_object* v_modules_1618_; lean_object* v___x_1619_; uint8_t v___x_1620_; 
v_val_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_val_1616_);
lean_dec_ref_known(v___x_1615_, 1);
v___x_1617_ = l_Lean_Environment_header(v_env_1600_);
v_modules_1618_ = lean_ctor_get(v___x_1617_, 3);
lean_inc_ref(v_modules_1618_);
lean_dec_ref(v___x_1617_);
v___x_1619_ = lean_array_get_size(v_modules_1618_);
v___x_1620_ = lean_nat_dec_lt(v_val_1616_, v___x_1619_);
if (v___x_1620_ == 0)
{
lean_dec_ref(v_modules_1618_);
lean_dec(v_val_1616_);
lean_dec_ref(v_env_1600_);
lean_dec(v_declName_1586_);
goto v___jp_1597_;
}
else
{
lean_object* v___x_1621_; lean_object* v___x_1622_; uint8_t v___y_1624_; 
v___x_1621_ = lean_array_fget(v_modules_1618_, v_val_1616_);
lean_dec(v_val_1616_);
lean_dec_ref(v_modules_1618_);
v___x_1622_ = lean_st_ref_get(v___y_1593_);
if (v_isMeta_1587_ == 0)
{
lean_dec(v___x_1622_);
v___y_1624_ = v_isMeta_1587_;
goto v___jp_1623_;
}
else
{
lean_object* v_env_1635_; uint8_t v___x_1636_; 
v_env_1635_ = lean_ctor_get(v___x_1622_, 0);
lean_inc_ref(v_env_1635_);
lean_dec(v___x_1622_);
lean_inc(v_declName_1586_);
v___x_1636_ = l_Lean_isMarkedMeta(v_env_1635_, v_declName_1586_);
if (v___x_1636_ == 0)
{
v___y_1624_ = v_isMeta_1587_;
goto v___jp_1623_;
}
else
{
uint8_t v___x_1637_; 
v___x_1637_ = 0;
v___y_1624_ = v___x_1637_;
goto v___jp_1623_;
}
}
v___jp_1623_:
{
lean_object* v_toImport_1625_; lean_object* v_module_1626_; lean_object* v___x_1627_; 
v_toImport_1625_ = lean_ctor_get(v___x_1621_, 0);
lean_inc_ref(v_toImport_1625_);
lean_dec(v___x_1621_);
v_module_1626_ = lean_ctor_get(v_toImport_1625_, 0);
lean_inc(v_module_1626_);
lean_dec_ref(v_toImport_1625_);
lean_inc(v_declName_1586_);
v___x_1627_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6(v_module_1626_, v___y_1624_, v_declName_1586_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
lean_dec_ref_known(v___x_1627_, 1);
v___x_1628_ = l_Lean_indirectModUseExt;
v___x_1629_ = lean_box(1);
v___x_1630_ = lean_box(0);
lean_inc_ref(v_env_1600_);
v___x_1631_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1595_, v___x_1628_, v_env_1600_, v___x_1629_, v___x_1630_);
v___x_1632_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8___redArg(v___x_1631_, v_declName_1586_);
lean_dec(v___x_1631_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v___x_1633_; 
v___x_1633_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5___closed__1));
v___y_1602_ = v___x_1633_;
goto v___jp_1601_;
}
else
{
lean_object* v_val_1634_; 
v_val_1634_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_val_1634_);
lean_dec_ref_known(v___x_1632_, 1);
v___y_1602_ = v_val_1634_;
goto v___jp_1601_;
}
}
else
{
lean_dec_ref(v_env_1600_);
lean_dec(v_declName_1586_);
return v___x_1627_;
}
}
}
}
v___jp_1597_:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = lean_box(0);
v___x_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1598_);
return v___x_1599_;
}
v___jp_1601_:
{
lean_object* v___x_1603_; size_t v_sz_1604_; size_t v___x_1605_; lean_object* v___x_1606_; 
v___x_1603_ = lean_box(0);
v_sz_1604_ = lean_array_size(v___y_1602_);
v___x_1605_ = ((size_t)0ULL);
v___x_1606_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__7(v_env_1600_, v_declName_1586_, v___y_1602_, v_sz_1604_, v___x_1605_, v___x_1603_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
lean_dec_ref(v___y_1602_);
lean_dec_ref(v_env_1600_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1613_ == 0)
{
lean_object* v_unused_1614_; 
v_unused_1614_ = lean_ctor_get(v___x_1606_, 0);
lean_dec(v_unused_1614_);
v___x_1608_ = v___x_1606_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_dec(v___x_1606_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 0, v___x_1603_);
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1603_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
else
{
return v___x_1606_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5___boxed(lean_object* v_declName_1638_, lean_object* v_isMeta_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
uint8_t v_isMeta_boxed_1647_; lean_object* v_res_1648_; 
v_isMeta_boxed_1647_ = lean_unbox(v_isMeta_1639_);
v_res_1648_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5(v_declName_1638_, v_isMeta_boxed_1647_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6___redArg(lean_object* v_as_x27_1649_, lean_object* v_b_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
if (lean_obj_tag(v_as_x27_1649_) == 0)
{
lean_object* v___x_1658_; 
v___x_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1658_, 0, v_b_1650_);
return v___x_1658_;
}
else
{
lean_object* v_head_1659_; lean_object* v_tail_1660_; lean_object* v___x_1661_; uint8_t v___x_1662_; lean_object* v___x_1663_; 
v_head_1659_ = lean_ctor_get(v_as_x27_1649_, 0);
v_tail_1660_ = lean_ctor_get(v_as_x27_1649_, 1);
v___x_1661_ = lean_box(0);
v___x_1662_ = 1;
lean_inc(v_head_1659_);
v___x_1663_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5(v_head_1659_, v___x_1662_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_dec_ref_known(v___x_1663_, 1);
v_as_x27_1649_ = v_tail_1660_;
v_b_1650_ = v___x_1661_;
goto _start;
}
else
{
return v___x_1663_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6___redArg___boxed(lean_object* v_as_x27_1665_, lean_object* v_b_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6___redArg(v_as_x27_1665_, v_b_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v_as_x27_1665_);
return v_res_1674_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = l_Lean_maxRecDepthErrorMessage;
v___x_1681_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
return v___x_1681_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__4(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__3);
v___x_1683_ = l_Lean_MessageData_ofFormat(v___x_1682_);
return v___x_1683_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1684_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__4);
v___x_1685_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__2));
v___x_1686_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1685_);
lean_ctor_set(v___x_1686_, 1, v___x_1684_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg(lean_object* v_ref_1687_){
_start:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1689_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__5);
v___x_1690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1690_, 0, v_ref_1687_);
lean_ctor_set(v___x_1690_, 1, v___x_1689_);
v___x_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1690_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___boxed(lean_object* v_ref_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg(v_ref_1692_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__2(lean_object* v_currNamespace_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1698_, 0, v_currNamespace_1695_);
lean_ctor_set(v___x_1698_, 1, v___y_1697_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__2___boxed(lean_object* v_currNamespace_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__2(v_currNamespace_1699_, v___y_1700_, v___y_1701_);
lean_dec_ref(v___y_1700_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__0(lean_object* v_env_1703_, lean_object* v_declName_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
uint8_t v___x_1707_; lean_object* v_env_1708_; lean_object* v___x_1709_; uint8_t v___x_1710_; uint8_t v___x_1711_; 
v___x_1707_ = 0;
v_env_1708_ = l_Lean_Environment_setExporting(v_env_1703_, v___x_1707_);
lean_inc(v_declName_1704_);
v___x_1709_ = l_Lean_mkPrivateName(v_env_1708_, v_declName_1704_);
v___x_1710_ = 1;
lean_inc_ref(v_env_1708_);
v___x_1711_ = l_Lean_Environment_contains(v_env_1708_, v___x_1709_, v___x_1710_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; uint8_t v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1712_ = l_Lean_privateToUserName(v_declName_1704_);
v___x_1713_ = l_Lean_Environment_contains(v_env_1708_, v___x_1712_, v___x_1710_);
v___x_1714_ = lean_box(v___x_1713_);
v___x_1715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1714_);
lean_ctor_set(v___x_1715_, 1, v___y_1706_);
return v___x_1715_;
}
else
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
lean_dec_ref(v_env_1708_);
lean_dec(v_declName_1704_);
v___x_1716_ = lean_box(v___x_1711_);
v___x_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1716_);
lean_ctor_set(v___x_1717_, 1, v___y_1706_);
return v___x_1717_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__0___boxed(lean_object* v_env_1718_, lean_object* v_declName_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__0(v_env_1718_, v_declName_1719_, v___y_1720_, v___y_1721_);
lean_dec_ref(v___y_1720_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__4(lean_object* v_env_1723_, lean_object* v_currNamespace_1724_, lean_object* v_openDecls_1725_, lean_object* v_n_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1729_ = l_Lean_ResolveName_resolveNamespace(v_env_1723_, v_currNamespace_1724_, v_openDecls_1725_, v_n_1726_);
v___x_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
lean_ctor_set(v___x_1730_, 1, v___y_1728_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__4___boxed(lean_object* v_env_1731_, lean_object* v_currNamespace_1732_, lean_object* v_openDecls_1733_, lean_object* v_n_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__4(v_env_1731_, v_currNamespace_1732_, v_openDecls_1733_, v_n_1734_, v___y_1735_, v___y_1736_);
lean_dec_ref(v___y_1735_);
return v_res_1737_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1738_ = lean_box(0);
v___x_1739_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1739_);
lean_ctor_set(v___x_1740_, 1, v___x_1738_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg(){
_start:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg___closed__0);
v___x_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1743_, 0, v___x_1742_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg___boxed(lean_object* v___y_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg();
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__7(lean_object* v_as_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
if (lean_obj_tag(v_as_1746_) == 0)
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1754_ = lean_box(0);
v___x_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
return v___x_1755_;
}
else
{
lean_object* v_toCold_1756_; lean_object* v_options_1757_; uint8_t v_hasTrace_1758_; 
v_toCold_1756_ = lean_ctor_get(v___y_1751_, 0);
v_options_1757_ = lean_ctor_get(v_toCold_1756_, 2);
v_hasTrace_1758_ = lean_ctor_get_uint8(v_options_1757_, sizeof(void*)*1);
if (v_hasTrace_1758_ == 0)
{
lean_object* v_tail_1759_; 
v_tail_1759_ = lean_ctor_get(v_as_1746_, 1);
lean_inc(v_tail_1759_);
lean_dec_ref_known(v_as_1746_, 2);
v_as_1746_ = v_tail_1759_;
goto _start;
}
else
{
lean_object* v_head_1761_; lean_object* v_tail_1762_; lean_object* v_fst_1763_; lean_object* v_snd_1764_; lean_object* v_inheritedTraceOptions_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; 
v_head_1761_ = lean_ctor_get(v_as_1746_, 0);
lean_inc(v_head_1761_);
v_tail_1762_ = lean_ctor_get(v_as_1746_, 1);
lean_inc(v_tail_1762_);
lean_dec_ref_known(v_as_1746_, 2);
v_fst_1763_ = lean_ctor_get(v_head_1761_, 0);
lean_inc_n(v_fst_1763_, 2);
v_snd_1764_ = lean_ctor_get(v_head_1761_, 1);
lean_inc(v_snd_1764_);
lean_dec(v_head_1761_);
v_inheritedTraceOptions_1765_ = lean_ctor_get(v_toCold_1756_, 11);
v___x_1766_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__13));
v___x_1767_ = l_Lean_Name_append(v___x_1766_, v_fst_1763_);
v___x_1768_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1765_, v_options_1757_, v___x_1767_);
lean_dec(v___x_1767_);
if (v___x_1768_ == 0)
{
lean_dec(v_snd_1764_);
lean_dec(v_fst_1763_);
v_as_1746_ = v_tail_1762_;
goto _start;
}
else
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1770_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1770_, 0, v_snd_1764_);
v___x_1771_ = l_Lean_MessageData_ofFormat(v___x_1770_);
v___x_1772_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg(v_fst_1763_, v___x_1771_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_dec_ref_known(v___x_1772_, 1);
v_as_1746_ = v_tail_1762_;
goto _start;
}
else
{
lean_dec(v_tail_1762_);
return v___x_1772_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__7___boxed(lean_object* v_as_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__7(v_as_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__3(lean_object* v_env_1783_, lean_object* v___x_1784_, lean_object* v_currNamespace_1785_, lean_object* v_openDecls_1786_, lean_object* v_n_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1790_ = l_Lean_ResolveName_resolveGlobalName(v_env_1783_, v___x_1784_, v_currNamespace_1785_, v_openDecls_1786_, v_n_1787_);
v___x_1791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1790_);
lean_ctor_set(v___x_1791_, 1, v___y_1789_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__3___boxed(lean_object* v_env_1792_, lean_object* v___x_1793_, lean_object* v_currNamespace_1794_, lean_object* v_openDecls_1795_, lean_object* v_n_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__3(v_env_1792_, v___x_1793_, v_currNamespace_1794_, v_openDecls_1795_, v_n_1796_, v___y_1797_, v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec_ref(v___x_1793_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8___redArg(lean_object* v_ref_1800_, lean_object* v_msg_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v_toCold_1809_; lean_object* v_currRecDepth_1810_; lean_object* v_ref_1811_; uint16_t v_optionFlags_1812_; uint8_t v_suppressElabErrors_1813_; uint8_t v_isRecordingDeps_1814_; lean_object* v_ref_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v_toCold_1809_ = lean_ctor_get(v___y_1806_, 0);
v_currRecDepth_1810_ = lean_ctor_get(v___y_1806_, 1);
v_ref_1811_ = lean_ctor_get(v___y_1806_, 2);
v_optionFlags_1812_ = lean_ctor_get_uint16(v___y_1806_, sizeof(void*)*3);
v_suppressElabErrors_1813_ = lean_ctor_get_uint8(v___y_1806_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1814_ = lean_ctor_get_uint8(v___y_1806_, sizeof(void*)*3 + 3);
v_ref_1815_ = l_Lean_replaceRef(v_ref_1800_, v_ref_1811_);
lean_inc(v_currRecDepth_1810_);
lean_inc_ref(v_toCold_1809_);
v___x_1816_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1816_, 0, v_toCold_1809_);
lean_ctor_set(v___x_1816_, 1, v_currRecDepth_1810_);
lean_ctor_set(v___x_1816_, 2, v_ref_1815_);
lean_ctor_set_uint16(v___x_1816_, sizeof(void*)*3, v_optionFlags_1812_);
lean_ctor_set_uint8(v___x_1816_, sizeof(void*)*3 + 2, v_suppressElabErrors_1813_);
lean_ctor_set_uint8(v___x_1816_, sizeof(void*)*3 + 3, v_isRecordingDeps_1814_);
v___x_1817_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg(v_msg_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___x_1816_, v___y_1807_);
lean_dec_ref_known(v___x_1816_, 3);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8___redArg___boxed(lean_object* v_ref_1818_, lean_object* v_msg_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8___redArg(v_ref_1818_, v_msg_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v_ref_1818_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___redArg(lean_object* v_x_1828_, lean_object* v___y_1829_){
_start:
{
if (lean_obj_tag(v_x_1828_) == 0)
{
lean_object* v_a_1830_; lean_object* v___x_1831_; 
v_a_1830_ = lean_ctor_get(v_x_1828_, 0);
lean_inc(v_a_1830_);
v___x_1831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1831_, 0, v_a_1830_);
lean_ctor_set(v___x_1831_, 1, v___y_1829_);
return v___x_1831_;
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1833_; 
v_a_1832_ = lean_ctor_get(v_x_1828_, 0);
lean_inc(v_a_1832_);
v___x_1833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1833_, 0, v_a_1832_);
lean_ctor_set(v___x_1833_, 1, v___y_1829_);
return v___x_1833_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___redArg___boxed(lean_object* v_x_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___redArg(v_x_1834_, v___y_1835_);
lean_dec_ref(v_x_1834_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__1(lean_object* v_env_1837_, lean_object* v_stx_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1837_, v_stx_1838_, v___y_1839_, v___y_1840_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_a_1842_);
if (lean_obj_tag(v_a_1842_) == 0)
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1851_; 
v_a_1843_ = lean_ctor_get(v___x_1841_, 1);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1851_ == 0)
{
lean_object* v_unused_1852_; 
v_unused_1852_ = lean_ctor_get(v___x_1841_, 0);
lean_dec(v_unused_1852_);
v___x_1845_ = v___x_1841_;
v_isShared_1846_ = v_isSharedCheck_1851_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1841_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1851_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1847_; lean_object* v___x_1849_; 
v___x_1847_ = lean_box(0);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 0, v___x_1847_);
v___x_1849_ = v___x_1845_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1847_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_a_1843_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
else
{
lean_object* v_val_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1881_; 
v_val_1853_ = lean_ctor_get(v_a_1842_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v_a_1842_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1855_ = v_a_1842_;
v_isShared_1856_ = v_isSharedCheck_1881_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_val_1853_);
lean_dec(v_a_1842_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1881_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v_snd_1857_; 
v_snd_1857_ = lean_ctor_get(v_val_1853_, 1);
lean_inc(v_snd_1857_);
lean_dec(v_val_1853_);
if (lean_obj_tag(v_snd_1857_) == 0)
{
lean_object* v_a_1858_; lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1867_; 
lean_del_object(v___x_1855_);
v_a_1858_ = lean_ctor_get(v___x_1841_, 1);
lean_inc(v_a_1858_);
lean_dec_ref_known(v___x_1841_, 2);
v_a_1859_ = lean_ctor_get(v_snd_1857_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v_snd_1857_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1861_ = v_snd_1857_;
v_isShared_1862_ = v_isSharedCheck_1867_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v_snd_1857_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1867_;
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
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___redArg(v___x_1864_, v_a_1858_);
lean_dec_ref(v___x_1864_);
return v___x_1865_;
}
}
}
else
{
lean_object* v_a_1868_; lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1880_; 
v_a_1868_ = lean_ctor_get(v___x_1841_, 1);
lean_inc(v_a_1868_);
lean_dec_ref_known(v___x_1841_, 2);
v_a_1869_ = lean_ctor_get(v_snd_1857_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v_snd_1857_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1871_ = v_snd_1857_;
v_isShared_1872_ = v_isSharedCheck_1880_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v_snd_1857_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1880_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 0, v_a_1869_);
v___x_1874_ = v___x_1855_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
lean_object* v___x_1876_; 
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 0, v___x_1874_);
v___x_1876_ = v___x_1871_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1874_);
v___x_1876_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
lean_object* v___x_1877_; 
v___x_1877_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___redArg(v___x_1876_, v_a_1868_);
lean_dec_ref(v___x_1876_);
return v___x_1877_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1882_; lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
v_a_1882_ = lean_ctor_get(v___x_1841_, 0);
v_a_1883_ = lean_ctor_get(v___x_1841_, 1);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1841_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_inc(v_a_1882_);
lean_dec(v___x_1841_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1882_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v_a_1883_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__1___boxed(lean_object* v_env_1891_, lean_object* v_stx_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__1(v_env_1891_, v_stx_1892_, v___y_1893_, v___y_1894_);
lean_dec_ref(v___y_1893_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg(lean_object* v_x_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v___x_1905_; lean_object* v_toCold_1906_; lean_object* v_env_1907_; lean_object* v_currRecDepth_1908_; lean_object* v_ref_1909_; lean_object* v_maxRecDepth_1910_; lean_object* v_currNamespace_1911_; lean_object* v_openDecls_1912_; lean_object* v_quotContext_1913_; lean_object* v_currMacroScope_1914_; lean_object* v___f_1915_; lean_object* v___f_1916_; lean_object* v___x_1917_; lean_object* v___f_1918_; lean_object* v___f_1919_; lean_object* v___f_1920_; lean_object* v_methods_1921_; lean_object* v___x_1922_; lean_object* v_nextMacroScope_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1905_ = lean_st_ref_get(v___y_1903_);
v_toCold_1906_ = lean_ctor_get(v___y_1902_, 0);
v_env_1907_ = lean_ctor_get(v___x_1905_, 0);
lean_inc_ref_n(v_env_1907_, 4);
lean_dec(v___x_1905_);
v_currRecDepth_1908_ = lean_ctor_get(v___y_1902_, 1);
v_ref_1909_ = lean_ctor_get(v___y_1902_, 2);
v_maxRecDepth_1910_ = lean_ctor_get(v_toCold_1906_, 3);
v_currNamespace_1911_ = lean_ctor_get(v_toCold_1906_, 4);
v_openDecls_1912_ = lean_ctor_get(v_toCold_1906_, 5);
v_quotContext_1913_ = lean_ctor_get(v_toCold_1906_, 8);
v_currMacroScope_1914_ = lean_ctor_get(v_toCold_1906_, 9);
v___f_1915_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1915_, 0, v_env_1907_);
v___f_1916_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1916_, 0, v_env_1907_);
v___x_1917_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1902_);
lean_inc_n(v_currNamespace_1911_, 3);
v___f_1918_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1918_, 0, v_currNamespace_1911_);
lean_inc_n(v_openDecls_1912_, 2);
v___f_1919_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__3___boxed), 7, 4);
lean_closure_set(v___f_1919_, 0, v_env_1907_);
lean_closure_set(v___f_1919_, 1, v___x_1917_);
lean_closure_set(v___f_1919_, 2, v_currNamespace_1911_);
lean_closure_set(v___f_1919_, 3, v_openDecls_1912_);
v___f_1920_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_1920_, 0, v_env_1907_);
lean_closure_set(v___f_1920_, 1, v_currNamespace_1911_);
lean_closure_set(v___f_1920_, 2, v_openDecls_1912_);
v_methods_1921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1921_, 0, v___f_1916_);
lean_ctor_set(v_methods_1921_, 1, v___f_1918_);
lean_ctor_set(v_methods_1921_, 2, v___f_1915_);
lean_ctor_set(v_methods_1921_, 3, v___f_1920_);
lean_ctor_set(v_methods_1921_, 4, v___f_1919_);
v___x_1922_ = lean_st_ref_get(v___y_1903_);
v_nextMacroScope_1923_ = lean_ctor_get(v___x_1922_, 1);
lean_inc(v_nextMacroScope_1923_);
lean_dec(v___x_1922_);
lean_inc(v_ref_1909_);
lean_inc(v_maxRecDepth_1910_);
lean_inc(v_currRecDepth_1908_);
lean_inc(v_currMacroScope_1914_);
lean_inc(v_quotContext_1913_);
v___x_1924_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1924_, 0, v_methods_1921_);
lean_ctor_set(v___x_1924_, 1, v_quotContext_1913_);
lean_ctor_set(v___x_1924_, 2, v_currMacroScope_1914_);
lean_ctor_set(v___x_1924_, 3, v_currRecDepth_1908_);
lean_ctor_set(v___x_1924_, 4, v_maxRecDepth_1910_);
lean_ctor_set(v___x_1924_, 5, v_ref_1909_);
v___x_1925_ = lean_box(0);
v___x_1926_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1926_, 0, v_nextMacroScope_1923_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
lean_ctor_set(v___x_1926_, 2, v___x_1925_);
v___x_1927_ = lean_apply_2(v_x_1897_, v___x_1924_, v___x_1926_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v_a_1929_; lean_object* v_macroScope_1930_; lean_object* v_traceMsgs_1931_; lean_object* v_expandedMacroDecls_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 1);
lean_inc(v_a_1928_);
v_a_1929_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1929_);
lean_dec_ref_known(v___x_1927_, 2);
v_macroScope_1930_ = lean_ctor_get(v_a_1928_, 0);
lean_inc(v_macroScope_1930_);
v_traceMsgs_1931_ = lean_ctor_get(v_a_1928_, 1);
lean_inc(v_traceMsgs_1931_);
v_expandedMacroDecls_1932_ = lean_ctor_get(v_a_1928_, 2);
lean_inc(v_expandedMacroDecls_1932_);
lean_dec(v_a_1928_);
v___x_1933_ = lean_box(0);
v___x_1934_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6___redArg(v_expandedMacroDecls_1932_, v___x_1933_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec(v_expandedMacroDecls_1932_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v___x_1935_; lean_object* v_env_1936_; lean_object* v_ngen_1937_; lean_object* v_auxDeclNGen_1938_; lean_object* v_traceState_1939_; lean_object* v_cache_1940_; lean_object* v_recordedDeps_1941_; lean_object* v_messages_1942_; lean_object* v_infoState_1943_; lean_object* v_snapshotTasks_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1970_; 
lean_dec_ref_known(v___x_1934_, 1);
v___x_1935_ = lean_st_ref_take(v___y_1903_);
v_env_1936_ = lean_ctor_get(v___x_1935_, 0);
v_ngen_1937_ = lean_ctor_get(v___x_1935_, 2);
v_auxDeclNGen_1938_ = lean_ctor_get(v___x_1935_, 3);
v_traceState_1939_ = lean_ctor_get(v___x_1935_, 4);
v_cache_1940_ = lean_ctor_get(v___x_1935_, 5);
v_recordedDeps_1941_ = lean_ctor_get(v___x_1935_, 6);
v_messages_1942_ = lean_ctor_get(v___x_1935_, 7);
v_infoState_1943_ = lean_ctor_get(v___x_1935_, 8);
v_snapshotTasks_1944_ = lean_ctor_get(v___x_1935_, 9);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1970_ == 0)
{
lean_object* v_unused_1971_; 
v_unused_1971_ = lean_ctor_get(v___x_1935_, 1);
lean_dec(v_unused_1971_);
v___x_1946_ = v___x_1935_;
v_isShared_1947_ = v_isSharedCheck_1970_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_snapshotTasks_1944_);
lean_inc(v_infoState_1943_);
lean_inc(v_messages_1942_);
lean_inc(v_recordedDeps_1941_);
lean_inc(v_cache_1940_);
lean_inc(v_traceState_1939_);
lean_inc(v_auxDeclNGen_1938_);
lean_inc(v_ngen_1937_);
lean_inc(v_env_1936_);
lean_dec(v___x_1935_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1970_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 1, v_macroScope_1930_);
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_env_1936_);
lean_ctor_set(v_reuseFailAlloc_1969_, 1, v_macroScope_1930_);
lean_ctor_set(v_reuseFailAlloc_1969_, 2, v_ngen_1937_);
lean_ctor_set(v_reuseFailAlloc_1969_, 3, v_auxDeclNGen_1938_);
lean_ctor_set(v_reuseFailAlloc_1969_, 4, v_traceState_1939_);
lean_ctor_set(v_reuseFailAlloc_1969_, 5, v_cache_1940_);
lean_ctor_set(v_reuseFailAlloc_1969_, 6, v_recordedDeps_1941_);
lean_ctor_set(v_reuseFailAlloc_1969_, 7, v_messages_1942_);
lean_ctor_set(v_reuseFailAlloc_1969_, 8, v_infoState_1943_);
lean_ctor_set(v_reuseFailAlloc_1969_, 9, v_snapshotTasks_1944_);
v___x_1949_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1950_ = lean_st_ref_put(v___y_1903_, v___x_1949_);
v___x_1951_ = l_List_reverse___redArg(v_traceMsgs_1931_);
v___x_1952_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__7(v___x_1951_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_1959_ == 0)
{
lean_object* v_unused_1960_; 
v_unused_1960_ = lean_ctor_get(v___x_1952_, 0);
lean_dec(v_unused_1960_);
v___x_1954_ = v___x_1952_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_dec(v___x_1952_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 0, v_a_1929_);
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1929_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
lean_dec(v_a_1929_);
v_a_1961_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1952_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1952_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
}
}
else
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
lean_dec(v_traceMsgs_1931_);
lean_dec(v_macroScope_1930_);
lean_dec(v_a_1929_);
v_a_1972_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1934_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1934_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
else
{
lean_object* v_a_1980_; 
v_a_1980_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1980_);
lean_dec_ref_known(v___x_1927_, 2);
if (lean_obj_tag(v_a_1980_) == 0)
{
lean_object* v_a_1981_; lean_object* v_a_1982_; lean_object* v___x_1983_; uint8_t v___x_1984_; 
v_a_1981_ = lean_ctor_get(v_a_1980_, 0);
lean_inc(v_a_1981_);
v_a_1982_ = lean_ctor_get(v_a_1980_, 1);
lean_inc_ref(v_a_1982_);
lean_dec_ref_known(v_a_1980_, 2);
v___x_1983_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___closed__0));
v___x_1984_ = lean_string_dec_eq(v_a_1982_, v___x_1983_);
if (v___x_1984_ == 0)
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1985_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1985_, 0, v_a_1982_);
v___x_1986_ = l_Lean_MessageData_ofFormat(v___x_1985_);
v___x_1987_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8___redArg(v_a_1981_, v___x_1986_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec(v_a_1981_);
return v___x_1987_;
}
else
{
lean_object* v___x_1988_; 
lean_dec_ref(v_a_1982_);
v___x_1988_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg(v_a_1981_);
return v___x_1988_;
}
}
else
{
lean_object* v___x_1989_; 
v___x_1989_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg();
return v___x_1989_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___boxed(lean_object* v_x_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg(v_x_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
return v_res_1998_;
}
}
static lean_object* _init_l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__1(void){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__0));
v___x_2001_ = l_Lean_stringToMessageData(v___x_2000_);
return v___x_2001_;
}
}
static lean_object* _init_l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__6(void){
_start:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__5));
v___x_2011_ = l_Lean_stringToMessageData(v___x_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f(lean_object* v_e_2012_, lean_object* v_dec_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = l_Lean_Elab_Do_Forward_matchApp_x3f(v_e_2012_);
if (lean_obj_tag(v___x_2022_) == 1)
{
lean_object* v_val_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2193_; 
v_val_2023_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2025_ = v___x_2022_;
v_isShared_2026_ = v_isSharedCheck_2193_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_val_2023_);
lean_dec(v___x_2022_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2193_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v_fst_2027_; lean_object* v_snd_2028_; lean_object* v___f_2029_; lean_object* v___x_2030_; 
v_fst_2027_ = lean_ctor_get(v_val_2023_, 0);
lean_inc_n(v_fst_2027_, 2);
v_snd_2028_ = lean_ctor_get(v_val_2023_, 1);
lean_inc(v_snd_2028_);
lean_dec(v_val_2023_);
lean_inc(v_a_2018_);
lean_inc_ref(v_a_2017_);
lean_inc(v_a_2016_);
lean_inc_ref(v_a_2015_);
v___f_2029_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___boxed), 8, 5);
lean_closure_set(v___f_2029_, 0, v_a_2015_);
lean_closure_set(v___f_2029_, 1, v_a_2016_);
lean_closure_set(v___f_2029_, 2, v_a_2017_);
lean_closure_set(v___f_2029_, 3, v_a_2018_);
lean_closure_set(v___f_2029_, 4, v_fst_2027_);
v___x_2030_ = l_Lean_Core_withFreshMacroScope___redArg(v___f_2029_, v_a_2019_, v_a_2020_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v_a_2031_; lean_object* v_fst_2032_; lean_object* v_snd_2033_; lean_object* v___x_2034_; 
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
lean_inc(v_a_2031_);
lean_dec_ref_known(v___x_2030_, 1);
v_fst_2032_ = lean_ctor_get(v_a_2031_, 0);
lean_inc_n(v_fst_2032_, 2);
v_snd_2033_ = lean_ctor_get(v_a_2031_, 1);
lean_inc_n(v_snd_2033_, 2);
lean_dec(v_a_2031_);
v___x_2034_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder(v_fst_2027_, v_fst_2032_, v_snd_2033_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_binders_2035_; lean_object* v_body_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2176_; 
lean_dec_ref_known(v___x_2034_, 1);
v_binders_2035_ = lean_ctor_get(v_snd_2028_, 0);
v_body_2036_ = lean_ctor_get(v_snd_2028_, 1);
v_isSharedCheck_2176_ = !lean_is_exclusive(v_snd_2028_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2038_ = v_snd_2028_;
v_isShared_2039_ = v_isSharedCheck_2176_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_body_2036_);
lean_inc(v_binders_2035_);
lean_dec(v_snd_2028_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2176_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___f_2040_; lean_object* v___x_2041_; 
lean_inc(v_body_2036_);
v___f_2040_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__1___boxed), 10, 1);
lean_closure_set(v___f_2040_, 0, v_body_2036_);
v___x_2041_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_body_2036_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2043_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2042_);
lean_dec_ref_known(v___x_2041_, 1);
v___x_2043_ = l_Lean_Elab_Do_EffectForwarder_ofCont(v_a_2042_, v_dec_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_);
lean_dec(v_a_2042_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2051_; lean_object* v___y_2052_; lean_object* v___y_2084_; lean_object* v___f_2116_; lean_object* v___x_2117_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc_n(v_a_2044_, 2);
lean_dec_ref_known(v___x_2043_, 1);
lean_inc_ref(v_a_2014_);
v___f_2116_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__2___boxed), 12, 3);
lean_closure_set(v___f_2116_, 0, v_a_2044_);
lean_closure_set(v___f_2116_, 1, v___f_2040_);
lean_closure_set(v___f_2116_, 2, v_a_2014_);
lean_inc(v_a_2020_);
lean_inc_ref(v_a_2019_);
lean_inc(v_a_2018_);
lean_inc_ref(v_a_2017_);
lean_inc(v_fst_2032_);
v___x_2117_ = lean_infer_type(v_fst_2032_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_a_2118_; lean_object* v___x_2119_; lean_object* v_a_2120_; lean_object* v_ref_2121_; uint8_t v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2127_; 
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_a_2118_);
lean_dec_ref_known(v___x_2117_, 1);
v___x_2119_ = l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___redArg(v_a_2118_, v_a_2018_);
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_a_2120_);
lean_dec_ref(v___x_2119_);
v_ref_2121_ = lean_ctor_get(v_a_2019_, 2);
v___x_2122_ = 0;
v___x_2123_ = l_Lean_SourceInfo_fromRef(v_ref_2121_, v___x_2122_);
v___x_2124_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__3));
v___x_2125_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__4));
lean_inc(v___x_2123_);
if (v_isShared_2039_ == 0)
{
lean_ctor_set_tag(v___x_2038_, 2);
lean_ctor_set(v___x_2038_, 1, v___x_2125_);
lean_ctor_set(v___x_2038_, 0, v___x_2123_);
v___x_2127_ = v___x_2038_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2123_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v___x_2125_);
v___x_2127_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
lean_object* v___x_2128_; size_t v_sz_2129_; size_t v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2128_ = l_Lean_Syntax_node1(v___x_2123_, v___x_2124_, v___x_2127_);
v_sz_2129_ = lean_array_size(v_binders_2035_);
v___x_2130_ = ((size_t)0ULL);
v___x_2131_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__2(v_sz_2129_, v___x_2130_, v_binders_2035_);
v___x_2132_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandFunBinders___boxed), 4, 2);
lean_closure_set(v___x_2132_, 0, v___x_2131_);
lean_closure_set(v___x_2132_, 1, v___x_2128_);
v___x_2133_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg(v___x_2132_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v_snd_2135_; lean_object* v_snd_2136_; uint8_t v___x_2137_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_a_2134_);
lean_dec_ref_known(v___x_2133_, 1);
v_snd_2135_ = lean_ctor_get(v_a_2134_, 1);
v_snd_2136_ = lean_ctor_get(v_snd_2135_, 1);
v___x_2137_ = lean_unbox(v_snd_2136_);
if (v___x_2137_ == 0)
{
lean_object* v_fst_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v_fst_2138_ = lean_ctor_get(v_a_2134_, 0);
lean_inc(v_fst_2138_);
lean_dec(v_a_2134_);
v___x_2139_ = lean_box(0);
v___x_2140_ = l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__3(v_a_2120_, v_fst_2138_, v___f_2116_, v___x_2139_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_);
lean_dec(v_fst_2138_);
v___y_2084_ = v___x_2140_;
goto v___jp_2083_;
}
else
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v_a_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2150_; 
lean_dec(v_a_2134_);
lean_dec(v_a_2120_);
lean_dec_ref(v___f_2116_);
lean_dec(v_a_2044_);
lean_dec(v_snd_2033_);
lean_dec(v_fst_2032_);
lean_del_object(v___x_2025_);
v___x_2141_ = lean_obj_once(&l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__6, &l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__6_once, _init_l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__6);
v___x_2142_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg(v___x_2141_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_);
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2145_ = v___x_2142_;
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_a_2143_);
lean_dec(v___x_2142_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2148_; 
if (v_isShared_2146_ == 0)
{
v___x_2148_ = v___x_2145_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_a_2143_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_dec(v_a_2120_);
lean_dec_ref(v___f_2116_);
lean_dec(v_a_2044_);
lean_dec(v_snd_2033_);
lean_dec(v_fst_2032_);
lean_del_object(v___x_2025_);
v_a_2151_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2133_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2133_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
}
else
{
lean_dec_ref(v___f_2116_);
lean_del_object(v___x_2038_);
lean_dec_ref(v_binders_2035_);
v___y_2084_ = v___x_2117_;
goto v___jp_2083_;
}
v___jp_2045_:
{
lean_object* v___x_2053_; 
v___x_2053_ = l_Lean_Elab_Do_EffectForwarder_restoreCont(v_a_2044_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_a_2054_; lean_object* v___x_2055_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_a_2054_);
lean_dec_ref_known(v___x_2053_, 1);
v___x_2055_ = l_Lean_Elab_Do_DoElemCont_mkBindUnlessPure(v_a_2054_, v_snd_2033_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2066_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2058_ = v___x_2055_;
v_isShared_2059_ = v_isSharedCheck_2066_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2055_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2066_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 0, v_a_2056_);
v___x_2061_ = v___x_2025_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2056_);
v___x_2061_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
lean_object* v___x_2063_; 
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 0, v___x_2061_);
v___x_2063_ = v___x_2058_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2061_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
lean_del_object(v___x_2025_);
v_a_2067_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_2055_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2055_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
lean_dec(v_snd_2033_);
lean_del_object(v___x_2025_);
v_a_2075_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2053_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2053_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
v___jp_2083_:
{
if (lean_obj_tag(v___y_2084_) == 0)
{
lean_object* v_a_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v_a_2085_ = lean_ctor_get(v___y_2084_, 0);
lean_inc(v_a_2085_);
lean_dec_ref_known(v___y_2084_, 1);
v___x_2086_ = l_Lean_Expr_mvarId_x21(v_fst_2032_);
lean_dec(v_fst_2032_);
lean_inc(v_a_2020_);
lean_inc_ref(v_a_2019_);
lean_inc(v_a_2018_);
lean_inc_ref(v_a_2017_);
v___x_2087_ = lean_checked_assign(v___x_2086_, v_a_2085_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; uint8_t v___x_2089_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_a_2088_);
lean_dec_ref_known(v___x_2087_, 1);
v___x_2089_ = lean_unbox(v_a_2088_);
lean_dec(v_a_2088_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2099_; 
lean_dec(v_a_2044_);
lean_dec(v_snd_2033_);
lean_del_object(v___x_2025_);
v___x_2090_ = lean_obj_once(&l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__1, &l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__1_once, _init_l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__1);
v___x_2091_ = l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0___redArg(v___x_2090_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_);
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2094_ = v___x_2091_;
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2091_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2097_; 
if (v_isShared_2095_ == 0)
{
v___x_2097_ = v___x_2094_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_a_2092_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
else
{
v___y_2046_ = v_a_2014_;
v___y_2047_ = v_a_2015_;
v___y_2048_ = v_a_2016_;
v___y_2049_ = v_a_2017_;
v___y_2050_ = v_a_2018_;
v___y_2051_ = v_a_2019_;
v___y_2052_ = v_a_2020_;
goto v___jp_2045_;
}
}
else
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2107_; 
lean_dec(v_a_2044_);
lean_dec(v_snd_2033_);
lean_del_object(v___x_2025_);
v_a_2100_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2102_ = v___x_2087_;
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2087_);
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
else
{
lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
lean_dec(v_a_2044_);
lean_dec(v_snd_2033_);
lean_dec(v_fst_2032_);
lean_del_object(v___x_2025_);
v_a_2108_ = lean_ctor_get(v___y_2084_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___y_2084_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2110_ = v___y_2084_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_dec(v___y_2084_);
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
}
}
else
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
lean_dec_ref(v___f_2040_);
lean_del_object(v___x_2038_);
lean_dec_ref(v_binders_2035_);
lean_dec(v_snd_2033_);
lean_dec(v_fst_2032_);
lean_del_object(v___x_2025_);
v_a_2160_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v___x_2043_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2043_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
else
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
lean_dec_ref(v___f_2040_);
lean_del_object(v___x_2038_);
lean_dec_ref(v_binders_2035_);
lean_dec(v_snd_2033_);
lean_dec(v_fst_2032_);
lean_del_object(v___x_2025_);
lean_dec_ref(v_dec_2013_);
v_a_2168_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2170_ = v___x_2041_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2041_);
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
v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2168_);
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
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
lean_dec(v_snd_2033_);
lean_dec(v_fst_2032_);
lean_dec(v_snd_2028_);
lean_del_object(v___x_2025_);
lean_dec_ref(v_dec_2013_);
v_a_2177_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2034_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2034_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
lean_dec(v_snd_2028_);
lean_dec(v_fst_2027_);
lean_del_object(v___x_2025_);
lean_dec_ref(v_dec_2013_);
v_a_2185_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2030_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2030_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2185_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
}
else
{
lean_object* v___x_2194_; lean_object* v___x_2195_; 
lean_dec(v___x_2022_);
lean_dec_ref(v_dec_2013_);
v___x_2194_ = lean_box(0);
v___x_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
return v___x_2195_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___boxed(lean_object* v_e_2196_, lean_object* v_dec_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l_Lean_Elab_Do_tryElabForwardApp_x3f(v_e_2196_, v_dec_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_);
lean_dec(v_a_2204_);
lean_dec_ref(v_a_2203_);
lean_dec(v_a_2202_);
lean_dec_ref(v_a_2201_);
lean_dec(v_a_2200_);
lean_dec_ref(v_a_2199_);
lean_dec_ref(v_a_2198_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0(lean_object* v_00_u03b1_2207_, lean_object* v_msg_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v___x_2217_; 
v___x_2217_ = l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0___redArg(v_msg_2208_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0___boxed(lean_object* v_00_u03b1_2218_, lean_object* v_msg_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0(v_00_u03b1_2218_, v_msg_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec_ref(v___y_2220_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4(lean_object* v_00_u03b1_2229_, lean_object* v_x_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v___x_2233_; 
v___x_2233_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___redArg(v_x_2230_, v___y_2232_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2234_, lean_object* v_x_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4(v_00_u03b1_2234_, v_x_2235_, v___y_2236_, v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec_ref(v_x_2235_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9(lean_object* v_00_u03b1_2239_, lean_object* v_ref_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v___x_2248_; 
v___x_2248_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg(v_ref_2240_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___boxed(lean_object* v_00_u03b1_2249_, lean_object* v_ref_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9(v_00_u03b1_2249_, v_ref_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10(lean_object* v_00_u03b1_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg();
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___boxed(lean_object* v_00_u03b1_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10(v_00_u03b1_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3(lean_object* v_00_u03b1_2277_, lean_object* v_x_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg(v_x_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___boxed(lean_object* v_00_u03b1_2287_, lean_object* v_x_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3(v_00_u03b1_2287_, v_x_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3(lean_object* v_cls_2297_, lean_object* v_msg_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
lean_object* v___x_2306_; 
v___x_2306_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg(v_cls_2297_, v_msg_2298_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___boxed(lean_object* v_cls_2307_, lean_object* v_msg_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3(v_cls_2307_, v_msg_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6(lean_object* v_as_2317_, lean_object* v_as_x27_2318_, lean_object* v_b_2319_, lean_object* v_a_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v___x_2328_; 
v___x_2328_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6___redArg(v_as_x27_2318_, v_b_2319_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6___boxed(lean_object* v_as_2329_, lean_object* v_as_x27_2330_, lean_object* v_b_2331_, lean_object* v_a_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6(v_as_2329_, v_as_x27_2330_, v_b_2331_, v_a_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v_as_x27_2330_);
lean_dec(v_as_2329_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8(lean_object* v_00_u03b1_2341_, lean_object* v_ref_2342_, lean_object* v_msg_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v___x_2351_; 
v___x_2351_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8___redArg(v_ref_2342_, v_msg_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8___boxed(lean_object* v_00_u03b1_2352_, lean_object* v_ref_2353_, lean_object* v_msg_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8(v_00_u03b1_2352_, v_ref_2353_, v_msg_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v_ref_2353_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_2363_, lean_object* v_m_2364_, lean_object* v_a_2365_){
_start:
{
lean_object* v___x_2366_; 
v___x_2366_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8___redArg(v_m_2364_, v_a_2365_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_2367_, lean_object* v_m_2368_, lean_object* v_a_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8(v_00_u03b2_2367_, v_m_2368_, v_a_2369_);
lean_dec(v_a_2369_);
lean_dec_ref(v_m_2368_);
return v_res_2370_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9(lean_object* v_00_u03b2_2371_, lean_object* v_x_2372_, lean_object* v_x_2373_){
_start:
{
uint8_t v___x_2374_; 
v___x_2374_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9___redArg(v_x_2372_, v_x_2373_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9___boxed(lean_object* v_00_u03b2_2375_, lean_object* v_x_2376_, lean_object* v_x_2377_){
_start:
{
uint8_t v_res_2378_; lean_object* v_r_2379_; 
v_res_2378_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9(v_00_u03b2_2375_, v_x_2376_, v_x_2377_);
lean_dec_ref(v_x_2377_);
lean_dec_ref(v_x_2376_);
v_r_2379_ = lean_box(v_res_2378_);
return v_r_2379_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12(lean_object* v_00_u03b2_2380_, lean_object* v_a_2381_, lean_object* v_x_2382_){
_start:
{
lean_object* v___x_2383_; 
v___x_2383_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12___redArg(v_a_2381_, v_x_2382_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12___boxed(lean_object* v_00_u03b2_2384_, lean_object* v_a_2385_, lean_object* v_x_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12(v_00_u03b2_2384_, v_a_2385_, v_x_2386_);
lean_dec(v_x_2386_);
lean_dec(v_a_2385_);
return v_res_2387_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13(lean_object* v_00_u03b2_2388_, lean_object* v_x_2389_, size_t v_x_2390_, lean_object* v_x_2391_){
_start:
{
uint8_t v___x_2392_; 
v___x_2392_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13___redArg(v_x_2389_, v_x_2390_, v_x_2391_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13___boxed(lean_object* v_00_u03b2_2393_, lean_object* v_x_2394_, lean_object* v_x_2395_, lean_object* v_x_2396_){
_start:
{
size_t v_x_30034__boxed_2397_; uint8_t v_res_2398_; lean_object* v_r_2399_; 
v_x_30034__boxed_2397_ = lean_unbox_usize(v_x_2395_);
lean_dec(v_x_2395_);
v_res_2398_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13(v_00_u03b2_2393_, v_x_2394_, v_x_30034__boxed_2397_, v_x_2396_);
lean_dec_ref(v_x_2396_);
lean_dec_ref(v_x_2394_);
v_r_2399_ = lean_box(v_res_2398_);
return v_r_2399_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16(lean_object* v_00_u03b2_2400_, lean_object* v_keys_2401_, lean_object* v_vals_2402_, lean_object* v_heq_2403_, lean_object* v_i_2404_, lean_object* v_k_2405_){
_start:
{
uint8_t v___x_2406_; 
v___x_2406_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16___redArg(v_keys_2401_, v_i_2404_, v_k_2405_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16___boxed(lean_object* v_00_u03b2_2407_, lean_object* v_keys_2408_, lean_object* v_vals_2409_, lean_object* v_heq_2410_, lean_object* v_i_2411_, lean_object* v_k_2412_){
_start:
{
uint8_t v_res_2413_; lean_object* v_r_2414_; 
v_res_2413_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16(v_00_u03b2_2407_, v_keys_2408_, v_vals_2409_, v_heq_2410_, v_i_2411_, v_k_2412_);
lean_dec_ref(v_k_2412_);
lean_dec_ref(v_vals_2409_);
lean_dec_ref(v_keys_2408_);
v_r_2414_ = lean_box(v_res_2413_);
return v_r_2414_;
}
}
lean_object* runtime_initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_Control(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Do_InferControlInfo(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Binders(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_BuiltinDo_Forward(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Do_InferControlInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Binders(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Do(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_BuiltinDo_Forward(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Do(uint8_t builtin);
lean_object* initialize_Lean_Elab_Do_Control(uint8_t builtin);
lean_object* initialize_Lean_Elab_Do_InferControlInfo(uint8_t builtin);
lean_object* initialize_Lean_Elab_Binders(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_BuiltinDo_Forward(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Do_Control(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Do_InferControlInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Binders(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_BuiltinDo_Forward(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_BuiltinDo_Forward(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_BuiltinDo_Forward(builtin);
}
#ifdef __cplusplus
}
#endif
