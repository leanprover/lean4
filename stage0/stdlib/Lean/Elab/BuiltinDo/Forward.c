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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___lam__0(lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__2(lean_object* v_opts_1_, lean_object* v_opt_2_){
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
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1_ = stack[0].m_obj;
lean_object* v_opt_2_ = stack[1].m_obj;
uint8_t v_res_11_;
v_res_11_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__2(v_opts_1_, v_opt_2_);
stack->m_num = v_res_11_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__2___boxed(lean_object* v_opts_12_, lean_object* v_opt_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__2(v_opts_12_, v_opt_13_);
lean_dec_ref(v_opt_13_);
lean_dec_ref(v_opts_12_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_box(1);
v___x_17_ = l_Lean_MessageData_ofFormat(v___x_16_);
return v___x_17_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__2));
v___x_22_ = l_Lean_MessageData_ofFormat(v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3(lean_object* v_x_23_, lean_object* v_x_24_){
_start:
{
if (lean_obj_tag(v_x_24_) == 0)
{
return v_x_23_;
}
else
{
lean_object* v_head_25_; lean_object* v_tail_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_48_; 
v_head_25_ = lean_ctor_get(v_x_24_, 0);
v_tail_26_ = lean_ctor_get(v_x_24_, 1);
v_isSharedCheck_48_ = !lean_is_exclusive(v_x_24_);
if (v_isSharedCheck_48_ == 0)
{
v___x_28_ = v_x_24_;
v_isShared_29_ = v_isSharedCheck_48_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_tail_26_);
lean_inc(v_head_25_);
lean_dec(v_x_24_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_48_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v_before_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_46_; 
v_before_30_ = lean_ctor_get(v_head_25_, 0);
v_isSharedCheck_46_ = !lean_is_exclusive(v_head_25_);
if (v_isSharedCheck_46_ == 0)
{
lean_object* v_unused_47_; 
v_unused_47_ = lean_ctor_get(v_head_25_, 1);
lean_dec(v_unused_47_);
v___x_32_ = v_head_25_;
v_isShared_33_ = v_isSharedCheck_46_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_before_30_);
lean_dec(v_head_25_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_46_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_34_; lean_object* v___x_36_; 
v___x_34_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_33_ == 0)
{
lean_ctor_set_tag(v___x_32_, 7);
lean_ctor_set(v___x_32_, 1, v___x_34_);
lean_ctor_set(v___x_32_, 0, v_x_23_);
v___x_36_ = v___x_32_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_x_23_);
lean_ctor_set(v_reuseFailAlloc_45_, 1, v___x_34_);
v___x_36_ = v_reuseFailAlloc_45_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
lean_object* v___x_37_; lean_object* v___x_39_; 
v___x_37_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__3);
if (v_isShared_29_ == 0)
{
lean_ctor_set_tag(v___x_28_, 7);
lean_ctor_set(v___x_28_, 1, v___x_37_);
lean_ctor_set(v___x_28_, 0, v___x_36_);
v___x_39_ = v___x_28_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v___x_36_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v___x_37_);
v___x_39_ = v_reuseFailAlloc_44_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_40_ = l_Lean_MessageData_ofSyntax(v_before_30_);
v___x_41_ = l_Lean_indentD(v___x_40_);
v___x_42_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_42_, 0, v___x_39_);
lean_ctor_set(v___x_42_, 1, v___x_41_);
v_x_23_ = v___x_42_;
v_x_24_ = v_tail_26_;
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
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___closed__1));
v___x_53_ = l_Lean_MessageData_ofFormat(v___x_52_);
return v___x_53_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg(lean_object* v_msgData_54_, lean_object* v_macroStack_55_, lean_object* v___y_56_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_58_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_56_);
v___x_59_ = l_Lean_Elab_pp_macroStack;
v___x_60_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__2(v___x_58_, v___x_59_);
lean_dec_ref(v___x_58_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; 
lean_dec(v_macroStack_55_);
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v_msgData_54_);
return v___x_61_;
}
else
{
if (lean_obj_tag(v_macroStack_55_) == 0)
{
lean_object* v___x_62_; 
v___x_62_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_62_, 0, v_msgData_54_);
return v___x_62_;
}
else
{
lean_object* v_head_63_; lean_object* v_after_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_79_; 
v_head_63_ = lean_ctor_get(v_macroStack_55_, 0);
lean_inc(v_head_63_);
v_after_64_ = lean_ctor_get(v_head_63_, 1);
v_isSharedCheck_79_ = !lean_is_exclusive(v_head_63_);
if (v_isSharedCheck_79_ == 0)
{
lean_object* v_unused_80_; 
v_unused_80_ = lean_ctor_get(v_head_63_, 0);
lean_dec(v_unused_80_);
v___x_66_ = v_head_63_;
v_isShared_67_ = v_isSharedCheck_79_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_after_64_);
lean_dec(v_head_63_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_79_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_68_; lean_object* v___x_70_; 
v___x_68_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_67_ == 0)
{
lean_ctor_set_tag(v___x_66_, 7);
lean_ctor_set(v___x_66_, 1, v___x_68_);
lean_ctor_set(v___x_66_, 0, v_msgData_54_);
v___x_70_ = v___x_66_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v_msgData_54_);
lean_ctor_set(v_reuseFailAlloc_78_, 1, v___x_68_);
v___x_70_ = v_reuseFailAlloc_78_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v_msgData_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_71_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___closed__2);
v___x_72_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_70_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
v___x_73_ = l_Lean_MessageData_ofSyntax(v_after_64_);
v___x_74_ = l_Lean_indentD(v___x_73_);
v_msgData_75_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_75_, 0, v___x_72_);
lean_ctor_set(v_msgData_75_, 1, v___x_74_);
v___x_76_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3(v_msgData_75_, v_macroStack_55_);
v___x_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
return v___x_77_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_54_ = stack[0].m_obj;
lean_object* v_macroStack_55_ = stack[1].m_obj;
lean_object* v___y_56_ = stack[2].m_obj;
lean_object* v_res_81_;
v_res_81_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg(v_msgData_54_, v_macroStack_55_, v___y_56_);
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_82_, lean_object* v_macroStack_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg(v_msgData_82_, v_macroStack_83_, v___y_84_);
lean_dec_ref(v___y_84_);
return v_res_86_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0(lean_object* v_msgData_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v___x_93_; lean_object* v_env_94_; uint8_t v___x_95_; lean_object* v_env_96_; lean_object* v___x_97_; lean_object* v_toCold_98_; lean_object* v_mctx_99_; lean_object* v_lctx_100_; lean_object* v_options_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_93_ = lean_st_ref_get(v___y_91_);
v_env_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc_ref(v_env_94_);
lean_dec(v___x_93_);
v___x_95_ = 0;
v_env_96_ = l_Lean_Environment_setRecordingDeps(v_env_94_, v___x_95_);
v___x_97_ = lean_st_ref_get(v___y_89_);
v_toCold_98_ = lean_ctor_get(v___y_90_, 0);
v_mctx_99_ = lean_ctor_get(v___x_97_, 0);
lean_inc_ref(v_mctx_99_);
lean_dec(v___x_97_);
v_lctx_100_ = lean_ctor_get(v___y_88_, 2);
v_options_101_ = lean_ctor_get(v_toCold_98_, 2);
lean_inc_ref(v_options_101_);
lean_inc_ref(v_lctx_100_);
v___x_102_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_102_, 0, v_env_96_);
lean_ctor_set(v___x_102_, 1, v_mctx_99_);
lean_ctor_set(v___x_102_, 2, v_lctx_100_);
lean_ctor_set(v___x_102_, 3, v_options_101_);
v___x_103_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v_msgData_87_);
v___x_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
return v___x_104_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_87_ = stack[0].m_obj;
lean_object* v___y_88_ = stack[1].m_obj;
lean_object* v___y_89_ = stack[2].m_obj;
lean_object* v___y_90_ = stack[3].m_obj;
lean_object* v___y_91_ = stack[4].m_obj;
lean_object* v_res_105_;
v_res_105_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0(v_msgData_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
stack->m_obj
 = v_res_105_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0___boxed(lean_object* v_msgData_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0(v_msgData_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
return v_res_112_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg(lean_object* v_msg_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v_ref_121_; lean_object* v_macroStack_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v_a_125_; lean_object* v___x_126_; lean_object* v_a_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_135_; 
v_ref_121_ = lean_ctor_get(v___y_118_, 2);
v_macroStack_122_ = lean_ctor_get(v___y_114_, 1);
v___x_123_ = l_Lean_Elab_getBetterRef(v_ref_121_, v_macroStack_122_);
v___x_124_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0(v_msg_113_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
v_a_125_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_a_125_);
lean_dec_ref(v___x_124_);
lean_inc(v_macroStack_122_);
v___x_126_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg(v_a_125_, v_macroStack_122_, v___y_118_);
v_a_127_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_135_ == 0)
{
v___x_129_ = v___x_126_;
v_isShared_130_ = v_isSharedCheck_135_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_a_127_);
lean_dec(v___x_126_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_135_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_123_);
lean_ctor_set(v___x_131_, 1, v_a_127_);
if (v_isShared_130_ == 0)
{
lean_ctor_set_tag(v___x_129_, 1);
lean_ctor_set(v___x_129_, 0, v___x_131_);
v___x_133_ = v___x_129_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_131_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_113_ = stack[0].m_obj;
lean_object* v___y_114_ = stack[1].m_obj;
lean_object* v___y_115_ = stack[2].m_obj;
lean_object* v___y_116_ = stack[3].m_obj;
lean_object* v___y_117_ = stack[4].m_obj;
lean_object* v___y_118_ = stack[5].m_obj;
lean_object* v___y_119_ = stack[6].m_obj;
lean_object* v_res_136_;
v_res_136_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg(v_msg_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
stack->m_obj
 = v_res_136_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg___boxed(lean_object* v_msg_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg(v_msg_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
return v_res_145_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoForward___redArg___closed__1(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = ((lean_object*)(l_Lean_Elab_Do_elabDoForward___redArg___closed__0));
v___x_148_ = l_Lean_stringToMessageData(v___x_147_);
return v___x_148_;
}
}
lean_object* l_Lean_Elab_Do_elabDoForward___redArg(lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = lean_obj_once(&l_Lean_Elab_Do_elabDoForward___redArg___closed__1, &l_Lean_Elab_Do_elabDoForward___redArg___closed__1_once, _init_l_Lean_Elab_Do_elabDoForward___redArg___closed__1);
v___x_157_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg(v___x_156_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_);
return v___x_157_;
}
}
LEAN_EXPORT void l_Lean_Elab_Do_elabDoForward___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_149_ = stack[0].m_obj;
lean_object* v_a_150_ = stack[1].m_obj;
lean_object* v_a_151_ = stack[2].m_obj;
lean_object* v_a_152_ = stack[3].m_obj;
lean_object* v_a_153_ = stack[4].m_obj;
lean_object* v_a_154_ = stack[5].m_obj;
lean_object* v_res_158_;
v_res_158_ = l_Lean_Elab_Do_elabDoForward___redArg(v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_);
stack->m_obj
 = v_res_158_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoForward___redArg___boxed(lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_Elab_Do_elabDoForward___redArg(v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_);
lean_dec(v_a_164_);
lean_dec_ref(v_a_163_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
lean_dec(v_a_160_);
lean_dec_ref(v_a_159_);
return v_res_166_;
}
}
lean_object* l_Lean_Elab_Do_elabDoForward(lean_object* v_x_167_, lean_object* v_x_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Lean_Elab_Do_elabDoForward___redArg(v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
return v___x_176_;
}
}
LEAN_EXPORT void l_Lean_Elab_Do_elabDoForward_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_167_ = stack[0].m_obj;
lean_object* v_x_168_ = stack[1].m_obj;
lean_object* v_a_169_ = stack[2].m_obj;
lean_object* v_a_170_ = stack[3].m_obj;
lean_object* v_a_171_ = stack[4].m_obj;
lean_object* v_a_172_ = stack[5].m_obj;
lean_object* v_a_173_ = stack[6].m_obj;
lean_object* v_a_174_ = stack[7].m_obj;
lean_object* v_res_177_;
v_res_177_ = l_Lean_Elab_Do_elabDoForward(v_x_167_, v_x_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
stack->m_obj
 = v_res_177_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoForward___boxed(lean_object* v_x_178_, lean_object* v_x_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_Elab_Do_elabDoForward(v_x_178_, v_x_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_);
lean_dec(v_a_185_);
lean_dec_ref(v_a_184_);
lean_dec(v_a_183_);
lean_dec_ref(v_a_182_);
lean_dec(v_a_181_);
lean_dec_ref(v_a_180_);
lean_dec(v_x_179_);
lean_dec(v_x_178_);
return v_res_187_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0(lean_object* v_00_u03b1_188_, lean_object* v_msg_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg(v_msg_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
return v___x_197_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_189_ = stack[1].m_obj;
lean_object* v___y_190_ = stack[2].m_obj;
lean_object* v___y_191_ = stack[3].m_obj;
lean_object* v___y_192_ = stack[4].m_obj;
lean_object* v___y_193_ = stack[5].m_obj;
lean_object* v___y_194_ = stack[6].m_obj;
lean_object* v___y_195_ = stack[7].m_obj;
lean_object* v_res_198_;
v_res_198_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0(lean_box(0), v_msg_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
stack->m_obj
 = v_res_198_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___boxed(lean_object* v_00_u03b1_199_, lean_object* v_msg_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0(v_00_u03b1_199_, v_msg_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
return v_res_208_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1(lean_object* v_msgData_209_, lean_object* v_macroStack_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg(v_msgData_209_, v_macroStack_210_, v___y_215_);
return v___x_218_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_209_ = stack[0].m_obj;
lean_object* v_macroStack_210_ = stack[1].m_obj;
lean_object* v___y_211_ = stack[2].m_obj;
lean_object* v___y_212_ = stack[3].m_obj;
lean_object* v___y_213_ = stack[4].m_obj;
lean_object* v___y_214_ = stack[5].m_obj;
lean_object* v___y_215_ = stack[6].m_obj;
lean_object* v___y_216_ = stack[7].m_obj;
lean_object* v_res_219_;
v_res_219_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1(v_msgData_209_, v_macroStack_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_);
stack->m_obj
 = v_res_219_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___boxed(lean_object* v_msgData_220_, lean_object* v_macroStack_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1(v_msgData_220_, v_macroStack_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
return v_res_229_;
}
}
lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1(){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_248_ = l_Lean_Elab_Term_termElabAttribute;
v___x_249_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__4));
v___x_250_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__8));
v___x_251_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoForward___boxed), 9, 0);
v___x_252_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_248_, v___x_249_, v___x_250_, v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_253_;
v_res_253_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1();
stack->m_obj
 = v_res_253_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___boxed(lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1();
return v_res_255_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__0));
v___x_258_ = l_Lean_stringToMessageData(v___x_257_);
return v___x_258_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__3(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__2));
v___x_261_ = l_Lean_stringToMessageData(v___x_260_);
return v___x_261_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__5(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__4));
v___x_264_ = l_Lean_stringToMessageData(v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint(lean_object* v_headApp_265_, lean_object* v_reason_266_){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_267_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1);
v___x_268_ = l_Lean_MessageData_ofSyntax(v_headApp_265_);
v___x_269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_267_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v___x_270_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__3, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__3);
v___x_271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_269_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
v___x_272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v_reason_266_);
v___x_273_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__5, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__5_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__5);
v___x_274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_272_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
return v___x_274_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(lean_object* v_e_275_, lean_object* v___y_276_){
_start:
{
uint8_t v___x_278_; 
v___x_278_ = l_Lean_Expr_hasMVar(v_e_275_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; 
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v_e_275_);
return v___x_279_;
}
else
{
lean_object* v___x_280_; lean_object* v_mctx_281_; lean_object* v___x_282_; lean_object* v_fst_283_; lean_object* v_snd_284_; lean_object* v___x_285_; lean_object* v_cache_286_; lean_object* v_zetaDeltaFVarIds_287_; lean_object* v_postponed_288_; lean_object* v_diag_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_298_; 
v___x_280_ = lean_st_ref_get(v___y_276_);
v_mctx_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc_ref(v_mctx_281_);
lean_dec(v___x_280_);
v___x_282_ = l_Lean_instantiateMVarsCore(v_mctx_281_, v_e_275_);
v_fst_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_fst_283_);
v_snd_284_ = lean_ctor_get(v___x_282_, 1);
lean_inc(v_snd_284_);
lean_dec_ref(v___x_282_);
v___x_285_ = lean_st_ref_take(v___y_276_);
v_cache_286_ = lean_ctor_get(v___x_285_, 1);
v_zetaDeltaFVarIds_287_ = lean_ctor_get(v___x_285_, 2);
v_postponed_288_ = lean_ctor_get(v___x_285_, 3);
v_diag_289_ = lean_ctor_get(v___x_285_, 4);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_298_ == 0)
{
lean_object* v_unused_299_; 
v_unused_299_ = lean_ctor_get(v___x_285_, 0);
lean_dec(v_unused_299_);
v___x_291_ = v___x_285_;
v_isShared_292_ = v_isSharedCheck_298_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_diag_289_);
lean_inc(v_postponed_288_);
lean_inc(v_zetaDeltaFVarIds_287_);
lean_inc(v_cache_286_);
lean_dec(v___x_285_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_298_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 0, v_snd_284_);
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_snd_284_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v_cache_286_);
lean_ctor_set(v_reuseFailAlloc_297_, 2, v_zetaDeltaFVarIds_287_);
lean_ctor_set(v_reuseFailAlloc_297_, 3, v_postponed_288_);
lean_ctor_set(v_reuseFailAlloc_297_, 4, v_diag_289_);
v___x_294_ = v_reuseFailAlloc_297_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_st_ref_put(v___y_276_, v___x_294_);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v_fst_283_);
return v___x_296_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_275_ = stack[0].m_obj;
lean_object* v___y_276_ = stack[1].m_obj;
lean_object* v_res_300_;
v_res_300_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_e_275_, v___y_276_);
stack->m_obj
 = v_res_300_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg___boxed(lean_object* v_e_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_e_301_, v___y_302_);
lean_dec(v___y_302_);
return v_res_304_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1(lean_object* v_e_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_e_305_, v___y_307_);
return v___x_311_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_305_ = stack[0].m_obj;
lean_object* v___y_306_ = stack[1].m_obj;
lean_object* v___y_307_ = stack[2].m_obj;
lean_object* v___y_308_ = stack[3].m_obj;
lean_object* v___y_309_ = stack[4].m_obj;
lean_object* v_res_312_;
v_res_312_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1(v_e_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
stack->m_obj
 = v_res_312_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___boxed(lean_object* v_e_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1(v_e_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
return v_res_319_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___lam__0(lean_object* v_k_320_, lean_object* v_b_321_, lean_object* v_c_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
lean_object* v___x_328_; 
lean_inc(v___y_326_);
lean_inc_ref(v___y_325_);
lean_inc(v___y_324_);
lean_inc_ref(v___y_323_);
v___x_328_ = lean_apply_7(v_k_320_, v_b_321_, v_c_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, lean_box(0));
return v___x_328_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_320_ = stack[0].m_obj;
lean_object* v_b_321_ = stack[1].m_obj;
lean_object* v_c_322_ = stack[2].m_obj;
lean_object* v___y_323_ = stack[3].m_obj;
lean_object* v___y_324_ = stack[4].m_obj;
lean_object* v___y_325_ = stack[5].m_obj;
lean_object* v___y_326_ = stack[6].m_obj;
lean_object* v_res_329_;
v_res_329_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___lam__0(v_k_320_, v_b_321_, v_c_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_);
stack->m_obj
 = v_res_329_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___lam__0___boxed(lean_object* v_k_330_, lean_object* v_b_331_, lean_object* v_c_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___lam__0(v_k_330_, v_b_331_, v_c_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
return v_res_338_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg(lean_object* v_type_339_, lean_object* v_k_340_, uint8_t v_cleanupAnnotations_341_, uint8_t v_whnfType_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v___f_348_; lean_object* v___x_349_; 
v___f_348_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_348_, 0, v_k_340_);
v___x_349_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_339_, v___f_348_, v_cleanupAnnotations_341_, v_whnfType_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_349_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_349_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
else
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
v_a_358_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_349_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_349_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_339_ = stack[0].m_obj;
lean_object* v_k_340_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_341_ = stack[2].m_num;
uint8_t v_whnfType_342_ = stack[3].m_num;
lean_object* v___y_343_ = stack[4].m_obj;
lean_object* v___y_344_ = stack[5].m_obj;
lean_object* v___y_345_ = stack[6].m_obj;
lean_object* v___y_346_ = stack[7].m_obj;
lean_object* v_res_366_;
v_res_366_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg(v_type_339_, v_k_340_, v_cleanupAnnotations_341_, v_whnfType_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
stack->m_obj
 = v_res_366_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___boxed(lean_object* v_type_367_, lean_object* v_k_368_, lean_object* v_cleanupAnnotations_369_, lean_object* v_whnfType_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_376_; uint8_t v_whnfType_boxed_377_; lean_object* v_res_378_; 
v_cleanupAnnotations_boxed_376_ = lean_unbox(v_cleanupAnnotations_369_);
v_whnfType_boxed_377_ = lean_unbox(v_whnfType_370_);
v_res_378_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg(v_type_367_, v_k_368_, v_cleanupAnnotations_boxed_376_, v_whnfType_boxed_377_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
return v_res_378_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4(lean_object* v_00_u03b1_379_, lean_object* v_type_380_, lean_object* v_k_381_, uint8_t v_cleanupAnnotations_382_, uint8_t v_whnfType_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg(v_type_380_, v_k_381_, v_cleanupAnnotations_382_, v_whnfType_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
return v___x_389_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_380_ = stack[1].m_obj;
lean_object* v_k_381_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_382_ = stack[3].m_num;
uint8_t v_whnfType_383_ = stack[4].m_num;
lean_object* v___y_384_ = stack[5].m_obj;
lean_object* v___y_385_ = stack[6].m_obj;
lean_object* v___y_386_ = stack[7].m_obj;
lean_object* v___y_387_ = stack[8].m_obj;
lean_object* v_res_390_;
v_res_390_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4(lean_box(0), v_type_380_, v_k_381_, v_cleanupAnnotations_382_, v_whnfType_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
stack->m_obj
 = v_res_390_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___boxed(lean_object* v_00_u03b1_391_, lean_object* v_type_392_, lean_object* v_k_393_, lean_object* v_cleanupAnnotations_394_, lean_object* v_whnfType_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_401_; uint8_t v_whnfType_boxed_402_; lean_object* v_res_403_; 
v_cleanupAnnotations_boxed_401_ = lean_unbox(v_cleanupAnnotations_394_);
v_whnfType_boxed_402_ = lean_unbox(v_whnfType_395_);
v_res_403_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4(v_00_u03b1_391_, v_type_392_, v_k_393_, v_cleanupAnnotations_boxed_401_, v_whnfType_boxed_402_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
return v_res_403_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(lean_object* v_msg_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v_ref_410_; lean_object* v___x_411_; lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_420_; 
v_ref_410_ = lean_ctor_get(v___y_407_, 2);
v___x_411_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0(v_msg_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
v_a_412_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_420_ == 0)
{
v___x_414_ = v___x_411_;
v_isShared_415_ = v_isSharedCheck_420_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_411_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_420_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; lean_object* v___x_418_; 
lean_inc(v_ref_410_);
v___x_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_416_, 0, v_ref_410_);
lean_ctor_set(v___x_416_, 1, v_a_412_);
if (v_isShared_415_ == 0)
{
lean_ctor_set_tag(v___x_414_, 1);
lean_ctor_set(v___x_414_, 0, v___x_416_);
v___x_418_ = v___x_414_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_416_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_404_ = stack[0].m_obj;
lean_object* v___y_405_ = stack[1].m_obj;
lean_object* v___y_406_ = stack[2].m_obj;
lean_object* v___y_407_ = stack[3].m_obj;
lean_object* v___y_408_ = stack[4].m_obj;
lean_object* v_res_421_;
v_res_421_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v_msg_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
stack->m_obj
 = v_res_421_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg___boxed(lean_object* v_msg_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v_msg_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
return v_res_428_;
}
}
lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0(lean_object* v_headApp_429_, lean_object* v_00_u03b1_430_, lean_object* v_reason_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint(v_headApp_429_, v_reason_431_);
v___x_438_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v___x_437_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
return v___x_438_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_headApp_429_ = stack[0].m_obj;
lean_object* v_reason_431_ = stack[2].m_obj;
lean_object* v___y_432_ = stack[3].m_obj;
lean_object* v___y_433_ = stack[4].m_obj;
lean_object* v___y_434_ = stack[5].m_obj;
lean_object* v___y_435_ = stack[6].m_obj;
lean_object* v_res_439_;
v_res_439_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0(v_headApp_429_, lean_box(0), v_reason_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
stack->m_obj
 = v_res_439_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0___boxed(lean_object* v_headApp_440_, lean_object* v_00_u03b1_441_, lean_object* v_reason_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0(v_headApp_440_, v_00_u03b1_441_, v_reason_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
return v_res_448_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0(lean_object* v_arg_449_, lean_object* v_x_450_){
_start:
{
lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_451_ = l_Lean_Expr_mvarId_x21(v_arg_449_);
v___x_452_ = l_Lean_instBEqMVarId_beq(v_x_450_, v___x_451_);
lean_dec(v___x_451_);
return v___x_452_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_449_ = stack[0].m_obj;
lean_object* v_x_450_ = stack[1].m_obj;
uint8_t v_res_453_;
v_res_453_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0(v_arg_449_, v_x_450_);
stack->m_num = v_res_453_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0___boxed(lean_object* v_arg_454_, lean_object* v_x_455_){
_start:
{
uint8_t v_res_456_; lean_object* v_r_457_; 
v_res_456_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0(v_arg_454_, v_x_455_);
lean_dec(v_x_455_);
lean_dec_ref(v_arg_454_);
v_r_457_ = lean_box(v_res_456_);
return v_r_457_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__0));
v___x_460_ = l_Lean_stringToMessageData(v___x_459_);
return v___x_460_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4(lean_object* v_arg_461_, lean_object* v_headApp_462_, lean_object* v_as_463_, size_t v_sz_464_, size_t v_i_465_, lean_object* v_b_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_a_473_; uint8_t v___x_477_; 
v___x_477_ = lean_usize_dec_lt(v_i_465_, v_sz_464_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; 
lean_dec(v_headApp_462_);
lean_dec_ref(v_arg_461_);
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v_b_466_);
return v___x_478_;
}
else
{
lean_object* v___f_479_; lean_object* v___x_480_; lean_object* v_a_481_; lean_object* v___x_482_; 
lean_inc_ref(v_arg_461_);
v___f_479_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_479_, 0, v_arg_461_);
v___x_480_ = lean_box(0);
v_a_481_ = lean_array_uget_borrowed(v_as_463_, v_i_465_);
lean_inc(v___y_470_);
lean_inc_ref(v___y_469_);
lean_inc(v___y_468_);
lean_inc_ref(v___y_467_);
lean_inc(v_a_481_);
v___x_482_ = lean_infer_type(v_a_481_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v___x_484_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc_n(v_a_483_, 2);
lean_dec_ref_known(v___x_482_, 1);
v___x_484_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_a_483_, v___y_468_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_a_485_);
lean_dec_ref_known(v___x_484_, 1);
v___x_486_ = lean_box(0);
v___x_487_ = l_Lean_FindMVar_main(v___f_479_, v_a_485_, v___x_486_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_dec(v_a_483_);
v_a_473_ = v___x_480_;
goto v___jp_472_;
}
else
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
lean_dec_ref_known(v___x_487_, 1);
v___x_488_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1);
v___x_489_ = l_Lean_MessageData_ofExpr(v_a_483_);
v___x_490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_488_);
lean_ctor_set(v___x_490_, 1, v___x_489_);
v___x_491_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1);
v___x_492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_490_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
lean_inc(v_headApp_462_);
v___x_493_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint(v_headApp_462_, v___x_492_);
v___x_494_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v___x_493_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_dec_ref_known(v___x_494_, 1);
v_a_473_ = v___x_480_;
goto v___jp_472_;
}
else
{
lean_dec(v_headApp_462_);
lean_dec_ref(v_arg_461_);
return v___x_494_;
}
}
}
else
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
lean_dec(v_a_483_);
lean_dec_ref(v___f_479_);
lean_dec(v_headApp_462_);
lean_dec_ref(v_arg_461_);
v_a_495_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_484_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_484_);
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
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_495_);
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
else
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_510_; 
lean_dec_ref(v___f_479_);
lean_dec(v_headApp_462_);
lean_dec_ref(v_arg_461_);
v_a_503_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_510_ == 0)
{
v___x_505_ = v___x_482_;
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_482_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_a_503_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
v___jp_472_:
{
size_t v___x_474_; size_t v___x_475_; 
v___x_474_ = ((size_t)1ULL);
v___x_475_ = lean_usize_add(v_i_465_, v___x_474_);
v_i_465_ = v___x_475_;
v_b_466_ = v_a_473_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_461_ = stack[0].m_obj;
lean_object* v_headApp_462_ = stack[1].m_obj;
lean_object* v_as_463_ = stack[2].m_obj;
size_t v_sz_464_ = stack[3].m_num;
size_t v_i_465_ = stack[4].m_num;
lean_object* v_b_466_ = stack[5].m_obj;
lean_object* v___y_467_ = stack[6].m_obj;
lean_object* v___y_468_ = stack[7].m_obj;
lean_object* v___y_469_ = stack[8].m_obj;
lean_object* v___y_470_ = stack[9].m_obj;
lean_object* v_res_511_;
v_res_511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4(v_arg_461_, v_headApp_462_, v_as_463_, v_sz_464_, v_i_465_, v_b_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
stack->m_obj
 = v_res_511_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___boxed(lean_object* v_arg_512_, lean_object* v_headApp_513_, lean_object* v_as_514_, lean_object* v_sz_515_, lean_object* v_i_516_, lean_object* v_b_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
size_t v_sz_boxed_523_; size_t v_i_boxed_524_; lean_object* v_res_525_; 
v_sz_boxed_523_ = lean_unbox_usize(v_sz_515_);
lean_dec(v_sz_515_);
v_i_boxed_524_ = lean_unbox_usize(v_i_516_);
lean_dec(v_i_516_);
v_res_525_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4(v_arg_512_, v_headApp_513_, v_as_514_, v_sz_boxed_523_, v_i_boxed_524_, v_b_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec_ref(v_as_514_);
return v_res_525_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3(lean_object* v_arg_526_, lean_object* v_headApp_527_, lean_object* v_as_528_, size_t v_sz_529_, size_t v_i_530_, lean_object* v_b_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v_a_538_; uint8_t v___x_542_; 
v___x_542_ = lean_usize_dec_lt(v_i_530_, v_sz_529_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; 
lean_dec(v_headApp_527_);
lean_dec_ref(v_arg_526_);
v___x_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_543_, 0, v_b_531_);
return v___x_543_;
}
else
{
lean_object* v___f_544_; lean_object* v___x_545_; lean_object* v_a_546_; lean_object* v___x_547_; 
lean_inc_ref(v_arg_526_);
v___f_544_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_544_, 0, v_arg_526_);
v___x_545_ = lean_box(0);
v_a_546_ = lean_array_uget_borrowed(v_as_528_, v_i_530_);
lean_inc(v___y_535_);
lean_inc_ref(v___y_534_);
lean_inc(v___y_533_);
lean_inc_ref(v___y_532_);
lean_inc(v_a_546_);
v___x_547_ = lean_infer_type(v_a_546_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v_a_548_; lean_object* v___x_549_; 
v_a_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc_n(v_a_548_, 2);
lean_dec_ref_known(v___x_547_, 1);
v___x_549_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_a_548_, v___y_533_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
lean_inc(v_a_550_);
lean_dec_ref_known(v___x_549_, 1);
v___x_551_ = lean_box(0);
v___x_552_ = l_Lean_FindMVar_main(v___f_544_, v_a_550_, v___x_551_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_dec(v_a_548_);
v_a_538_ = v___x_545_;
goto v___jp_537_;
}
else
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
lean_dec_ref_known(v___x_552_, 1);
v___x_553_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1);
v___x_554_ = l_Lean_MessageData_ofExpr(v_a_548_);
v___x_555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_553_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1);
v___x_557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_555_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
lean_inc(v_headApp_527_);
v___x_558_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint(v_headApp_527_, v___x_557_);
v___x_559_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v___x_558_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_dec_ref_known(v___x_559_, 1);
v_a_538_ = v___x_545_;
goto v___jp_537_;
}
else
{
lean_dec(v_headApp_527_);
lean_dec_ref(v_arg_526_);
return v___x_559_;
}
}
}
else
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
lean_dec(v_a_548_);
lean_dec_ref(v___f_544_);
lean_dec(v_headApp_527_);
lean_dec_ref(v_arg_526_);
v_a_560_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___x_549_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_549_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
else
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
lean_dec_ref(v___f_544_);
lean_dec(v_headApp_527_);
lean_dec_ref(v_arg_526_);
v_a_568_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_575_ == 0)
{
v___x_570_ = v___x_547_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_547_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_a_568_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
v___jp_537_:
{
size_t v___x_539_; size_t v___x_540_; lean_object* v___x_541_; 
v___x_539_ = ((size_t)1ULL);
v___x_540_ = lean_usize_add(v_i_530_, v___x_539_);
v___x_541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4(v_arg_526_, v_headApp_527_, v_as_528_, v_sz_529_, v___x_540_, v_a_538_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
return v___x_541_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_526_ = stack[0].m_obj;
lean_object* v_headApp_527_ = stack[1].m_obj;
lean_object* v_as_528_ = stack[2].m_obj;
size_t v_sz_529_ = stack[3].m_num;
size_t v_i_530_ = stack[4].m_num;
lean_object* v_b_531_ = stack[5].m_obj;
lean_object* v___y_532_ = stack[6].m_obj;
lean_object* v___y_533_ = stack[7].m_obj;
lean_object* v___y_534_ = stack[8].m_obj;
lean_object* v___y_535_ = stack[9].m_obj;
lean_object* v_res_576_;
v_res_576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3(v_arg_526_, v_headApp_527_, v_as_528_, v_sz_529_, v_i_530_, v_b_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
stack->m_obj
 = v_res_576_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3___boxed(lean_object* v_arg_577_, lean_object* v_headApp_578_, lean_object* v_as_579_, lean_object* v_sz_580_, lean_object* v_i_581_, lean_object* v_b_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
size_t v_sz_boxed_588_; size_t v_i_boxed_589_; lean_object* v_res_590_; 
v_sz_boxed_588_ = lean_unbox_usize(v_sz_580_);
lean_dec(v_sz_580_);
v_i_boxed_589_ = lean_unbox_usize(v_i_581_);
lean_dec(v_i_581_);
v_res_590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3(v_arg_577_, v_headApp_578_, v_as_579_, v_sz_boxed_588_, v_i_boxed_589_, v_b_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec_ref(v_as_579_);
return v_res_590_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__1(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__0));
v___x_593_ = l_Lean_stringToMessageData(v___x_592_);
return v___x_593_;
}
}
lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1(lean_object* v_arg_594_, lean_object* v_headApp_595_, lean_object* v_a_596_, lean_object* v_reject_597_, lean_object* v_args_598_, lean_object* v_body_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v___x_618_; lean_object* v_a_619_; lean_object* v___x_620_; 
v___x_618_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_body_599_, v___y_601_);
v_a_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_a_619_);
lean_dec_ref(v___x_618_);
v___x_620_ = l_Lean_Meta_whnfD(v_a_619_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v___x_622_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_a_621_);
lean_dec_ref_known(v___x_620_, 1);
v___x_622_ = l_Lean_Meta_isExprDefEq(v_a_596_, v_a_621_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; uint8_t v___x_624_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_a_623_);
lean_dec_ref_known(v___x_622_, 1);
v___x_624_ = lean_unbox(v_a_623_);
lean_dec(v_a_623_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__1);
lean_inc(v___y_603_);
lean_inc_ref(v___y_602_);
lean_inc(v___y_601_);
lean_inc_ref(v___y_600_);
v___x_626_ = lean_apply_7(v_reject_597_, lean_box(0), v___x_625_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, lean_box(0));
if (lean_obj_tag(v___x_626_) == 0)
{
lean_dec_ref_known(v___x_626_, 1);
goto v___jp_605_;
}
else
{
lean_dec(v_headApp_595_);
lean_dec_ref(v_arg_594_);
return v___x_626_;
}
}
else
{
lean_dec_ref(v_reject_597_);
goto v___jp_605_;
}
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
lean_dec_ref(v_reject_597_);
lean_dec(v_headApp_595_);
lean_dec_ref(v_arg_594_);
v_a_627_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_622_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_622_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
else
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
lean_dec_ref(v_reject_597_);
lean_dec_ref(v_a_596_);
lean_dec(v_headApp_595_);
lean_dec_ref(v_arg_594_);
v_a_635_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_642_ == 0)
{
v___x_637_ = v___x_620_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_620_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_a_635_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
v___jp_605_:
{
lean_object* v___x_606_; size_t v_sz_607_; size_t v___x_608_; lean_object* v___x_609_; 
v___x_606_ = lean_box(0);
v_sz_607_ = lean_array_size(v_args_598_);
v___x_608_ = ((size_t)0ULL);
v___x_609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3(v_arg_594_, v_headApp_595_, v_args_598_, v_sz_607_, v___x_608_, v___x_606_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_616_ == 0)
{
lean_object* v_unused_617_; 
v_unused_617_ = lean_ctor_get(v___x_609_, 0);
lean_dec(v_unused_617_);
v___x_611_ = v___x_609_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_dec(v___x_609_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v___x_606_);
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_606_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
else
{
return v___x_609_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_594_ = stack[0].m_obj;
lean_object* v_headApp_595_ = stack[1].m_obj;
lean_object* v_a_596_ = stack[2].m_obj;
lean_object* v_reject_597_ = stack[3].m_obj;
lean_object* v_args_598_ = stack[4].m_obj;
lean_object* v_body_599_ = stack[5].m_obj;
lean_object* v___y_600_ = stack[6].m_obj;
lean_object* v___y_601_ = stack[7].m_obj;
lean_object* v___y_602_ = stack[8].m_obj;
lean_object* v___y_603_ = stack[9].m_obj;
lean_object* v_res_643_;
v_res_643_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1(v_arg_594_, v_headApp_595_, v_a_596_, v_reject_597_, v_args_598_, v_body_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
stack->m_obj
 = v_res_643_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___boxed(lean_object* v_arg_644_, lean_object* v_headApp_645_, lean_object* v_a_646_, lean_object* v_reject_647_, lean_object* v_args_648_, lean_object* v_body_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1(v_arg_644_, v_headApp_645_, v_a_646_, v_reject_647_, v_args_648_, v_body_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec_ref(v_args_648_);
return v_res_655_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__0));
v___x_658_ = l_Lean_stringToMessageData(v___x_657_);
return v___x_658_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2(lean_object* v_forwarded_659_, lean_object* v_arg_660_, lean_object* v_headApp_661_, lean_object* v_as_662_, size_t v_sz_663_, size_t v_i_664_, lean_object* v_b_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v_a_672_; uint8_t v___x_676_; 
v___x_676_ = lean_usize_dec_lt(v_i_664_, v_sz_663_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; 
lean_dec(v_headApp_661_);
lean_dec_ref(v_arg_660_);
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v_b_665_);
return v___x_677_;
}
else
{
lean_object* v_a_678_; lean_object* v_fst_679_; lean_object* v_snd_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_740_; 
v_a_678_ = lean_array_uget(v_as_662_, v_i_664_);
v_fst_679_ = lean_ctor_get(v_a_678_, 0);
v_snd_680_ = lean_ctor_get(v_a_678_, 1);
v_isSharedCheck_740_ = !lean_is_exclusive(v_a_678_);
if (v_isSharedCheck_740_ == 0)
{
v___x_682_ = v_a_678_;
v_isShared_683_ = v_isSharedCheck_740_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_snd_680_);
lean_inc(v_fst_679_);
lean_dec(v_a_678_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_740_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___f_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
lean_inc_ref(v_arg_660_);
v___f_684_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_684_, 0, v_arg_660_);
v___x_685_ = lean_box(0);
v___x_686_ = l_Lean_Expr_fvarId_x21(v_fst_679_);
lean_dec(v_fst_679_);
v___x_687_ = l_Lean_FVarId_getDecl___redArg(v___x_686_, v___y_666_, v___y_668_, v___y_669_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; uint8_t v___x_689_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_a_688_);
lean_dec_ref_known(v___x_687_, 1);
v___x_689_ = l_Lean_LocalDecl_binderInfo(v_a_688_);
lean_dec(v_a_688_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_snd_680_, v___y_667_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; uint8_t v___x_692_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_a_691_);
lean_dec_ref_known(v___x_690_, 1);
v___x_692_ = lean_expr_eqv(v_a_691_, v_forwarded_659_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; 
lean_inc(v___y_669_);
lean_inc_ref(v___y_668_);
lean_inc(v___y_667_);
lean_inc_ref(v___y_666_);
v___x_693_ = lean_infer_type(v_a_691_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v___x_695_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc_n(v_a_694_, 2);
lean_dec_ref_known(v___x_693_, 1);
v___x_695_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_a_694_, v___y_667_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_a_696_);
lean_dec_ref_known(v___x_695_, 1);
v___x_697_ = lean_box(0);
v___x_698_ = l_Lean_FindMVar_main(v___f_684_, v_a_696_, v___x_697_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_dec(v_a_694_);
lean_del_object(v___x_682_);
v_a_672_ = v___x_685_;
goto v___jp_671_;
}
else
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_702_; 
lean_dec_ref_known(v___x_698_, 1);
v___x_699_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1);
v___x_700_ = l_Lean_MessageData_ofExpr(v_a_694_);
if (v_isShared_683_ == 0)
{
lean_ctor_set_tag(v___x_682_, 7);
lean_ctor_set(v___x_682_, 1, v___x_700_);
lean_ctor_set(v___x_682_, 0, v___x_699_);
v___x_702_ = v___x_682_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v___x_700_);
v___x_702_ = v_reuseFailAlloc_707_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_703_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1);
v___x_704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_702_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
lean_inc(v_headApp_661_);
v___x_705_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint(v_headApp_661_, v___x_704_);
v___x_706_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v___x_705_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_dec_ref_known(v___x_706_, 1);
v_a_672_ = v___x_685_;
goto v___jp_671_;
}
else
{
lean_dec(v_headApp_661_);
lean_dec_ref(v_arg_660_);
return v___x_706_;
}
}
}
}
else
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_dec(v_a_694_);
lean_dec_ref(v___f_684_);
lean_del_object(v___x_682_);
lean_dec(v_headApp_661_);
lean_dec_ref(v_arg_660_);
v_a_708_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_695_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_695_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
else
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
lean_dec_ref(v___f_684_);
lean_del_object(v___x_682_);
lean_dec(v_headApp_661_);
lean_dec_ref(v_arg_660_);
v_a_716_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_723_ == 0)
{
v___x_718_ = v___x_693_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_693_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_719_ == 0)
{
v___x_721_ = v___x_718_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_716_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
else
{
lean_dec(v_a_691_);
lean_dec_ref(v___f_684_);
lean_del_object(v___x_682_);
v_a_672_ = v___x_685_;
goto v___jp_671_;
}
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec_ref(v___f_684_);
lean_del_object(v___x_682_);
lean_dec(v_headApp_661_);
lean_dec_ref(v_arg_660_);
v_a_724_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_690_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_690_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
else
{
lean_dec_ref(v___f_684_);
lean_del_object(v___x_682_);
lean_dec(v_snd_680_);
v_a_672_ = v___x_685_;
goto v___jp_671_;
}
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec_ref(v___f_684_);
lean_del_object(v___x_682_);
lean_dec(v_snd_680_);
lean_dec(v_headApp_661_);
lean_dec_ref(v_arg_660_);
v_a_732_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_687_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_687_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
}
v___jp_671_:
{
size_t v___x_673_; size_t v___x_674_; 
v___x_673_ = ((size_t)1ULL);
v___x_674_ = lean_usize_add(v_i_664_, v___x_673_);
v_i_664_ = v___x_674_;
v_b_665_ = v_a_672_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_forwarded_659_ = stack[0].m_obj;
lean_object* v_arg_660_ = stack[1].m_obj;
lean_object* v_headApp_661_ = stack[2].m_obj;
lean_object* v_as_662_ = stack[3].m_obj;
size_t v_sz_663_ = stack[4].m_num;
size_t v_i_664_ = stack[5].m_num;
lean_object* v_b_665_ = stack[6].m_obj;
lean_object* v___y_666_ = stack[7].m_obj;
lean_object* v___y_667_ = stack[8].m_obj;
lean_object* v___y_668_ = stack[9].m_obj;
lean_object* v___y_669_ = stack[10].m_obj;
lean_object* v_res_741_;
v_res_741_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2(v_forwarded_659_, v_arg_660_, v_headApp_661_, v_as_662_, v_sz_663_, v_i_664_, v_b_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
stack->m_obj
 = v_res_741_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___boxed(lean_object* v_forwarded_742_, lean_object* v_arg_743_, lean_object* v_headApp_744_, lean_object* v_as_745_, lean_object* v_sz_746_, lean_object* v_i_747_, lean_object* v_b_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
size_t v_sz_boxed_754_; size_t v_i_boxed_755_; lean_object* v_res_756_; 
v_sz_boxed_754_ = lean_unbox_usize(v_sz_746_);
lean_dec(v_sz_746_);
v_i_boxed_755_ = lean_unbox_usize(v_i_747_);
lean_dec(v_i_747_);
v_res_756_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2(v_forwarded_742_, v_arg_743_, v_headApp_744_, v_as_745_, v_sz_boxed_754_, v_i_boxed_755_, v_b_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec_ref(v_as_745_);
lean_dec_ref(v_forwarded_742_);
return v_res_756_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2(lean_object* v_forwarded_757_, lean_object* v_arg_758_, lean_object* v_headApp_759_, lean_object* v_as_760_, size_t v_sz_761_, size_t v_i_762_, lean_object* v_b_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_a_770_; uint8_t v___x_774_; 
v___x_774_ = lean_usize_dec_lt(v_i_762_, v_sz_761_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; 
lean_dec(v_headApp_759_);
lean_dec_ref(v_arg_758_);
v___x_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_775_, 0, v_b_763_);
return v___x_775_;
}
else
{
lean_object* v_a_776_; lean_object* v_fst_777_; lean_object* v_snd_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_838_; 
v_a_776_ = lean_array_uget(v_as_760_, v_i_762_);
v_fst_777_ = lean_ctor_get(v_a_776_, 0);
v_snd_778_ = lean_ctor_get(v_a_776_, 1);
v_isSharedCheck_838_ = !lean_is_exclusive(v_a_776_);
if (v_isSharedCheck_838_ == 0)
{
v___x_780_ = v_a_776_;
v_isShared_781_ = v_isSharedCheck_838_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_snd_778_);
lean_inc(v_fst_777_);
lean_dec(v_a_776_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_838_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___f_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
lean_inc_ref(v_arg_758_);
v___f_782_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_782_, 0, v_arg_758_);
v___x_783_ = lean_box(0);
v___x_784_ = l_Lean_Expr_fvarId_x21(v_fst_777_);
lean_dec(v_fst_777_);
v___x_785_ = l_Lean_FVarId_getDecl___redArg(v___x_784_, v___y_764_, v___y_766_, v___y_767_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; uint8_t v___x_787_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_a_786_);
lean_dec_ref_known(v___x_785_, 1);
v___x_787_ = l_Lean_LocalDecl_binderInfo(v_a_786_);
lean_dec(v_a_786_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; 
v___x_788_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_snd_778_, v___y_765_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; uint8_t v___x_790_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_789_);
lean_dec_ref_known(v___x_788_, 1);
v___x_790_ = lean_expr_eqv(v_a_789_, v_forwarded_757_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; 
lean_inc(v___y_767_);
lean_inc_ref(v___y_766_);
lean_inc(v___y_765_);
lean_inc_ref(v___y_764_);
v___x_791_ = lean_infer_type(v_a_789_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v___x_793_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc_n(v_a_792_, 2);
lean_dec_ref_known(v___x_791_, 1);
v___x_793_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_a_792_, v___y_765_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v_a_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v_a_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_a_794_);
lean_dec_ref_known(v___x_793_, 1);
v___x_795_ = lean_box(0);
v___x_796_ = l_Lean_FindMVar_main(v___f_782_, v_a_794_, v___x_795_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_dec(v_a_792_);
lean_del_object(v___x_780_);
v_a_770_ = v___x_783_;
goto v___jp_769_;
}
else
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_800_; 
lean_dec_ref_known(v___x_796_, 1);
v___x_797_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1);
v___x_798_ = l_Lean_MessageData_ofExpr(v_a_792_);
if (v_isShared_781_ == 0)
{
lean_ctor_set_tag(v___x_780_, 7);
lean_ctor_set(v___x_780_, 1, v___x_798_);
lean_ctor_set(v___x_780_, 0, v___x_797_);
v___x_800_ = v___x_780_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v___x_798_);
v___x_800_ = v_reuseFailAlloc_805_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_801_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1);
v___x_802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_800_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
lean_inc(v_headApp_759_);
v___x_803_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint(v_headApp_759_, v___x_802_);
v___x_804_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v___x_803_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_dec_ref_known(v___x_804_, 1);
v_a_770_ = v___x_783_;
goto v___jp_769_;
}
else
{
lean_dec(v_headApp_759_);
lean_dec_ref(v_arg_758_);
return v___x_804_;
}
}
}
}
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
lean_dec(v_a_792_);
lean_dec_ref(v___f_782_);
lean_del_object(v___x_780_);
lean_dec(v_headApp_759_);
lean_dec_ref(v_arg_758_);
v_a_806_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_793_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_793_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
else
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_dec_ref(v___f_782_);
lean_del_object(v___x_780_);
lean_dec(v_headApp_759_);
lean_dec_ref(v_arg_758_);
v_a_814_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_791_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_791_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
else
{
lean_dec(v_a_789_);
lean_dec_ref(v___f_782_);
lean_del_object(v___x_780_);
v_a_770_ = v___x_783_;
goto v___jp_769_;
}
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
lean_dec_ref(v___f_782_);
lean_del_object(v___x_780_);
lean_dec(v_headApp_759_);
lean_dec_ref(v_arg_758_);
v_a_822_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_788_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_788_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
else
{
lean_dec_ref(v___f_782_);
lean_del_object(v___x_780_);
lean_dec(v_snd_778_);
v_a_770_ = v___x_783_;
goto v___jp_769_;
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec_ref(v___f_782_);
lean_del_object(v___x_780_);
lean_dec(v_snd_778_);
lean_dec(v_headApp_759_);
lean_dec_ref(v_arg_758_);
v_a_830_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_785_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_785_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
}
v___jp_769_:
{
size_t v___x_771_; size_t v___x_772_; lean_object* v___x_773_; 
v___x_771_ = ((size_t)1ULL);
v___x_772_ = lean_usize_add(v_i_762_, v___x_771_);
v___x_773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2(v_forwarded_757_, v_arg_758_, v_headApp_759_, v_as_760_, v_sz_761_, v___x_772_, v_a_770_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
return v___x_773_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_forwarded_757_ = stack[0].m_obj;
lean_object* v_arg_758_ = stack[1].m_obj;
lean_object* v_headApp_759_ = stack[2].m_obj;
lean_object* v_as_760_ = stack[3].m_obj;
size_t v_sz_761_ = stack[4].m_num;
size_t v_i_762_ = stack[5].m_num;
lean_object* v_b_763_ = stack[6].m_obj;
lean_object* v___y_764_ = stack[7].m_obj;
lean_object* v___y_765_ = stack[8].m_obj;
lean_object* v___y_766_ = stack[9].m_obj;
lean_object* v___y_767_ = stack[10].m_obj;
lean_object* v_res_839_;
v_res_839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2(v_forwarded_757_, v_arg_758_, v_headApp_759_, v_as_760_, v_sz_761_, v_i_762_, v_b_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
stack->m_obj
 = v_res_839_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___boxed(lean_object* v_forwarded_840_, lean_object* v_arg_841_, lean_object* v_headApp_842_, lean_object* v_as_843_, lean_object* v_sz_844_, lean_object* v_i_845_, lean_object* v_b_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
size_t v_sz_boxed_852_; size_t v_i_boxed_853_; lean_object* v_res_854_; 
v_sz_boxed_852_ = lean_unbox_usize(v_sz_844_);
lean_dec(v_sz_844_);
v_i_boxed_853_ = lean_unbox_usize(v_i_845_);
lean_dec(v_i_845_);
v_res_854_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2(v_forwarded_840_, v_arg_841_, v_headApp_842_, v_as_843_, v_sz_boxed_852_, v_i_boxed_853_, v_b_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec_ref(v_as_843_);
lean_dec_ref(v_forwarded_840_);
return v_res_854_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___closed__0(void){
_start:
{
lean_object* v___x_855_; lean_object* v_dummy_856_; 
v___x_855_ = lean_box(0);
v_dummy_856_ = l_Lean_Expr_sort___override(v___x_855_);
return v_dummy_856_;
}
}
lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2(lean_object* v_probeExpr_857_, lean_object* v_forwarded_858_, lean_object* v_arg_859_, lean_object* v_headApp_860_, lean_object* v_fvars_861_, lean_object* v_x_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v_dummy_868_; lean_object* v_nargs_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; size_t v_sz_876_; size_t v___x_877_; lean_object* v___x_878_; 
v_dummy_868_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___closed__0, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___closed__0_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___closed__0);
v_nargs_869_ = l_Lean_Expr_getAppNumArgs(v_probeExpr_857_);
lean_inc(v_nargs_869_);
v___x_870_ = lean_mk_array(v_nargs_869_, v_dummy_868_);
v___x_871_ = lean_unsigned_to_nat(1u);
v___x_872_ = lean_nat_sub(v_nargs_869_, v___x_871_);
lean_dec(v_nargs_869_);
v___x_873_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_probeExpr_857_, v___x_870_, v___x_872_);
v___x_874_ = l_Array_zip___redArg(v_fvars_861_, v___x_873_);
lean_dec_ref(v___x_873_);
v___x_875_ = lean_box(0);
v_sz_876_ = lean_array_size(v___x_874_);
v___x_877_ = ((size_t)0ULL);
v___x_878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2(v_forwarded_858_, v_arg_859_, v_headApp_860_, v___x_874_, v_sz_876_, v___x_877_, v___x_875_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
lean_dec_ref(v___x_874_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_885_ == 0)
{
lean_object* v_unused_886_; 
v_unused_886_ = lean_ctor_get(v___x_878_, 0);
lean_dec(v_unused_886_);
v___x_880_ = v___x_878_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_dec(v___x_878_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v___x_875_);
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_875_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
else
{
return v___x_878_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_probeExpr_857_ = stack[0].m_obj;
lean_object* v_forwarded_858_ = stack[1].m_obj;
lean_object* v_arg_859_ = stack[2].m_obj;
lean_object* v_headApp_860_ = stack[3].m_obj;
lean_object* v_fvars_861_ = stack[4].m_obj;
lean_object* v_x_862_ = stack[5].m_obj;
lean_object* v___y_863_ = stack[6].m_obj;
lean_object* v___y_864_ = stack[7].m_obj;
lean_object* v___y_865_ = stack[8].m_obj;
lean_object* v___y_866_ = stack[9].m_obj;
lean_object* v_res_887_;
v_res_887_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2(v_probeExpr_857_, v_forwarded_858_, v_arg_859_, v_headApp_860_, v_fvars_861_, v_x_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
stack->m_obj
 = v_res_887_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___boxed(lean_object* v_probeExpr_888_, lean_object* v_forwarded_889_, lean_object* v_arg_890_, lean_object* v_headApp_891_, lean_object* v_fvars_892_, lean_object* v_x_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2(v_probeExpr_888_, v_forwarded_889_, v_arg_890_, v_headApp_891_, v_fvars_892_, v_x_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec_ref(v_x_893_);
lean_dec_ref(v_fvars_892_);
lean_dec_ref(v_forwarded_889_);
return v_res_899_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__1(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__0));
v___x_902_ = l_Lean_stringToMessageData(v___x_901_);
return v___x_902_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__3(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__2));
v___x_905_ = l_Lean_stringToMessageData(v___x_904_);
return v___x_905_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__5(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__4));
v___x_908_ = l_Lean_stringToMessageData(v___x_907_);
return v___x_908_;
}
}
lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder(lean_object* v_headApp_909_, lean_object* v_forwarded_910_, lean_object* v_probeExpr_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_){
_start:
{
lean_object* v_reject_917_; lean_object* v___x_918_; 
lean_inc(v_headApp_909_);
v_reject_917_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0___boxed), 8, 1);
lean_closure_set(v_reject_917_, 0, v_headApp_909_);
lean_inc(v_a_915_);
lean_inc_ref(v_a_914_);
lean_inc(v_a_913_);
lean_inc_ref(v_a_912_);
lean_inc_ref(v_probeExpr_911_);
v___x_918_ = lean_infer_type(v_probeExpr_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v_a_919_; lean_object* v___x_920_; lean_object* v_a_921_; lean_object* v___x_922_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
lean_inc(v_a_919_);
lean_dec_ref_known(v___x_918_, 1);
v___x_920_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_a_919_, v_a_913_);
v_a_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_921_);
lean_dec_ref(v___x_920_);
v___x_922_ = l_Lean_Meta_whnfD(v_a_921_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc(v_a_923_);
lean_dec_ref_known(v___x_922_, 1);
if (lean_obj_tag(v_a_923_) == 5)
{
lean_object* v_arg_924_; lean_object* v___f_925_; lean_object* v___f_926_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_931_; uint8_t v___x_956_; 
v_arg_924_ = lean_ctor_get(v_a_923_, 1);
lean_inc_ref_n(v_arg_924_, 3);
lean_inc_n(v_headApp_909_, 2);
v___f_925_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___boxed), 11, 4);
lean_closure_set(v___f_925_, 0, v_arg_924_);
lean_closure_set(v___f_925_, 1, v_headApp_909_);
lean_closure_set(v___f_925_, 2, v_a_923_);
lean_closure_set(v___f_925_, 3, v_reject_917_);
lean_inc_ref(v_forwarded_910_);
lean_inc_ref(v_probeExpr_911_);
v___f_926_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___boxed), 11, 4);
lean_closure_set(v___f_926_, 0, v_probeExpr_911_);
lean_closure_set(v___f_926_, 1, v_forwarded_910_);
lean_closure_set(v___f_926_, 2, v_arg_924_);
lean_closure_set(v___f_926_, 3, v_headApp_909_);
v___x_956_ = l_Lean_Expr_isMVar(v_arg_924_);
lean_dec_ref(v_arg_924_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; lean_object* v___x_958_; 
lean_dec_ref(v___f_926_);
lean_dec_ref(v___f_925_);
lean_dec_ref(v_probeExpr_911_);
lean_dec_ref(v_forwarded_910_);
v___x_957_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__1);
v___x_958_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0(v_headApp_909_, lean_box(0), v___x_957_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
return v___x_958_;
}
else
{
lean_dec(v_headApp_909_);
v___y_928_ = v_a_912_;
v___y_929_ = v_a_913_;
v___y_930_ = v_a_914_;
v___y_931_ = v_a_915_;
goto v___jp_927_;
}
v___jp_927_:
{
lean_object* v___x_932_; 
lean_inc(v___y_931_);
lean_inc_ref(v___y_930_);
lean_inc(v___y_929_);
lean_inc_ref(v___y_928_);
v___x_932_ = lean_infer_type(v_forwarded_910_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; uint8_t v___x_934_; lean_object* v___x_935_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_a_933_);
lean_dec_ref_known(v___x_932_, 1);
v___x_934_ = 0;
v___x_935_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg(v_a_933_, v___f_925_, v___x_934_, v___x_934_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v___x_936_; lean_object* v___x_937_; 
lean_dec_ref_known(v___x_935_, 1);
v___x_936_ = l_Lean_Expr_getAppFn(v_probeExpr_911_);
lean_dec_ref(v_probeExpr_911_);
lean_inc(v___y_931_);
lean_inc_ref(v___y_930_);
lean_inc(v___y_929_);
lean_inc_ref(v___y_928_);
v___x_937_ = lean_infer_type(v___x_936_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; lean_object* v___x_939_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_a_938_);
lean_dec_ref_known(v___x_937_, 1);
v___x_939_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg(v_a_938_, v___f_926_, v___x_934_, v___x_934_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
return v___x_939_;
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
lean_dec_ref(v___f_926_);
v_a_940_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_937_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_937_);
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
lean_dec_ref(v___f_926_);
lean_dec_ref(v_probeExpr_911_);
return v___x_935_;
}
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec_ref(v___f_926_);
lean_dec_ref(v___f_925_);
lean_dec_ref(v_probeExpr_911_);
v_a_948_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_932_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_932_);
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
else
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
lean_dec_ref(v_reject_917_);
lean_dec_ref(v_probeExpr_911_);
lean_dec_ref(v_forwarded_910_);
v___x_959_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__3, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__3);
v___x_960_ = l_Lean_MessageData_ofExpr(v_a_923_);
v___x_961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_959_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__5, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__5_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__5);
v___x_963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_961_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0(v_headApp_909_, lean_box(0), v___x_963_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
return v___x_964_;
}
}
else
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_972_; 
lean_dec_ref(v_reject_917_);
lean_dec_ref(v_probeExpr_911_);
lean_dec_ref(v_forwarded_910_);
lean_dec(v_headApp_909_);
v_a_965_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_972_ == 0)
{
v___x_967_ = v___x_922_;
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_922_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_965_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
lean_dec_ref(v_reject_917_);
lean_dec_ref(v_probeExpr_911_);
lean_dec_ref(v_forwarded_910_);
lean_dec(v_headApp_909_);
v_a_973_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_918_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_918_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_0interp(lean_interpreter_value* stack)
{
lean_object* v_headApp_909_ = stack[0].m_obj;
lean_object* v_forwarded_910_ = stack[1].m_obj;
lean_object* v_probeExpr_911_ = stack[2].m_obj;
lean_object* v_a_912_ = stack[3].m_obj;
lean_object* v_a_913_ = stack[4].m_obj;
lean_object* v_a_914_ = stack[5].m_obj;
lean_object* v_a_915_ = stack[6].m_obj;
lean_object* v_res_981_;
v_res_981_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder(v_headApp_909_, v_forwarded_910_, v_probeExpr_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
stack->m_obj
 = v_res_981_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___boxed(lean_object* v_headApp_982_, lean_object* v_forwarded_983_, lean_object* v_probeExpr_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder(v_headApp_982_, v_forwarded_983_, v_probeExpr_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
return v_res_990_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0(lean_object* v_00_u03b1_991_, lean_object* v_msg_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v_msg_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
return v___x_998_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_992_ = stack[1].m_obj;
lean_object* v___y_993_ = stack[2].m_obj;
lean_object* v___y_994_ = stack[3].m_obj;
lean_object* v___y_995_ = stack[4].m_obj;
lean_object* v___y_996_ = stack[5].m_obj;
lean_object* v_res_999_;
v_res_999_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0(lean_box(0), v_msg_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
stack->m_obj
 = v_res_999_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___boxed(lean_object* v_00_u03b1_1000_, lean_object* v_msg_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0(v_00_u03b1_1000_, v_msg_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
return v_res_1007_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___redArg(lean_object* v_e_1008_, lean_object* v___y_1009_){
_start:
{
uint8_t v___x_1011_; 
v___x_1011_ = l_Lean_Expr_hasMVar(v_e_1008_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; 
v___x_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1012_, 0, v_e_1008_);
return v___x_1012_;
}
else
{
lean_object* v___x_1013_; lean_object* v_mctx_1014_; lean_object* v___x_1015_; lean_object* v_fst_1016_; lean_object* v_snd_1017_; lean_object* v___x_1018_; lean_object* v_cache_1019_; lean_object* v_zetaDeltaFVarIds_1020_; lean_object* v_postponed_1021_; lean_object* v_diag_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1031_; 
v___x_1013_ = lean_st_ref_get(v___y_1009_);
v_mctx_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc_ref(v_mctx_1014_);
lean_dec(v___x_1013_);
v___x_1015_ = l_Lean_instantiateMVarsCore(v_mctx_1014_, v_e_1008_);
v_fst_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_fst_1016_);
v_snd_1017_ = lean_ctor_get(v___x_1015_, 1);
lean_inc(v_snd_1017_);
lean_dec_ref(v___x_1015_);
v___x_1018_ = lean_st_ref_take(v___y_1009_);
v_cache_1019_ = lean_ctor_get(v___x_1018_, 1);
v_zetaDeltaFVarIds_1020_ = lean_ctor_get(v___x_1018_, 2);
v_postponed_1021_ = lean_ctor_get(v___x_1018_, 3);
v_diag_1022_ = lean_ctor_get(v___x_1018_, 4);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1031_ == 0)
{
lean_object* v_unused_1032_; 
v_unused_1032_ = lean_ctor_get(v___x_1018_, 0);
lean_dec(v_unused_1032_);
v___x_1024_ = v___x_1018_;
v_isShared_1025_ = v_isSharedCheck_1031_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_diag_1022_);
lean_inc(v_postponed_1021_);
lean_inc(v_zetaDeltaFVarIds_1020_);
lean_inc(v_cache_1019_);
lean_dec(v___x_1018_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1031_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 0, v_snd_1017_);
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_snd_1017_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_cache_1019_);
lean_ctor_set(v_reuseFailAlloc_1030_, 2, v_zetaDeltaFVarIds_1020_);
lean_ctor_set(v_reuseFailAlloc_1030_, 3, v_postponed_1021_);
lean_ctor_set(v_reuseFailAlloc_1030_, 4, v_diag_1022_);
v___x_1027_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = lean_st_ref_put(v___y_1009_, v___x_1027_);
v___x_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1029_, 0, v_fst_1016_);
return v___x_1029_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1008_ = stack[0].m_obj;
lean_object* v___y_1009_ = stack[1].m_obj;
lean_object* v_res_1033_;
v_res_1033_ = l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___redArg(v_e_1008_, v___y_1009_);
stack->m_obj
 = v_res_1033_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___redArg___boxed(lean_object* v_e_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___redArg(v_e_1034_, v___y_1035_);
lean_dec(v___y_1035_);
return v_res_1037_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1(lean_object* v_e_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___redArg(v_e_1038_, v___y_1042_);
return v___x_1046_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1038_ = stack[0].m_obj;
lean_object* v___y_1039_ = stack[1].m_obj;
lean_object* v___y_1040_ = stack[2].m_obj;
lean_object* v___y_1041_ = stack[3].m_obj;
lean_object* v___y_1042_ = stack[4].m_obj;
lean_object* v___y_1043_ = stack[5].m_obj;
lean_object* v___y_1044_ = stack[6].m_obj;
lean_object* v_res_1047_;
v_res_1047_ = l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1(v_e_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
stack->m_obj
 = v_res_1047_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___boxed(lean_object* v_e_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1(v_e_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
return v_res_1056_;
}
}
static lean_object* _init_l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__3));
v___x_1066_ = l_String_toRawSubstring_x27(v___x_1065_);
return v___x_1066_;
}
}
lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0(lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_fst_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v_toCold_1086_; lean_object* v_ref_1087_; lean_object* v_quotContext_1088_; lean_object* v_currMacroScope_1089_; uint8_t v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; uint8_t v___x_1102_; lean_object* v___x_1103_; 
v_toCold_1086_ = lean_ctor_get(v___y_1083_, 0);
v_ref_1087_ = lean_ctor_get(v___y_1083_, 2);
v_quotContext_1088_ = lean_ctor_get(v_toCold_1086_, 8);
v_currMacroScope_1089_ = lean_ctor_get(v_toCold_1086_, 9);
v___x_1090_ = 0;
v___x_1091_ = l_Lean_SourceInfo_fromRef(v_ref_1087_, v___x_1090_);
v___x_1092_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__1));
v___x_1093_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__2));
lean_inc_n(v___x_1091_, 3);
v___x_1094_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1091_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
v___x_1095_ = lean_obj_once(&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__4, &l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__4_once, _init_l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__4);
v___x_1096_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__5));
lean_inc(v_currMacroScope_1089_);
lean_inc(v_quotContext_1088_);
v___x_1097_ = l_Lean_addMacroScope(v_quotContext_1088_, v___x_1096_, v_currMacroScope_1089_);
v___x_1098_ = lean_box(0);
v___x_1099_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1091_);
lean_ctor_set(v___x_1099_, 1, v___x_1095_);
lean_ctor_set(v___x_1099_, 2, v___x_1097_);
lean_ctor_set(v___x_1099_, 3, v___x_1098_);
v___x_1100_ = l_Lean_Syntax_node2(v___x_1091_, v___x_1092_, v___x_1094_, v___x_1099_);
v___x_1101_ = lean_box(0);
v___x_1102_ = 1;
lean_inc(v___x_1100_);
v___x_1103_ = l_Lean_Elab_Term_elabTerm(v___x_1100_, v___x_1101_, v___x_1102_, v___x_1102_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v___y_1083_, v___y_1084_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_a_1104_);
lean_dec_ref_known(v___x_1103_, 1);
v___x_1105_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__7));
v___x_1106_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__9));
lean_inc(v___x_1091_);
v___x_1107_ = l_Lean_Syntax_node1(v___x_1091_, v___x_1106_, v___x_1100_);
v___x_1108_ = l_Lean_Syntax_node2(v___x_1091_, v___x_1105_, v_fst_1082_, v___x_1107_);
v___x_1109_ = l_Lean_Elab_Term_elabTerm(v___x_1108_, v___x_1101_, v___x_1102_, v___x_1102_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v___y_1083_, v___y_1084_);
lean_dec_ref(v___y_1083_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1118_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1112_ = v___x_1109_;
v_isShared_1113_ = v_isSharedCheck_1118_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1109_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1118_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1114_; lean_object* v___x_1116_; 
v___x_1114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1114_, 0, v_a_1104_);
lean_ctor_set(v___x_1114_, 1, v_a_1110_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v___x_1114_);
v___x_1116_ = v___x_1112_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1114_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_dec(v_a_1104_);
v_a_1119_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1109_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1109_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_dec(v___x_1100_);
lean_dec(v___x_1091_);
lean_dec_ref(v___y_1083_);
lean_dec(v_fst_1082_);
v_a_1127_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1103_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1103_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1078_ = stack[0].m_obj;
lean_object* v_a_1079_ = stack[1].m_obj;
lean_object* v_a_1080_ = stack[2].m_obj;
lean_object* v_a_1081_ = stack[3].m_obj;
lean_object* v_fst_1082_ = stack[4].m_obj;
lean_object* v___y_1083_ = stack[5].m_obj;
lean_object* v___y_1084_ = stack[6].m_obj;
lean_object* v_res_1135_;
v_res_1135_ = l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0(v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_fst_1082_, v___y_1083_, v___y_1084_);
stack->m_obj
 = v_res_1135_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___boxed(lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_fst_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0(v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_fst_1140_, v___y_1141_, v___y_1142_);
lean_dec(v___y_1142_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec(v_a_1137_);
lean_dec_ref(v_a_1136_);
return v_res_1144_;
}
}
lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__1(lean_object* v_body_1145_, lean_object* v_cont_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
uint8_t v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = 1;
v___x_1156_ = l_Lean_Elab_Do_elabDoSeq(v_body_1145_, v_cont_1146_, v___x_1155_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
return v___x_1156_;
}
}
LEAN_EXPORT void l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_body_1145_ = stack[0].m_obj;
lean_object* v_cont_1146_ = stack[1].m_obj;
lean_object* v___y_1147_ = stack[2].m_obj;
lean_object* v___y_1148_ = stack[3].m_obj;
lean_object* v___y_1149_ = stack[4].m_obj;
lean_object* v___y_1150_ = stack[5].m_obj;
lean_object* v___y_1151_ = stack[6].m_obj;
lean_object* v___y_1152_ = stack[7].m_obj;
lean_object* v___y_1153_ = stack[8].m_obj;
lean_object* v_res_1157_;
v_res_1157_ = l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__1(v_body_1145_, v_cont_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
stack->m_obj
 = v_res_1157_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__1___boxed(lean_object* v_body_1158_, lean_object* v_cont_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__1(v_body_1158_, v_cont_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec_ref(v___y_1160_);
return v_res_1168_;
}
}
lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__2(lean_object* v_a_1169_, lean_object* v___f_1170_, lean_object* v_a_1171_, lean_object* v_bsExpr_1172_, lean_object* v_x_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l_Lean_Elab_Do_EffectForwarder_lift(v_a_1169_, v___f_1170_, v_a_1171_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; uint8_t v___x_1183_; uint8_t v___x_1184_; uint8_t v___x_1185_; lean_object* v___x_1186_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_a_1182_);
lean_dec_ref_known(v___x_1181_, 1);
v___x_1183_ = 0;
v___x_1184_ = 1;
v___x_1185_ = 1;
v___x_1186_ = l_Lean_Meta_mkLambdaFVars(v_bsExpr_1172_, v_a_1182_, v___x_1183_, v___x_1184_, v___x_1183_, v___x_1184_, v___x_1185_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
return v___x_1186_;
}
else
{
return v___x_1181_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1169_ = stack[0].m_obj;
lean_object* v___f_1170_ = stack[1].m_obj;
lean_object* v_a_1171_ = stack[2].m_obj;
lean_object* v_bsExpr_1172_ = stack[3].m_obj;
lean_object* v_x_1173_ = stack[4].m_obj;
lean_object* v___y_1174_ = stack[5].m_obj;
lean_object* v___y_1175_ = stack[6].m_obj;
lean_object* v___y_1176_ = stack[7].m_obj;
lean_object* v___y_1177_ = stack[8].m_obj;
lean_object* v___y_1178_ = stack[9].m_obj;
lean_object* v___y_1179_ = stack[10].m_obj;
lean_object* v_res_1187_;
v_res_1187_ = l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__2(v_a_1169_, v___f_1170_, v_a_1171_, v_bsExpr_1172_, v_x_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
stack->m_obj
 = v_res_1187_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__2___boxed(lean_object* v_a_1188_, lean_object* v___f_1189_, lean_object* v_a_1190_, lean_object* v_bsExpr_1191_, lean_object* v_x_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__2(v_a_1188_, v___f_1189_, v_a_1190_, v_bsExpr_1191_, v_x_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v_x_1192_);
lean_dec_ref(v_bsExpr_1191_);
lean_dec_ref(v_a_1190_);
return v_res_1200_;
}
}
lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__3(lean_object* v_a_1201_, lean_object* v_fst_1202_, lean_object* v___f_1203_, lean_object* v_____r_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1212_, 0, v_a_1201_);
v___x_1213_ = l_Lean_Elab_Term_elabFunBinders___redArg(v_fst_1202_, v___x_1212_, v___f_1203_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
return v___x_1213_;
}
}
LEAN_EXPORT void l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1201_ = stack[0].m_obj;
lean_object* v_fst_1202_ = stack[1].m_obj;
lean_object* v___f_1203_ = stack[2].m_obj;
lean_object* v_____r_1204_ = stack[3].m_obj;
lean_object* v___y_1205_ = stack[4].m_obj;
lean_object* v___y_1206_ = stack[5].m_obj;
lean_object* v___y_1207_ = stack[6].m_obj;
lean_object* v___y_1208_ = stack[7].m_obj;
lean_object* v___y_1209_ = stack[8].m_obj;
lean_object* v___y_1210_ = stack[9].m_obj;
lean_object* v_res_1214_;
v_res_1214_ = l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__3(v_a_1201_, v_fst_1202_, v___f_1203_, v_____r_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
stack->m_obj
 = v_res_1214_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__3___boxed(lean_object* v_a_1215_, lean_object* v_fst_1216_, lean_object* v___f_1217_, lean_object* v_____r_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__3(v_a_1215_, v_fst_1216_, v___f_1217_, v_____r_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec_ref(v_fst_1216_);
return v_res_1226_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0___redArg(lean_object* v_msg_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v_ref_1233_; lean_object* v___x_1234_; lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1243_; 
v_ref_1233_ = lean_ctor_get(v___y_1230_, 2);
v___x_1234_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0(v_msg_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1237_ = v___x_1234_;
v_isShared_1238_ = v_isSharedCheck_1243_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1234_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1243_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1239_; lean_object* v___x_1241_; 
lean_inc(v_ref_1233_);
v___x_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1239_, 0, v_ref_1233_);
lean_ctor_set(v___x_1239_, 1, v_a_1235_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set_tag(v___x_1237_, 1);
lean_ctor_set(v___x_1237_, 0, v___x_1239_);
v___x_1241_ = v___x_1237_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1239_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1227_ = stack[0].m_obj;
lean_object* v___y_1228_ = stack[1].m_obj;
lean_object* v___y_1229_ = stack[2].m_obj;
lean_object* v___y_1230_ = stack[3].m_obj;
lean_object* v___y_1231_ = stack[4].m_obj;
lean_object* v_res_1244_;
v_res_1244_ = l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0___redArg(v_msg_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
stack->m_obj
 = v_res_1244_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0___redArg___boxed(lean_object* v_msg_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0___redArg(v_msg_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
return v_res_1251_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__2(size_t v_sz_1252_, size_t v_i_1253_, lean_object* v_bs_1254_){
_start:
{
uint8_t v___x_1255_; 
v___x_1255_ = lean_usize_dec_lt(v_i_1253_, v_sz_1252_);
if (v___x_1255_ == 0)
{
return v_bs_1254_;
}
else
{
lean_object* v_v_1256_; lean_object* v___x_1257_; lean_object* v_bs_x27_1258_; size_t v___x_1259_; size_t v___x_1260_; lean_object* v___x_1261_; 
v_v_1256_ = lean_array_uget(v_bs_1254_, v_i_1253_);
v___x_1257_ = lean_unsigned_to_nat(0u);
v_bs_x27_1258_ = lean_array_uset(v_bs_1254_, v_i_1253_, v___x_1257_);
v___x_1259_ = ((size_t)1ULL);
v___x_1260_ = lean_usize_add(v_i_1253_, v___x_1259_);
v___x_1261_ = lean_array_uset(v_bs_x27_1258_, v_i_1253_, v_v_1256_);
v_i_1253_ = v___x_1260_;
v_bs_1254_ = v___x_1261_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1252_ = stack[0].m_num;
size_t v_i_1253_ = stack[1].m_num;
lean_object* v_bs_1254_ = stack[2].m_obj;
lean_object* v_res_1263_;
v_res_1263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__2(v_sz_1252_, v_i_1253_, v_bs_1254_);
stack->m_obj
 = v_res_1263_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__2___boxed(lean_object* v_sz_1264_, lean_object* v_i_1265_, lean_object* v_bs_1266_){
_start:
{
size_t v_sz_boxed_1267_; size_t v_i_boxed_1268_; lean_object* v_res_1269_; 
v_sz_boxed_1267_ = lean_unbox_usize(v_sz_1264_);
lean_dec(v_sz_1264_);
v_i_boxed_1268_ = lean_unbox_usize(v_i_1265_);
lean_dec(v_i_1265_);
v_res_1269_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__2(v_sz_boxed_1267_, v_i_boxed_1268_, v_bs_1266_);
return v_res_1269_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16___redArg(lean_object* v_keys_1270_, lean_object* v_i_1271_, lean_object* v_k_1272_){
_start:
{
lean_object* v___x_1273_; uint8_t v___x_1274_; 
v___x_1273_ = lean_array_get_size(v_keys_1270_);
v___x_1274_ = lean_nat_dec_lt(v_i_1271_, v___x_1273_);
if (v___x_1274_ == 0)
{
lean_dec(v_i_1271_);
return v___x_1274_;
}
else
{
lean_object* v_k_x27_1275_; uint8_t v___x_1276_; 
v_k_x27_1275_ = lean_array_fget_borrowed(v_keys_1270_, v_i_1271_);
v___x_1276_ = l_Lean_instBEqExtraModUse_beq(v_k_1272_, v_k_x27_1275_);
if (v___x_1276_ == 0)
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = lean_unsigned_to_nat(1u);
v___x_1278_ = lean_nat_add(v_i_1271_, v___x_1277_);
lean_dec(v_i_1271_);
v_i_1271_ = v___x_1278_;
goto _start;
}
else
{
lean_dec(v_i_1271_);
return v___x_1274_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_1270_ = stack[0].m_obj;
lean_object* v_i_1271_ = stack[1].m_obj;
lean_object* v_k_1272_ = stack[2].m_obj;
uint8_t v_res_1280_;
v_res_1280_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16___redArg(v_keys_1270_, v_i_1271_, v_k_1272_);
stack->m_num = v_res_1280_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16___redArg___boxed(lean_object* v_keys_1281_, lean_object* v_i_1282_, lean_object* v_k_1283_){
_start:
{
uint8_t v_res_1284_; lean_object* v_r_1285_; 
v_res_1284_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16___redArg(v_keys_1281_, v_i_1282_, v_k_1283_);
lean_dec_ref(v_k_1283_);
lean_dec_ref(v_keys_1281_);
v_r_1285_ = lean_box(v_res_1284_);
return v_r_1285_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13___redArg(lean_object* v_x_1286_, size_t v_x_1287_, lean_object* v_x_1288_){
_start:
{
if (lean_obj_tag(v_x_1286_) == 0)
{
lean_object* v_es_1289_; lean_object* v___x_1290_; size_t v___x_1291_; size_t v___x_1292_; lean_object* v_j_1293_; lean_object* v___x_1294_; 
v_es_1289_ = lean_ctor_get(v_x_1286_, 0);
v___x_1290_ = lean_box(2);
v___x_1291_ = ((size_t)31ULL);
v___x_1292_ = lean_usize_land(v_x_1287_, v___x_1291_);
v_j_1293_ = lean_usize_to_nat(v___x_1292_);
v___x_1294_ = lean_array_get_borrowed(v___x_1290_, v_es_1289_, v_j_1293_);
lean_dec(v_j_1293_);
switch(lean_obj_tag(v___x_1294_))
{
case 0:
{
lean_object* v_key_1295_; uint8_t v___x_1296_; 
v_key_1295_ = lean_ctor_get(v___x_1294_, 0);
v___x_1296_ = l_Lean_instBEqExtraModUse_beq(v_x_1288_, v_key_1295_);
return v___x_1296_;
}
case 1:
{
lean_object* v_node_1297_; size_t v___x_1298_; size_t v___x_1299_; 
v_node_1297_ = lean_ctor_get(v___x_1294_, 0);
v___x_1298_ = ((size_t)5ULL);
v___x_1299_ = lean_usize_shift_right(v_x_1287_, v___x_1298_);
v_x_1286_ = v_node_1297_;
v_x_1287_ = v___x_1299_;
goto _start;
}
default: 
{
uint8_t v___x_1301_; 
v___x_1301_ = 0;
return v___x_1301_;
}
}
}
else
{
lean_object* v_ks_1302_; lean_object* v___x_1303_; uint8_t v___x_1304_; 
v_ks_1302_ = lean_ctor_get(v_x_1286_, 0);
v___x_1303_ = lean_unsigned_to_nat(0u);
v___x_1304_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16___redArg(v_ks_1302_, v___x_1303_, v_x_1288_);
return v___x_1304_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1286_ = stack[0].m_obj;
size_t v_x_1287_ = stack[1].m_num;
lean_object* v_x_1288_ = stack[2].m_obj;
uint8_t v_res_1305_;
v_res_1305_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13___redArg(v_x_1286_, v_x_1287_, v_x_1288_);
stack->m_num = v_res_1305_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13___redArg___boxed(lean_object* v_x_1306_, lean_object* v_x_1307_, lean_object* v_x_1308_){
_start:
{
size_t v_x_28528__boxed_1309_; uint8_t v_res_1310_; lean_object* v_r_1311_; 
v_x_28528__boxed_1309_ = lean_unbox_usize(v_x_1307_);
lean_dec(v_x_1307_);
v_res_1310_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13___redArg(v_x_1306_, v_x_28528__boxed_1309_, v_x_1308_);
lean_dec_ref(v_x_1308_);
lean_dec_ref(v_x_1306_);
v_r_1311_ = lean_box(v_res_1310_);
return v_r_1311_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9___redArg(lean_object* v_x_1312_, lean_object* v_x_1313_){
_start:
{
uint64_t v___x_1314_; size_t v___x_1315_; uint8_t v___x_1316_; 
v___x_1314_ = l_Lean_instHashableExtraModUse_hash(v_x_1313_);
v___x_1315_ = lean_uint64_to_usize(v___x_1314_);
v___x_1316_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13___redArg(v_x_1312_, v___x_1315_, v_x_1313_);
return v___x_1316_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1312_ = stack[0].m_obj;
lean_object* v_x_1313_ = stack[1].m_obj;
uint8_t v_res_1317_;
v_res_1317_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9___redArg(v_x_1312_, v_x_1313_);
stack->m_num = v_res_1317_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9___redArg___boxed(lean_object* v_x_1318_, lean_object* v_x_1319_){
_start:
{
uint8_t v_res_1320_; lean_object* v_r_1321_; 
v_res_1320_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9___redArg(v_x_1318_, v_x_1319_);
lean_dec_ref(v_x_1319_);
lean_dec_ref(v_x_1318_);
v_r_1321_ = lean_box(v_res_1320_);
return v_r_1321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___lam__0(lean_object* v___x_1322_, lean_object* v_entry_1323_, lean_object* v_s_1324_){
_start:
{
lean_object* v_addEntryFn_1325_; lean_object* v_importedEntries_1326_; lean_object* v_state_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1335_; 
v_addEntryFn_1325_ = lean_ctor_get(v___x_1322_, 3);
lean_inc(v_addEntryFn_1325_);
lean_dec_ref(v___x_1322_);
v_importedEntries_1326_ = lean_ctor_get(v_s_1324_, 0);
v_state_1327_ = lean_ctor_get(v_s_1324_, 1);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_s_1324_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1329_ = v_s_1324_;
v_isShared_1330_ = v_isSharedCheck_1335_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_state_1327_);
lean_inc(v_importedEntries_1326_);
lean_dec(v_s_1324_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1335_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v_state_1331_; lean_object* v___x_1333_; 
v_state_1331_ = lean_apply_2(v_addEntryFn_1325_, v_state_1327_, v_entry_1323_);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 1, v_state_1331_);
v___x_1333_ = v___x_1329_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_importedEntries_1326_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_state_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1336_; double v___x_1337_; 
v___x_1336_ = lean_unsigned_to_nat(0u);
v___x_1337_ = lean_float_of_nat(v___x_1336_);
return v___x_1337_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg(lean_object* v_cls_1341_, lean_object* v_msg_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v_ref_1348_; lean_object* v___x_1349_; lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1395_; 
v_ref_1348_ = lean_ctor_get(v___y_1345_, 2);
v___x_1349_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0(v_msg_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1352_ = v___x_1349_;
v_isShared_1353_ = v_isSharedCheck_1395_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1349_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1395_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1354_; lean_object* v_traceState_1355_; lean_object* v_env_1356_; lean_object* v_nextMacroScope_1357_; lean_object* v_ngen_1358_; lean_object* v_auxDeclNGen_1359_; lean_object* v_cache_1360_; lean_object* v_recordedDeps_1361_; lean_object* v_messages_1362_; lean_object* v_infoState_1363_; lean_object* v_snapshotTasks_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1394_; 
v___x_1354_ = lean_st_ref_take(v___y_1346_);
v_traceState_1355_ = lean_ctor_get(v___x_1354_, 4);
v_env_1356_ = lean_ctor_get(v___x_1354_, 0);
v_nextMacroScope_1357_ = lean_ctor_get(v___x_1354_, 1);
v_ngen_1358_ = lean_ctor_get(v___x_1354_, 2);
v_auxDeclNGen_1359_ = lean_ctor_get(v___x_1354_, 3);
v_cache_1360_ = lean_ctor_get(v___x_1354_, 5);
v_recordedDeps_1361_ = lean_ctor_get(v___x_1354_, 6);
v_messages_1362_ = lean_ctor_get(v___x_1354_, 7);
v_infoState_1363_ = lean_ctor_get(v___x_1354_, 8);
v_snapshotTasks_1364_ = lean_ctor_get(v___x_1354_, 9);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1366_ = v___x_1354_;
v_isShared_1367_ = v_isSharedCheck_1394_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_snapshotTasks_1364_);
lean_inc(v_infoState_1363_);
lean_inc(v_messages_1362_);
lean_inc(v_recordedDeps_1361_);
lean_inc(v_cache_1360_);
lean_inc(v_traceState_1355_);
lean_inc(v_auxDeclNGen_1359_);
lean_inc(v_ngen_1358_);
lean_inc(v_nextMacroScope_1357_);
lean_inc(v_env_1356_);
lean_dec(v___x_1354_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1394_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
uint64_t v_tid_1368_; lean_object* v_traces_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1393_; 
v_tid_1368_ = lean_ctor_get_uint64(v_traceState_1355_, sizeof(void*)*1);
v_traces_1369_ = lean_ctor_get(v_traceState_1355_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v_traceState_1355_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1371_ = v_traceState_1355_;
v_isShared_1372_ = v_isSharedCheck_1393_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_traces_1369_);
lean_dec(v_traceState_1355_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1393_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; double v___x_1375_; uint8_t v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1384_; 
v___x_1373_ = lean_box(0);
v___x_1374_ = lean_box(0);
v___x_1375_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___closed__0);
v___x_1376_ = 0;
v___x_1377_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___closed__1));
v___x_1378_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1378_, 0, v_cls_1341_);
lean_ctor_set(v___x_1378_, 1, v___x_1374_);
lean_ctor_set(v___x_1378_, 2, v___x_1377_);
lean_ctor_set_float(v___x_1378_, sizeof(void*)*3, v___x_1375_);
lean_ctor_set_float(v___x_1378_, sizeof(void*)*3 + 8, v___x_1375_);
lean_ctor_set_uint8(v___x_1378_, sizeof(void*)*3 + 16, v___x_1376_);
v___x_1379_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___closed__2));
v___x_1380_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1378_);
lean_ctor_set(v___x_1380_, 1, v_a_1350_);
lean_ctor_set(v___x_1380_, 2, v___x_1379_);
lean_inc(v_ref_1348_);
v___x_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1381_, 0, v_ref_1348_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
v___x_1382_ = l_Lean_PersistentArray_push___redArg(v_traces_1369_, v___x_1381_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v___x_1382_);
v___x_1384_ = v___x_1371_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1382_);
lean_ctor_set_uint64(v_reuseFailAlloc_1392_, sizeof(void*)*1, v_tid_1368_);
v___x_1384_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
lean_object* v___x_1386_; 
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 4, v___x_1384_);
v___x_1386_ = v___x_1366_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_env_1356_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v_nextMacroScope_1357_);
lean_ctor_set(v_reuseFailAlloc_1391_, 2, v_ngen_1358_);
lean_ctor_set(v_reuseFailAlloc_1391_, 3, v_auxDeclNGen_1359_);
lean_ctor_set(v_reuseFailAlloc_1391_, 4, v___x_1384_);
lean_ctor_set(v_reuseFailAlloc_1391_, 5, v_cache_1360_);
lean_ctor_set(v_reuseFailAlloc_1391_, 6, v_recordedDeps_1361_);
lean_ctor_set(v_reuseFailAlloc_1391_, 7, v_messages_1362_);
lean_ctor_set(v_reuseFailAlloc_1391_, 8, v_infoState_1363_);
lean_ctor_set(v_reuseFailAlloc_1391_, 9, v_snapshotTasks_1364_);
v___x_1386_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1387_ = lean_st_ref_put(v___y_1346_, v___x_1386_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 0, v___x_1373_);
v___x_1389_ = v___x_1352_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1373_);
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
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1341_ = stack[0].m_obj;
lean_object* v_msg_1342_ = stack[1].m_obj;
lean_object* v___y_1343_ = stack[2].m_obj;
lean_object* v___y_1344_ = stack[3].m_obj;
lean_object* v___y_1345_ = stack[4].m_obj;
lean_object* v___y_1346_ = stack[5].m_obj;
lean_object* v_res_1396_;
v_res_1396_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg(v_cls_1341_, v_msg_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
stack->m_obj
 = v_res_1396_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___boxed(lean_object* v_cls_1397_, lean_object* v_msg_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg(v_cls_1397_, v_msg_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
return v_res_1404_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__0(void){
_start:
{
lean_object* v___x_1405_; 
v___x_1405_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1405_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__1(void){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1406_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__0);
v___x_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1406_);
return v___x_1407_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__2(void){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__1);
v___x_1409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1408_);
lean_ctor_set(v___x_1409_, 1, v___x_1408_);
return v___x_1409_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__3(void){
_start:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1410_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__1);
v___x_1411_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
lean_ctor_set(v___x_1411_, 1, v___x_1410_);
lean_ctor_set(v___x_1411_, 2, v___x_1410_);
lean_ctor_set(v___x_1411_, 3, v___x_1410_);
lean_ctor_set(v___x_1411_, 4, v___x_1410_);
lean_ctor_set(v___x_1411_, 5, v___x_1410_);
return v___x_1411_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__4(void){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1412_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__8(void){
_start:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1417_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__7));
v___x_1418_ = l_Lean_stringToMessageData(v___x_1417_);
return v___x_1418_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__10(void){
_start:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1420_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__9));
v___x_1421_ = l_Lean_stringToMessageData(v___x_1420_);
return v___x_1421_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__11(void){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1422_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___closed__1));
v___x_1423_ = l_Lean_stringToMessageData(v___x_1422_);
return v___x_1423_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__14(void){
_start:
{
lean_object* v_cls_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v_cls_1427_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__6));
v___x_1428_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__13));
v___x_1429_ = l_Lean_Name_append(v___x_1428_, v_cls_1427_);
return v___x_1429_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__16(void){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1431_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__15));
v___x_1432_ = l_Lean_stringToMessageData(v___x_1431_);
return v___x_1432_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__18(void){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__17));
v___x_1435_ = l_Lean_stringToMessageData(v___x_1434_);
return v___x_1435_;
}
}
lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6(lean_object* v_mod_1440_, uint8_t v_isMeta_1441_, lean_object* v_hint_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v_env_1484_; uint8_t v_isExporting_1485_; lean_object* v_entry_1486_; lean_object* v___x_1487_; lean_object* v_env_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; uint8_t v___x_1493_; 
v___x_1482_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__4);
v___x_1483_ = lean_st_ref_get(v___y_1448_);
v_env_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc_ref(v_env_1484_);
lean_dec(v___x_1483_);
v_isExporting_1485_ = lean_ctor_get_uint8(v_env_1484_, sizeof(void*)*13);
lean_dec_ref(v_env_1484_);
lean_inc(v_mod_1440_);
v_entry_1486_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1486_, 0, v_mod_1440_);
lean_ctor_set_uint8(v_entry_1486_, sizeof(void*)*1, v_isExporting_1485_);
lean_ctor_set_uint8(v_entry_1486_, sizeof(void*)*1 + 1, v_isMeta_1441_);
v___x_1487_ = lean_st_ref_get(v___y_1448_);
v_env_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc_ref(v_env_1488_);
lean_dec(v___x_1487_);
v___x_1489_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1490_ = lean_box(1);
v___x_1491_ = lean_box(0);
v___x_1492_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1482_, v___x_1489_, v_env_1488_, v___x_1490_, v___x_1491_);
v___x_1493_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9___redArg(v___x_1492_, v_entry_1486_);
lean_dec(v___x_1492_);
if (v___x_1493_ == 0)
{
lean_object* v_toCold_1494_; lean_object* v_options_1495_; lean_object* v_inheritedTraceOptions_1496_; uint8_t v_hasTrace_1497_; lean_object* v___f_1498_; uint8_t v___x_1499_; lean_object* v___y_1501_; lean_object* v___y_1502_; 
v_toCold_1494_ = lean_ctor_get(v___y_1447_, 0);
v_options_1495_ = lean_ctor_get(v_toCold_1494_, 2);
v_inheritedTraceOptions_1496_ = lean_ctor_get(v_toCold_1494_, 11);
v_hasTrace_1497_ = lean_ctor_get_uint8(v_options_1495_, sizeof(void*)*1);
v___f_1498_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___lam__0), 3, 2);
lean_closure_set(v___f_1498_, 0, v___x_1489_);
lean_closure_set(v___f_1498_, 1, v_entry_1486_);
v___x_1499_ = 1;
if (v_hasTrace_1497_ == 0)
{
lean_dec(v_hint_1442_);
lean_dec(v_mod_1440_);
v___y_1501_ = v___y_1446_;
v___y_1502_ = v___y_1448_;
goto v___jp_1500_;
}
else
{
lean_object* v_cls_1529_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___x_1549_; uint8_t v___x_1550_; 
v_cls_1529_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__6));
v___x_1549_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__14);
v___x_1550_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1496_, v_options_1495_, v___x_1549_);
if (v___x_1550_ == 0)
{
lean_dec(v_hint_1442_);
lean_dec(v_mod_1440_);
v___y_1501_ = v___y_1446_;
v___y_1502_ = v___y_1448_;
goto v___jp_1500_;
}
else
{
lean_object* v___x_1551_; lean_object* v___y_1553_; 
v___x_1551_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__16);
if (v_isExporting_1485_ == 0)
{
lean_object* v___x_1560_; 
v___x_1560_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__21));
v___y_1553_ = v___x_1560_;
goto v___jp_1552_;
}
else
{
lean_object* v___x_1561_; 
v___x_1561_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__22));
v___y_1553_ = v___x_1561_;
goto v___jp_1552_;
}
v___jp_1552_:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
lean_inc_ref(v___y_1553_);
v___x_1554_ = l_Lean_stringToMessageData(v___y_1553_);
v___x_1555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1551_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
v___x_1556_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__18);
v___x_1557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1555_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
if (v_isMeta_1441_ == 0)
{
lean_object* v___x_1558_; 
v___x_1558_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__19));
v___y_1536_ = v___x_1557_;
v___y_1537_ = v___x_1558_;
goto v___jp_1535_;
}
else
{
lean_object* v___x_1559_; 
v___x_1559_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__20));
v___y_1536_ = v___x_1557_;
v___y_1537_ = v___x_1559_;
goto v___jp_1535_;
}
}
}
v___jp_1530_:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___y_1531_);
lean_ctor_set(v___x_1533_, 1, v___y_1532_);
v___x_1534_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg(v_cls_1529_, v___x_1533_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_dec_ref_known(v___x_1534_, 1);
v___y_1501_ = v___y_1446_;
v___y_1502_ = v___y_1448_;
goto v___jp_1500_;
}
else
{
lean_dec_ref(v___f_1498_);
return v___x_1534_;
}
}
v___jp_1535_:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; 
lean_inc_ref(v___y_1537_);
v___x_1538_ = l_Lean_stringToMessageData(v___y_1537_);
v___x_1539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___y_1536_);
lean_ctor_set(v___x_1539_, 1, v___x_1538_);
v___x_1540_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__8);
v___x_1541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1539_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
v___x_1542_ = l_Lean_MessageData_ofName(v_mod_1440_);
v___x_1543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1541_);
lean_ctor_set(v___x_1543_, 1, v___x_1542_);
v___x_1544_ = l_Lean_Name_isAnonymous(v_hint_1442_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1545_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__10);
v___x_1546_ = l_Lean_MessageData_ofName(v_hint_1442_);
v___x_1547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1545_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
v___y_1531_ = v___x_1543_;
v___y_1532_ = v___x_1547_;
goto v___jp_1530_;
}
else
{
lean_object* v___x_1548_; 
lean_dec(v_hint_1442_);
v___x_1548_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__11);
v___y_1531_ = v___x_1543_;
v___y_1532_ = v___x_1548_;
goto v___jp_1530_;
}
}
}
v___jp_1500_:
{
lean_object* v___x_1503_; lean_object* v_toEnvExtension_1504_; uint8_t v_logWrites_1505_; 
v___x_1503_ = lean_st_ref_take(v___y_1502_);
v_toEnvExtension_1504_ = lean_ctor_get(v___x_1489_, 0);
v_logWrites_1505_ = lean_ctor_get_uint8(v_toEnvExtension_1504_, sizeof(void*)*6);
if (v_logWrites_1505_ == 0)
{
lean_object* v_env_1506_; lean_object* v_nextMacroScope_1507_; lean_object* v_ngen_1508_; lean_object* v_auxDeclNGen_1509_; lean_object* v_traceState_1510_; lean_object* v_recordedDeps_1511_; lean_object* v_messages_1512_; lean_object* v_infoState_1513_; lean_object* v_snapshotTasks_1514_; lean_object* v_asyncMode_1515_; lean_object* v___x_1516_; 
v_env_1506_ = lean_ctor_get(v___x_1503_, 0);
lean_inc_ref(v_env_1506_);
v_nextMacroScope_1507_ = lean_ctor_get(v___x_1503_, 1);
lean_inc(v_nextMacroScope_1507_);
v_ngen_1508_ = lean_ctor_get(v___x_1503_, 2);
lean_inc_ref(v_ngen_1508_);
v_auxDeclNGen_1509_ = lean_ctor_get(v___x_1503_, 3);
lean_inc_ref(v_auxDeclNGen_1509_);
v_traceState_1510_ = lean_ctor_get(v___x_1503_, 4);
lean_inc_ref(v_traceState_1510_);
v_recordedDeps_1511_ = lean_ctor_get(v___x_1503_, 6);
lean_inc_ref(v_recordedDeps_1511_);
v_messages_1512_ = lean_ctor_get(v___x_1503_, 7);
lean_inc_ref(v_messages_1512_);
v_infoState_1513_ = lean_ctor_get(v___x_1503_, 8);
lean_inc_ref(v_infoState_1513_);
v_snapshotTasks_1514_ = lean_ctor_get(v___x_1503_, 9);
lean_inc_ref(v_snapshotTasks_1514_);
lean_dec(v___x_1503_);
v_asyncMode_1515_ = lean_ctor_get(v_toEnvExtension_1504_, 2);
lean_inc_ref(v_toEnvExtension_1504_);
v___x_1516_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1504_, v_env_1506_, v___f_1498_, v_asyncMode_1515_, v___x_1491_, v___x_1499_);
v___y_1451_ = v_auxDeclNGen_1509_;
v___y_1452_ = v_snapshotTasks_1514_;
v___y_1453_ = v_messages_1512_;
v___y_1454_ = v___y_1501_;
v___y_1455_ = v_recordedDeps_1511_;
v___y_1456_ = v_ngen_1508_;
v___y_1457_ = v_infoState_1513_;
v___y_1458_ = v_nextMacroScope_1507_;
v___y_1459_ = v_traceState_1510_;
v___y_1460_ = v___y_1502_;
v___y_1461_ = v___x_1516_;
goto v___jp_1450_;
}
else
{
lean_object* v_env_1517_; lean_object* v_nextMacroScope_1518_; lean_object* v_ngen_1519_; lean_object* v_auxDeclNGen_1520_; lean_object* v_traceState_1521_; lean_object* v_recordedDeps_1522_; lean_object* v_messages_1523_; lean_object* v_infoState_1524_; lean_object* v_snapshotTasks_1525_; lean_object* v_asyncMode_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v_env_1517_ = lean_ctor_get(v___x_1503_, 0);
lean_inc_ref(v_env_1517_);
v_nextMacroScope_1518_ = lean_ctor_get(v___x_1503_, 1);
lean_inc(v_nextMacroScope_1518_);
v_ngen_1519_ = lean_ctor_get(v___x_1503_, 2);
lean_inc_ref(v_ngen_1519_);
v_auxDeclNGen_1520_ = lean_ctor_get(v___x_1503_, 3);
lean_inc_ref(v_auxDeclNGen_1520_);
v_traceState_1521_ = lean_ctor_get(v___x_1503_, 4);
lean_inc_ref(v_traceState_1521_);
v_recordedDeps_1522_ = lean_ctor_get(v___x_1503_, 6);
lean_inc_ref(v_recordedDeps_1522_);
v_messages_1523_ = lean_ctor_get(v___x_1503_, 7);
lean_inc_ref(v_messages_1523_);
v_infoState_1524_ = lean_ctor_get(v___x_1503_, 8);
lean_inc_ref(v_infoState_1524_);
v_snapshotTasks_1525_ = lean_ctor_get(v___x_1503_, 9);
lean_inc_ref(v_snapshotTasks_1525_);
lean_dec(v___x_1503_);
v_asyncMode_1526_ = lean_ctor_get(v_toEnvExtension_1504_, 2);
lean_inc_ref_n(v_toEnvExtension_1504_, 2);
v___x_1527_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1504_, v_env_1517_);
lean_dec_ref(v_env_1517_);
v___x_1528_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1504_, v___x_1527_, v___f_1498_, v_asyncMode_1526_, v___x_1491_, v___x_1499_);
v___y_1451_ = v_auxDeclNGen_1520_;
v___y_1452_ = v_snapshotTasks_1525_;
v___y_1453_ = v_messages_1523_;
v___y_1454_ = v___y_1501_;
v___y_1455_ = v_recordedDeps_1522_;
v___y_1456_ = v_ngen_1519_;
v___y_1457_ = v_infoState_1524_;
v___y_1458_ = v_nextMacroScope_1518_;
v___y_1459_ = v_traceState_1521_;
v___y_1460_ = v___y_1502_;
v___y_1461_ = v___x_1528_;
goto v___jp_1450_;
}
}
}
else
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
lean_dec_ref_known(v_entry_1486_, 1);
lean_dec(v_hint_1442_);
lean_dec(v_mod_1440_);
v___x_1562_ = lean_box(0);
v___x_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
return v___x_1563_;
}
v___jp_1450_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v_mctx_1466_; lean_object* v_zetaDeltaFVarIds_1467_; lean_object* v_postponed_1468_; lean_object* v_diag_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1480_; 
v___x_1462_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__2);
v___x_1463_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1463_, 0, v___y_1461_);
lean_ctor_set(v___x_1463_, 1, v___y_1458_);
lean_ctor_set(v___x_1463_, 2, v___y_1456_);
lean_ctor_set(v___x_1463_, 3, v___y_1451_);
lean_ctor_set(v___x_1463_, 4, v___y_1459_);
lean_ctor_set(v___x_1463_, 5, v___x_1462_);
lean_ctor_set(v___x_1463_, 6, v___y_1455_);
lean_ctor_set(v___x_1463_, 7, v___y_1453_);
lean_ctor_set(v___x_1463_, 8, v___y_1457_);
lean_ctor_set(v___x_1463_, 9, v___y_1452_);
v___x_1464_ = lean_st_ref_put(v___y_1460_, v___x_1463_);
v___x_1465_ = lean_st_ref_take(v___y_1454_);
v_mctx_1466_ = lean_ctor_get(v___x_1465_, 0);
v_zetaDeltaFVarIds_1467_ = lean_ctor_get(v___x_1465_, 2);
v_postponed_1468_ = lean_ctor_get(v___x_1465_, 3);
v_diag_1469_ = lean_ctor_get(v___x_1465_, 4);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1480_ == 0)
{
lean_object* v_unused_1481_; 
v_unused_1481_ = lean_ctor_get(v___x_1465_, 1);
lean_dec(v_unused_1481_);
v___x_1471_ = v___x_1465_;
v_isShared_1472_ = v_isSharedCheck_1480_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_diag_1469_);
lean_inc(v_postponed_1468_);
lean_inc(v_zetaDeltaFVarIds_1467_);
lean_inc(v_mctx_1466_);
lean_dec(v___x_1465_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1480_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1476_; 
v___x_1473_ = lean_box(0);
v___x_1474_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__3);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 1, v___x_1474_);
v___x_1476_ = v___x_1471_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_mctx_1466_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1479_, 2, v_zetaDeltaFVarIds_1467_);
lean_ctor_set(v_reuseFailAlloc_1479_, 3, v_postponed_1468_);
lean_ctor_set(v_reuseFailAlloc_1479_, 4, v_diag_1469_);
v___x_1476_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = lean_st_ref_put(v___y_1454_, v___x_1476_);
v___x_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1473_);
return v___x_1478_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_mod_1440_ = stack[0].m_obj;
uint8_t v_isMeta_1441_ = stack[1].m_num;
lean_object* v_hint_1442_ = stack[2].m_obj;
lean_object* v___y_1443_ = stack[3].m_obj;
lean_object* v___y_1444_ = stack[4].m_obj;
lean_object* v___y_1445_ = stack[5].m_obj;
lean_object* v___y_1446_ = stack[6].m_obj;
lean_object* v___y_1447_ = stack[7].m_obj;
lean_object* v___y_1448_ = stack[8].m_obj;
lean_object* v_res_1564_;
v_res_1564_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6(v_mod_1440_, v_isMeta_1441_, v_hint_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
stack->m_obj
 = v_res_1564_;
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___boxed(lean_object* v_mod_1565_, lean_object* v_isMeta_1566_, lean_object* v_hint_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
uint8_t v_isMeta_boxed_1575_; lean_object* v_res_1576_; 
v_isMeta_boxed_1575_ = lean_unbox(v_isMeta_1566_);
v_res_1576_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6(v_mod_1565_, v_isMeta_boxed_1575_, v_hint_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
return v_res_1576_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__7(lean_object* v___x_1577_, lean_object* v_declName_1578_, lean_object* v_as_1579_, size_t v_sz_1580_, size_t v_i_1581_, lean_object* v_b_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
uint8_t v___x_1590_; 
v___x_1590_ = lean_usize_dec_lt(v_i_1581_, v_sz_1580_);
if (v___x_1590_ == 0)
{
lean_object* v___x_1591_; 
lean_dec(v_declName_1578_);
v___x_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1591_, 0, v_b_1582_);
return v___x_1591_;
}
else
{
lean_object* v___x_1592_; lean_object* v_modules_1593_; lean_object* v___x_1594_; lean_object* v_a_1595_; lean_object* v___x_1596_; lean_object* v_toImport_1597_; lean_object* v_module_1598_; lean_object* v___x_1599_; uint8_t v___x_1600_; lean_object* v___x_1601_; 
v___x_1592_ = l_Lean_Environment_header(v___x_1577_);
v_modules_1593_ = lean_ctor_get(v___x_1592_, 3);
lean_inc_ref(v_modules_1593_);
lean_dec_ref(v___x_1592_);
v___x_1594_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1595_ = lean_array_uget_borrowed(v_as_1579_, v_i_1581_);
v___x_1596_ = lean_array_get(v___x_1594_, v_modules_1593_, v_a_1595_);
lean_dec_ref(v_modules_1593_);
v_toImport_1597_ = lean_ctor_get(v___x_1596_, 0);
lean_inc_ref(v_toImport_1597_);
lean_dec(v___x_1596_);
v_module_1598_ = lean_ctor_get(v_toImport_1597_, 0);
lean_inc(v_module_1598_);
lean_dec_ref(v_toImport_1597_);
v___x_1599_ = lean_box(0);
v___x_1600_ = 0;
lean_inc(v_declName_1578_);
v___x_1601_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6(v_module_1598_, v___x_1600_, v_declName_1578_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
if (lean_obj_tag(v___x_1601_) == 0)
{
size_t v___x_1602_; size_t v___x_1603_; 
lean_dec_ref_known(v___x_1601_, 1);
v___x_1602_ = ((size_t)1ULL);
v___x_1603_ = lean_usize_add(v_i_1581_, v___x_1602_);
v_i_1581_ = v___x_1603_;
v_b_1582_ = v___x_1599_;
goto _start;
}
else
{
lean_dec(v_declName_1578_);
return v___x_1601_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1577_ = stack[0].m_obj;
lean_object* v_declName_1578_ = stack[1].m_obj;
lean_object* v_as_1579_ = stack[2].m_obj;
size_t v_sz_1580_ = stack[3].m_num;
size_t v_i_1581_ = stack[4].m_num;
lean_object* v_b_1582_ = stack[5].m_obj;
lean_object* v___y_1583_ = stack[6].m_obj;
lean_object* v___y_1584_ = stack[7].m_obj;
lean_object* v___y_1585_ = stack[8].m_obj;
lean_object* v___y_1586_ = stack[9].m_obj;
lean_object* v___y_1587_ = stack[10].m_obj;
lean_object* v___y_1588_ = stack[11].m_obj;
lean_object* v_res_1605_;
v_res_1605_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__7(v___x_1577_, v_declName_1578_, v_as_1579_, v_sz_1580_, v_i_1581_, v_b_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
stack->m_obj
 = v_res_1605_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__7___boxed(lean_object* v___x_1606_, lean_object* v_declName_1607_, lean_object* v_as_1608_, lean_object* v_sz_1609_, lean_object* v_i_1610_, lean_object* v_b_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
size_t v_sz_boxed_1619_; size_t v_i_boxed_1620_; lean_object* v_res_1621_; 
v_sz_boxed_1619_ = lean_unbox_usize(v_sz_1609_);
lean_dec(v_sz_1609_);
v_i_boxed_1620_ = lean_unbox_usize(v_i_1610_);
lean_dec(v_i_1610_);
v_res_1621_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__7(v___x_1606_, v_declName_1607_, v_as_1608_, v_sz_boxed_1619_, v_i_boxed_1620_, v_b_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec_ref(v_as_1608_);
lean_dec_ref(v___x_1606_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12___redArg(lean_object* v_a_1622_, lean_object* v_x_1623_){
_start:
{
if (lean_obj_tag(v_x_1623_) == 0)
{
lean_object* v___x_1624_; 
v___x_1624_ = lean_box(0);
return v___x_1624_;
}
else
{
lean_object* v_key_1625_; lean_object* v_value_1626_; lean_object* v_tail_1627_; uint8_t v___x_1628_; 
v_key_1625_ = lean_ctor_get(v_x_1623_, 0);
v_value_1626_ = lean_ctor_get(v_x_1623_, 1);
v_tail_1627_ = lean_ctor_get(v_x_1623_, 2);
v___x_1628_ = lean_name_eq(v_key_1625_, v_a_1622_);
if (v___x_1628_ == 0)
{
v_x_1623_ = v_tail_1627_;
goto _start;
}
else
{
lean_object* v___x_1630_; 
lean_inc(v_value_1626_);
v___x_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1630_, 0, v_value_1626_);
return v___x_1630_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12___redArg___boxed(lean_object* v_a_1631_, lean_object* v_x_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12___redArg(v_a_1631_, v_x_1632_);
lean_dec(v_x_1632_);
lean_dec(v_a_1631_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8___redArg(lean_object* v_m_1634_, lean_object* v_a_1635_){
_start:
{
lean_object* v_buckets_1636_; lean_object* v___x_1637_; uint64_t v___y_1639_; 
v_buckets_1636_ = lean_ctor_get(v_m_1634_, 1);
v___x_1637_ = lean_array_get_size(v_buckets_1636_);
if (lean_obj_tag(v_a_1635_) == 0)
{
uint64_t v___x_1653_; 
v___x_1653_ = 1723ULL;
v___y_1639_ = v___x_1653_;
goto v___jp_1638_;
}
else
{
uint64_t v_hash_1654_; 
v_hash_1654_ = lean_ctor_get_uint64(v_a_1635_, sizeof(void*)*2);
v___y_1639_ = v_hash_1654_;
goto v___jp_1638_;
}
v___jp_1638_:
{
uint64_t v___x_1640_; uint64_t v___x_1641_; uint64_t v_fold_1642_; uint64_t v___x_1643_; uint64_t v___x_1644_; uint64_t v___x_1645_; size_t v___x_1646_; size_t v___x_1647_; size_t v___x_1648_; size_t v___x_1649_; size_t v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1640_ = 32ULL;
v___x_1641_ = lean_uint64_shift_right(v___y_1639_, v___x_1640_);
v_fold_1642_ = lean_uint64_xor(v___y_1639_, v___x_1641_);
v___x_1643_ = 16ULL;
v___x_1644_ = lean_uint64_shift_right(v_fold_1642_, v___x_1643_);
v___x_1645_ = lean_uint64_xor(v_fold_1642_, v___x_1644_);
v___x_1646_ = lean_uint64_to_usize(v___x_1645_);
v___x_1647_ = lean_usize_of_nat(v___x_1637_);
v___x_1648_ = ((size_t)1ULL);
v___x_1649_ = lean_usize_sub(v___x_1647_, v___x_1648_);
v___x_1650_ = lean_usize_land(v___x_1646_, v___x_1649_);
v___x_1651_ = lean_array_uget_borrowed(v_buckets_1636_, v___x_1650_);
v___x_1652_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12___redArg(v_a_1635_, v___x_1651_);
return v___x_1652_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_m_1655_, lean_object* v_a_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8___redArg(v_m_1655_, v_a_1656_);
lean_dec(v_a_1656_);
lean_dec_ref(v_m_1655_);
return v_res_1657_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1658_;
}
}
lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5(lean_object* v_declName_1661_, uint8_t v_isMeta_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v_env_1675_; lean_object* v___y_1677_; lean_object* v___x_1690_; 
v___x_1670_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5___closed__0);
v___x_1671_ = lean_st_ref_get(v___y_1668_);
v_env_1675_ = lean_ctor_get(v___x_1671_, 0);
lean_inc_ref(v_env_1675_);
lean_dec(v___x_1671_);
v___x_1690_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1675_, v_declName_1661_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_dec_ref(v_env_1675_);
lean_dec(v_declName_1661_);
goto v___jp_1672_;
}
else
{
lean_object* v_val_1691_; lean_object* v___x_1692_; lean_object* v_modules_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; 
v_val_1691_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_val_1691_);
lean_dec_ref_known(v___x_1690_, 1);
v___x_1692_ = l_Lean_Environment_header(v_env_1675_);
v_modules_1693_ = lean_ctor_get(v___x_1692_, 3);
lean_inc_ref(v_modules_1693_);
lean_dec_ref(v___x_1692_);
v___x_1694_ = lean_array_get_size(v_modules_1693_);
v___x_1695_ = lean_nat_dec_lt(v_val_1691_, v___x_1694_);
if (v___x_1695_ == 0)
{
lean_dec_ref(v_modules_1693_);
lean_dec(v_val_1691_);
lean_dec_ref(v_env_1675_);
lean_dec(v_declName_1661_);
goto v___jp_1672_;
}
else
{
lean_object* v___x_1696_; lean_object* v___x_1697_; uint8_t v___y_1699_; 
v___x_1696_ = lean_array_fget(v_modules_1693_, v_val_1691_);
lean_dec(v_val_1691_);
lean_dec_ref(v_modules_1693_);
v___x_1697_ = lean_st_ref_get(v___y_1668_);
if (v_isMeta_1662_ == 0)
{
lean_dec(v___x_1697_);
v___y_1699_ = v_isMeta_1662_;
goto v___jp_1698_;
}
else
{
lean_object* v_env_1710_; uint8_t v___x_1711_; 
v_env_1710_ = lean_ctor_get(v___x_1697_, 0);
lean_inc_ref(v_env_1710_);
lean_dec(v___x_1697_);
lean_inc(v_declName_1661_);
v___x_1711_ = l_Lean_isMarkedMeta(v_env_1710_, v_declName_1661_);
if (v___x_1711_ == 0)
{
v___y_1699_ = v_isMeta_1662_;
goto v___jp_1698_;
}
else
{
uint8_t v___x_1712_; 
v___x_1712_ = 0;
v___y_1699_ = v___x_1712_;
goto v___jp_1698_;
}
}
v___jp_1698_:
{
lean_object* v_toImport_1700_; lean_object* v_module_1701_; lean_object* v___x_1702_; 
v_toImport_1700_ = lean_ctor_get(v___x_1696_, 0);
lean_inc_ref(v_toImport_1700_);
lean_dec(v___x_1696_);
v_module_1701_ = lean_ctor_get(v_toImport_1700_, 0);
lean_inc(v_module_1701_);
lean_dec_ref(v_toImport_1700_);
lean_inc(v_declName_1661_);
v___x_1702_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6(v_module_1701_, v___y_1699_, v_declName_1661_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
lean_dec_ref_known(v___x_1702_, 1);
v___x_1703_ = l_Lean_indirectModUseExt;
v___x_1704_ = lean_box(1);
v___x_1705_ = lean_box(0);
lean_inc_ref(v_env_1675_);
v___x_1706_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1670_, v___x_1703_, v_env_1675_, v___x_1704_, v___x_1705_);
v___x_1707_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8___redArg(v___x_1706_, v_declName_1661_);
lean_dec(v___x_1706_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v___x_1708_; 
v___x_1708_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5___closed__1));
v___y_1677_ = v___x_1708_;
goto v___jp_1676_;
}
else
{
lean_object* v_val_1709_; 
v_val_1709_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_val_1709_);
lean_dec_ref_known(v___x_1707_, 1);
v___y_1677_ = v_val_1709_;
goto v___jp_1676_;
}
}
else
{
lean_dec_ref(v_env_1675_);
lean_dec(v_declName_1661_);
return v___x_1702_;
}
}
}
}
v___jp_1672_:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1673_ = lean_box(0);
v___x_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
return v___x_1674_;
}
v___jp_1676_:
{
lean_object* v___x_1678_; size_t v_sz_1679_; size_t v___x_1680_; lean_object* v___x_1681_; 
v___x_1678_ = lean_box(0);
v_sz_1679_ = lean_array_size(v___y_1677_);
v___x_1680_ = ((size_t)0ULL);
v___x_1681_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__7(v_env_1675_, v_declName_1661_, v___y_1677_, v_sz_1679_, v___x_1680_, v___x_1678_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
lean_dec_ref(v___y_1677_);
lean_dec_ref(v_env_1675_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1688_ == 0)
{
lean_object* v_unused_1689_; 
v_unused_1689_ = lean_ctor_get(v___x_1681_, 0);
lean_dec(v_unused_1689_);
v___x_1683_ = v___x_1681_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_dec(v___x_1681_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 0, v___x_1678_);
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1678_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
else
{
return v___x_1681_;
}
}
}
}
LEAN_EXPORT void l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1661_ = stack[0].m_obj;
uint8_t v_isMeta_1662_ = stack[1].m_num;
lean_object* v___y_1663_ = stack[2].m_obj;
lean_object* v___y_1664_ = stack[3].m_obj;
lean_object* v___y_1665_ = stack[4].m_obj;
lean_object* v___y_1666_ = stack[5].m_obj;
lean_object* v___y_1667_ = stack[6].m_obj;
lean_object* v___y_1668_ = stack[7].m_obj;
lean_object* v_res_1713_;
v_res_1713_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5(v_declName_1661_, v_isMeta_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
stack->m_obj
 = v_res_1713_;
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5___boxed(lean_object* v_declName_1714_, lean_object* v_isMeta_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
uint8_t v_isMeta_boxed_1723_; lean_object* v_res_1724_; 
v_isMeta_boxed_1723_ = lean_unbox(v_isMeta_1715_);
v_res_1724_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5(v_declName_1714_, v_isMeta_boxed_1723_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
return v_res_1724_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6___redArg(lean_object* v_as_x27_1725_, lean_object* v_b_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
if (lean_obj_tag(v_as_x27_1725_) == 0)
{
lean_object* v___x_1734_; 
v___x_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1734_, 0, v_b_1726_);
return v___x_1734_;
}
else
{
lean_object* v_head_1735_; lean_object* v_tail_1736_; lean_object* v___x_1737_; uint8_t v___x_1738_; lean_object* v___x_1739_; 
v_head_1735_ = lean_ctor_get(v_as_x27_1725_, 0);
v_tail_1736_ = lean_ctor_get(v_as_x27_1725_, 1);
v___x_1737_ = lean_box(0);
v___x_1738_ = 1;
lean_inc(v_head_1735_);
v___x_1739_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5(v_head_1735_, v___x_1738_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_dec_ref_known(v___x_1739_, 1);
v_as_x27_1725_ = v_tail_1736_;
v_b_1726_ = v___x_1737_;
goto _start;
}
else
{
return v___x_1739_;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_1725_ = stack[0].m_obj;
lean_object* v_b_1726_ = stack[1].m_obj;
lean_object* v___y_1727_ = stack[2].m_obj;
lean_object* v___y_1728_ = stack[3].m_obj;
lean_object* v___y_1729_ = stack[4].m_obj;
lean_object* v___y_1730_ = stack[5].m_obj;
lean_object* v___y_1731_ = stack[6].m_obj;
lean_object* v___y_1732_ = stack[7].m_obj;
lean_object* v_res_1741_;
v_res_1741_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6___redArg(v_as_x27_1725_, v_b_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
stack->m_obj
 = v_res_1741_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6___redArg___boxed(lean_object* v_as_x27_1742_, lean_object* v_b_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6___redArg(v_as_x27_1742_, v_b_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v_as_x27_1742_);
return v_res_1751_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1757_ = l_Lean_maxRecDepthErrorMessage;
v___x_1758_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
return v___x_1758_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__4(void){
_start:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1759_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__3);
v___x_1760_ = l_Lean_MessageData_ofFormat(v___x_1759_);
return v___x_1760_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1761_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__4);
v___x_1762_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__2));
v___x_1763_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
lean_ctor_set(v___x_1763_, 1, v___x_1761_);
return v___x_1763_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg(lean_object* v_ref_1764_){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1766_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__5);
v___x_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1767_, 0, v_ref_1764_);
lean_ctor_set(v___x_1767_, 1, v___x_1766_);
v___x_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
return v___x_1768_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1764_ = stack[0].m_obj;
lean_object* v_res_1769_;
v_res_1769_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg(v_ref_1764_);
stack->m_obj
 = v_res_1769_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___boxed(lean_object* v_ref_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg(v_ref_1770_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__2(lean_object* v_currNamespace_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v___x_1776_; 
v___x_1776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1776_, 0, v_currNamespace_1773_);
lean_ctor_set(v___x_1776_, 1, v___y_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__2___boxed(lean_object* v_currNamespace_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__2(v_currNamespace_1777_, v___y_1778_, v___y_1779_);
lean_dec_ref(v___y_1778_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__0(lean_object* v_env_1781_, lean_object* v_declName_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
uint8_t v___x_1785_; lean_object* v_env_1786_; lean_object* v___x_1787_; uint8_t v___x_1788_; uint8_t v___x_1789_; 
v___x_1785_ = 0;
v_env_1786_ = l_Lean_Environment_setExporting(v_env_1781_, v___x_1785_);
lean_inc(v_declName_1782_);
v___x_1787_ = l_Lean_mkPrivateName(v_env_1786_, v_declName_1782_);
v___x_1788_ = 1;
lean_inc_ref(v_env_1786_);
v___x_1789_ = l_Lean_Environment_contains(v_env_1786_, v___x_1787_, v___x_1788_);
if (v___x_1789_ == 0)
{
lean_object* v___x_1790_; uint8_t v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1790_ = l_Lean_privateToUserName(v_declName_1782_);
v___x_1791_ = l_Lean_Environment_contains(v_env_1786_, v___x_1790_, v___x_1788_);
v___x_1792_ = lean_box(v___x_1791_);
v___x_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1792_);
lean_ctor_set(v___x_1793_, 1, v___y_1784_);
return v___x_1793_;
}
else
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
lean_dec_ref(v_env_1786_);
lean_dec(v_declName_1782_);
v___x_1794_ = lean_box(v___x_1789_);
v___x_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1794_);
lean_ctor_set(v___x_1795_, 1, v___y_1784_);
return v___x_1795_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__0___boxed(lean_object* v_env_1796_, lean_object* v_declName_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__0(v_env_1796_, v_declName_1797_, v___y_1798_, v___y_1799_);
lean_dec_ref(v___y_1798_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__4(lean_object* v_env_1801_, lean_object* v_currNamespace_1802_, lean_object* v_openDecls_1803_, lean_object* v_n_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1807_ = l_Lean_ResolveName_resolveNamespace(v_env_1801_, v_currNamespace_1802_, v_openDecls_1803_, v_n_1804_);
v___x_1808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
lean_ctor_set(v___x_1808_, 1, v___y_1806_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__4___boxed(lean_object* v_env_1809_, lean_object* v_currNamespace_1810_, lean_object* v_openDecls_1811_, lean_object* v_n_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__4(v_env_1809_, v_currNamespace_1810_, v_openDecls_1811_, v_n_1812_, v___y_1813_, v___y_1814_);
lean_dec_ref(v___y_1813_);
return v_res_1815_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1816_ = lean_box(0);
v___x_1817_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
lean_ctor_set(v___x_1818_, 1, v___x_1816_);
return v___x_1818_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg(){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg___closed__0);
v___x_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1822_;
v_res_1822_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg();
stack->m_obj
 = v_res_1822_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg___boxed(lean_object* v___y_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg();
return v_res_1824_;
}
}
lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__7(lean_object* v_as_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
if (lean_obj_tag(v_as_1825_) == 0)
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = lean_box(0);
v___x_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
return v___x_1834_;
}
else
{
lean_object* v_toCold_1835_; lean_object* v_options_1836_; uint8_t v_hasTrace_1837_; 
v_toCold_1835_ = lean_ctor_get(v___y_1830_, 0);
v_options_1836_ = lean_ctor_get(v_toCold_1835_, 2);
v_hasTrace_1837_ = lean_ctor_get_uint8(v_options_1836_, sizeof(void*)*1);
if (v_hasTrace_1837_ == 0)
{
lean_object* v_tail_1838_; 
v_tail_1838_ = lean_ctor_get(v_as_1825_, 1);
lean_inc(v_tail_1838_);
lean_dec_ref_known(v_as_1825_, 2);
v_as_1825_ = v_tail_1838_;
goto _start;
}
else
{
lean_object* v_head_1840_; lean_object* v_tail_1841_; lean_object* v_fst_1842_; lean_object* v_snd_1843_; lean_object* v_inheritedTraceOptions_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; uint8_t v___x_1847_; 
v_head_1840_ = lean_ctor_get(v_as_1825_, 0);
lean_inc(v_head_1840_);
v_tail_1841_ = lean_ctor_get(v_as_1825_, 1);
lean_inc(v_tail_1841_);
lean_dec_ref_known(v_as_1825_, 2);
v_fst_1842_ = lean_ctor_get(v_head_1840_, 0);
lean_inc_n(v_fst_1842_, 2);
v_snd_1843_ = lean_ctor_get(v_head_1840_, 1);
lean_inc(v_snd_1843_);
lean_dec(v_head_1840_);
v_inheritedTraceOptions_1844_ = lean_ctor_get(v_toCold_1835_, 11);
v___x_1845_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__13));
v___x_1846_ = l_Lean_Name_append(v___x_1845_, v_fst_1842_);
v___x_1847_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1844_, v_options_1836_, v___x_1846_);
lean_dec(v___x_1846_);
if (v___x_1847_ == 0)
{
lean_dec(v_snd_1843_);
lean_dec(v_fst_1842_);
v_as_1825_ = v_tail_1841_;
goto _start;
}
else
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1849_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1849_, 0, v_snd_1843_);
v___x_1850_ = l_Lean_MessageData_ofFormat(v___x_1849_);
v___x_1851_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg(v_fst_1842_, v___x_1850_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_dec_ref_known(v___x_1851_, 1);
v_as_1825_ = v_tail_1841_;
goto _start;
}
else
{
lean_dec(v_tail_1841_);
return v___x_1851_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1825_ = stack[0].m_obj;
lean_object* v___y_1826_ = stack[1].m_obj;
lean_object* v___y_1827_ = stack[2].m_obj;
lean_object* v___y_1828_ = stack[3].m_obj;
lean_object* v___y_1829_ = stack[4].m_obj;
lean_object* v___y_1830_ = stack[5].m_obj;
lean_object* v___y_1831_ = stack[6].m_obj;
lean_object* v_res_1853_;
v_res_1853_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__7(v_as_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
stack->m_obj
 = v_res_1853_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__7___boxed(lean_object* v_as_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__7(v_as_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__3(lean_object* v_env_1863_, lean_object* v___x_1864_, lean_object* v_currNamespace_1865_, lean_object* v_openDecls_1866_, lean_object* v_n_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = l_Lean_ResolveName_resolveGlobalName(v_env_1863_, v___x_1864_, v_currNamespace_1865_, v_openDecls_1866_, v_n_1867_);
v___x_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1870_);
lean_ctor_set(v___x_1871_, 1, v___y_1869_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__3___boxed(lean_object* v_env_1872_, lean_object* v___x_1873_, lean_object* v_currNamespace_1874_, lean_object* v_openDecls_1875_, lean_object* v_n_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__3(v_env_1872_, v___x_1873_, v_currNamespace_1874_, v_openDecls_1875_, v_n_1876_, v___y_1877_, v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec_ref(v___x_1873_);
return v_res_1879_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8___redArg(lean_object* v_ref_1880_, lean_object* v_msg_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v_toCold_1889_; lean_object* v_currRecDepth_1890_; lean_object* v_ref_1891_; uint16_t v_optionFlags_1892_; uint8_t v_suppressElabErrors_1893_; uint8_t v_isRecordingDeps_1894_; lean_object* v_ref_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v_toCold_1889_ = lean_ctor_get(v___y_1886_, 0);
v_currRecDepth_1890_ = lean_ctor_get(v___y_1886_, 1);
v_ref_1891_ = lean_ctor_get(v___y_1886_, 2);
v_optionFlags_1892_ = lean_ctor_get_uint16(v___y_1886_, sizeof(void*)*3);
v_suppressElabErrors_1893_ = lean_ctor_get_uint8(v___y_1886_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1894_ = lean_ctor_get_uint8(v___y_1886_, sizeof(void*)*3 + 3);
v_ref_1895_ = l_Lean_replaceRef(v_ref_1880_, v_ref_1891_);
lean_inc(v_currRecDepth_1890_);
lean_inc_ref(v_toCold_1889_);
v___x_1896_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1896_, 0, v_toCold_1889_);
lean_ctor_set(v___x_1896_, 1, v_currRecDepth_1890_);
lean_ctor_set(v___x_1896_, 2, v_ref_1895_);
lean_ctor_set_uint16(v___x_1896_, sizeof(void*)*3, v_optionFlags_1892_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*3 + 2, v_suppressElabErrors_1893_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*3 + 3, v_isRecordingDeps_1894_);
v___x_1897_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg(v_msg_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___x_1896_, v___y_1887_);
lean_dec_ref_known(v___x_1896_, 3);
return v___x_1897_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1880_ = stack[0].m_obj;
lean_object* v_msg_1881_ = stack[1].m_obj;
lean_object* v___y_1882_ = stack[2].m_obj;
lean_object* v___y_1883_ = stack[3].m_obj;
lean_object* v___y_1884_ = stack[4].m_obj;
lean_object* v___y_1885_ = stack[5].m_obj;
lean_object* v___y_1886_ = stack[6].m_obj;
lean_object* v___y_1887_ = stack[7].m_obj;
lean_object* v_res_1898_;
v_res_1898_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8___redArg(v_ref_1880_, v_msg_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_);
stack->m_obj
 = v_res_1898_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8___redArg___boxed(lean_object* v_ref_1899_, lean_object* v_msg_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8___redArg(v_ref_1899_, v_msg_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v_ref_1899_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___redArg(lean_object* v_x_1909_, lean_object* v___y_1910_){
_start:
{
if (lean_obj_tag(v_x_1909_) == 0)
{
lean_object* v_a_1911_; lean_object* v___x_1912_; 
v_a_1911_ = lean_ctor_get(v_x_1909_, 0);
lean_inc(v_a_1911_);
v___x_1912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1912_, 0, v_a_1911_);
lean_ctor_set(v___x_1912_, 1, v___y_1910_);
return v___x_1912_;
}
else
{
lean_object* v_a_1913_; lean_object* v___x_1914_; 
v_a_1913_ = lean_ctor_get(v_x_1909_, 0);
lean_inc(v_a_1913_);
v___x_1914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1914_, 0, v_a_1913_);
lean_ctor_set(v___x_1914_, 1, v___y_1910_);
return v___x_1914_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___redArg___boxed(lean_object* v_x_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___redArg(v_x_1915_, v___y_1916_);
lean_dec_ref(v_x_1915_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__1(lean_object* v_env_1918_, lean_object* v_stx_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v___x_1922_; 
v___x_1922_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1918_, v_stx_1919_, v___y_1920_, v___y_1921_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_a_1923_; 
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
lean_inc(v_a_1923_);
if (lean_obj_tag(v_a_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1932_; 
v_a_1924_ = lean_ctor_get(v___x_1922_, 1);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1932_ == 0)
{
lean_object* v_unused_1933_; 
v_unused_1933_ = lean_ctor_get(v___x_1922_, 0);
lean_dec(v_unused_1933_);
v___x_1926_ = v___x_1922_;
v_isShared_1927_ = v_isSharedCheck_1932_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_dec(v___x_1922_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1932_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1928_; lean_object* v___x_1930_; 
v___x_1928_ = lean_box(0);
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 0, v___x_1928_);
v___x_1930_ = v___x_1926_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1928_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_a_1924_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
else
{
lean_object* v_val_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1962_; 
v_val_1934_ = lean_ctor_get(v_a_1923_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v_a_1923_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1936_ = v_a_1923_;
v_isShared_1937_ = v_isSharedCheck_1962_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_val_1934_);
lean_dec(v_a_1923_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1962_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v_snd_1938_; 
v_snd_1938_ = lean_ctor_get(v_val_1934_, 1);
lean_inc(v_snd_1938_);
lean_dec(v_val_1934_);
if (lean_obj_tag(v_snd_1938_) == 0)
{
lean_object* v_a_1939_; lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1948_; 
lean_del_object(v___x_1936_);
v_a_1939_ = lean_ctor_get(v___x_1922_, 1);
lean_inc(v_a_1939_);
lean_dec_ref_known(v___x_1922_, 2);
v_a_1940_ = lean_ctor_get(v_snd_1938_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v_snd_1938_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1942_ = v_snd_1938_;
v_isShared_1943_ = v_isSharedCheck_1948_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v_snd_1938_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1948_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
lean_object* v___x_1946_; 
v___x_1946_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___redArg(v___x_1945_, v_a_1939_);
lean_dec_ref(v___x_1945_);
return v___x_1946_;
}
}
}
else
{
lean_object* v_a_1949_; lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1961_; 
v_a_1949_ = lean_ctor_get(v___x_1922_, 1);
lean_inc(v_a_1949_);
lean_dec_ref_known(v___x_1922_, 2);
v_a_1950_ = lean_ctor_get(v_snd_1938_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v_snd_1938_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1952_ = v_snd_1938_;
v_isShared_1953_ = v_isSharedCheck_1961_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v_snd_1938_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1961_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 0, v_a_1950_);
v___x_1955_ = v___x_1936_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
lean_object* v___x_1957_; 
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 0, v___x_1955_);
v___x_1957_ = v___x_1952_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
lean_object* v___x_1958_; 
v___x_1958_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___redArg(v___x_1957_, v_a_1949_);
lean_dec_ref(v___x_1957_);
return v___x_1958_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1963_; lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
v_a_1963_ = lean_ctor_get(v___x_1922_, 0);
v_a_1964_ = lean_ctor_get(v___x_1922_, 1);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___x_1922_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_inc(v_a_1963_);
lean_dec(v___x_1922_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1963_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v_a_1964_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__1___boxed(lean_object* v_env_1972_, lean_object* v_stx_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__1(v_env_1972_, v_stx_1973_, v___y_1974_, v___y_1975_);
lean_dec_ref(v___y_1974_);
return v_res_1976_;
}
}
lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg(lean_object* v_x_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
lean_object* v___x_1986_; lean_object* v_toCold_1987_; lean_object* v_env_1988_; lean_object* v_currRecDepth_1989_; lean_object* v_ref_1990_; lean_object* v_maxRecDepth_1991_; lean_object* v_currNamespace_1992_; lean_object* v_openDecls_1993_; lean_object* v_quotContext_1994_; lean_object* v_currMacroScope_1995_; lean_object* v___f_1996_; lean_object* v___f_1997_; lean_object* v___x_1998_; lean_object* v___f_1999_; lean_object* v___f_2000_; lean_object* v___f_2001_; lean_object* v_methods_2002_; lean_object* v___x_2003_; lean_object* v_nextMacroScope_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_1986_ = lean_st_ref_get(v___y_1984_);
v_toCold_1987_ = lean_ctor_get(v___y_1983_, 0);
v_env_1988_ = lean_ctor_get(v___x_1986_, 0);
lean_inc_ref_n(v_env_1988_, 4);
lean_dec(v___x_1986_);
v_currRecDepth_1989_ = lean_ctor_get(v___y_1983_, 1);
v_ref_1990_ = lean_ctor_get(v___y_1983_, 2);
v_maxRecDepth_1991_ = lean_ctor_get(v_toCold_1987_, 3);
v_currNamespace_1992_ = lean_ctor_get(v_toCold_1987_, 4);
v_openDecls_1993_ = lean_ctor_get(v_toCold_1987_, 5);
v_quotContext_1994_ = lean_ctor_get(v_toCold_1987_, 8);
v_currMacroScope_1995_ = lean_ctor_get(v_toCold_1987_, 9);
v___f_1996_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1996_, 0, v_env_1988_);
v___f_1997_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1997_, 0, v_env_1988_);
v___x_1998_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1983_);
lean_inc_n(v_currNamespace_1992_, 3);
v___f_1999_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1999_, 0, v_currNamespace_1992_);
lean_inc_n(v_openDecls_1993_, 2);
v___f_2000_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__3___boxed), 7, 4);
lean_closure_set(v___f_2000_, 0, v_env_1988_);
lean_closure_set(v___f_2000_, 1, v___x_1998_);
lean_closure_set(v___f_2000_, 2, v_currNamespace_1992_);
lean_closure_set(v___f_2000_, 3, v_openDecls_1993_);
v___f_2001_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_2001_, 0, v_env_1988_);
lean_closure_set(v___f_2001_, 1, v_currNamespace_1992_);
lean_closure_set(v___f_2001_, 2, v_openDecls_1993_);
v_methods_2002_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2002_, 0, v___f_1997_);
lean_ctor_set(v_methods_2002_, 1, v___f_1999_);
lean_ctor_set(v_methods_2002_, 2, v___f_1996_);
lean_ctor_set(v_methods_2002_, 3, v___f_2001_);
lean_ctor_set(v_methods_2002_, 4, v___f_2000_);
v___x_2003_ = lean_st_ref_get(v___y_1984_);
v_nextMacroScope_2004_ = lean_ctor_get(v___x_2003_, 1);
lean_inc(v_nextMacroScope_2004_);
lean_dec(v___x_2003_);
lean_inc(v_ref_1990_);
lean_inc(v_maxRecDepth_1991_);
lean_inc(v_currRecDepth_1989_);
lean_inc(v_currMacroScope_1995_);
lean_inc(v_quotContext_1994_);
v___x_2005_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2005_, 0, v_methods_2002_);
lean_ctor_set(v___x_2005_, 1, v_quotContext_1994_);
lean_ctor_set(v___x_2005_, 2, v_currMacroScope_1995_);
lean_ctor_set(v___x_2005_, 3, v_currRecDepth_1989_);
lean_ctor_set(v___x_2005_, 4, v_maxRecDepth_1991_);
lean_ctor_set(v___x_2005_, 5, v_ref_1990_);
v___x_2006_ = lean_box(0);
v___x_2007_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2007_, 0, v_nextMacroScope_2004_);
lean_ctor_set(v___x_2007_, 1, v___x_2006_);
lean_ctor_set(v___x_2007_, 2, v___x_2006_);
v___x_2008_ = lean_apply_2(v_x_1978_, v___x_2005_, v___x_2007_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v_a_2010_; lean_object* v_macroScope_2011_; lean_object* v_traceMsgs_2012_; lean_object* v_expandedMacroDecls_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 1);
lean_inc(v_a_2009_);
v_a_2010_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_a_2010_);
lean_dec_ref_known(v___x_2008_, 2);
v_macroScope_2011_ = lean_ctor_get(v_a_2009_, 0);
lean_inc(v_macroScope_2011_);
v_traceMsgs_2012_ = lean_ctor_get(v_a_2009_, 1);
lean_inc(v_traceMsgs_2012_);
v_expandedMacroDecls_2013_ = lean_ctor_get(v_a_2009_, 2);
lean_inc(v_expandedMacroDecls_2013_);
lean_dec(v_a_2009_);
v___x_2014_ = lean_box(0);
v___x_2015_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6___redArg(v_expandedMacroDecls_2013_, v___x_2014_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
lean_dec(v_expandedMacroDecls_2013_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v___x_2016_; lean_object* v_env_2017_; lean_object* v_ngen_2018_; lean_object* v_auxDeclNGen_2019_; lean_object* v_traceState_2020_; lean_object* v_cache_2021_; lean_object* v_recordedDeps_2022_; lean_object* v_messages_2023_; lean_object* v_infoState_2024_; lean_object* v_snapshotTasks_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2051_; 
lean_dec_ref_known(v___x_2015_, 1);
v___x_2016_ = lean_st_ref_take(v___y_1984_);
v_env_2017_ = lean_ctor_get(v___x_2016_, 0);
v_ngen_2018_ = lean_ctor_get(v___x_2016_, 2);
v_auxDeclNGen_2019_ = lean_ctor_get(v___x_2016_, 3);
v_traceState_2020_ = lean_ctor_get(v___x_2016_, 4);
v_cache_2021_ = lean_ctor_get(v___x_2016_, 5);
v_recordedDeps_2022_ = lean_ctor_get(v___x_2016_, 6);
v_messages_2023_ = lean_ctor_get(v___x_2016_, 7);
v_infoState_2024_ = lean_ctor_get(v___x_2016_, 8);
v_snapshotTasks_2025_ = lean_ctor_get(v___x_2016_, 9);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2051_ == 0)
{
lean_object* v_unused_2052_; 
v_unused_2052_ = lean_ctor_get(v___x_2016_, 1);
lean_dec(v_unused_2052_);
v___x_2027_ = v___x_2016_;
v_isShared_2028_ = v_isSharedCheck_2051_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_snapshotTasks_2025_);
lean_inc(v_infoState_2024_);
lean_inc(v_messages_2023_);
lean_inc(v_recordedDeps_2022_);
lean_inc(v_cache_2021_);
lean_inc(v_traceState_2020_);
lean_inc(v_auxDeclNGen_2019_);
lean_inc(v_ngen_2018_);
lean_inc(v_env_2017_);
lean_dec(v___x_2016_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2051_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 1, v_macroScope_2011_);
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_env_2017_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v_macroScope_2011_);
lean_ctor_set(v_reuseFailAlloc_2050_, 2, v_ngen_2018_);
lean_ctor_set(v_reuseFailAlloc_2050_, 3, v_auxDeclNGen_2019_);
lean_ctor_set(v_reuseFailAlloc_2050_, 4, v_traceState_2020_);
lean_ctor_set(v_reuseFailAlloc_2050_, 5, v_cache_2021_);
lean_ctor_set(v_reuseFailAlloc_2050_, 6, v_recordedDeps_2022_);
lean_ctor_set(v_reuseFailAlloc_2050_, 7, v_messages_2023_);
lean_ctor_set(v_reuseFailAlloc_2050_, 8, v_infoState_2024_);
lean_ctor_set(v_reuseFailAlloc_2050_, 9, v_snapshotTasks_2025_);
v___x_2030_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2031_ = lean_st_ref_put(v___y_1984_, v___x_2030_);
v___x_2032_ = l_List_reverse___redArg(v_traceMsgs_2012_);
v___x_2033_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__7(v___x_2032_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2040_ == 0)
{
lean_object* v_unused_2041_; 
v_unused_2041_ = lean_ctor_get(v___x_2033_, 0);
lean_dec(v_unused_2041_);
v___x_2035_ = v___x_2033_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_dec(v___x_2033_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 0, v_a_2010_);
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2010_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
else
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
lean_dec(v_a_2010_);
v_a_2042_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2033_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2033_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
}
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec(v_traceMsgs_2012_);
lean_dec(v_macroScope_2011_);
lean_dec(v_a_2010_);
v_a_2053_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2015_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2015_);
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
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
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
else
{
lean_object* v_a_2061_; 
v_a_2061_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_a_2061_);
lean_dec_ref_known(v___x_2008_, 2);
if (lean_obj_tag(v_a_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v_a_2063_; lean_object* v___x_2064_; uint8_t v___x_2065_; 
v_a_2062_ = lean_ctor_get(v_a_2061_, 0);
lean_inc(v_a_2062_);
v_a_2063_ = lean_ctor_get(v_a_2061_, 1);
lean_inc_ref(v_a_2063_);
lean_dec_ref_known(v_a_2061_, 2);
v___x_2064_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___closed__0));
v___x_2065_ = lean_string_dec_eq(v_a_2063_, v___x_2064_);
if (v___x_2065_ == 0)
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2066_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2066_, 0, v_a_2063_);
v___x_2067_ = l_Lean_MessageData_ofFormat(v___x_2066_);
v___x_2068_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8___redArg(v_a_2062_, v___x_2067_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
lean_dec(v_a_2062_);
return v___x_2068_;
}
else
{
lean_object* v___x_2069_; 
lean_dec_ref(v_a_2063_);
v___x_2069_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg(v_a_2062_);
return v___x_2069_;
}
}
else
{
lean_object* v___x_2070_; 
v___x_2070_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg();
return v___x_2070_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1978_ = stack[0].m_obj;
lean_object* v___y_1979_ = stack[1].m_obj;
lean_object* v___y_1980_ = stack[2].m_obj;
lean_object* v___y_1981_ = stack[3].m_obj;
lean_object* v___y_1982_ = stack[4].m_obj;
lean_object* v___y_1983_ = stack[5].m_obj;
lean_object* v___y_1984_ = stack[6].m_obj;
lean_object* v_res_2071_;
v_res_2071_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg(v_x_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
stack->m_obj
 = v_res_2071_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___boxed(lean_object* v_x_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg(v_x_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
return v_res_2080_;
}
}
static lean_object* _init_l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__1(void){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2082_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__0));
v___x_2083_ = l_Lean_stringToMessageData(v___x_2082_);
return v___x_2083_;
}
}
static lean_object* _init_l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__6(void){
_start:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2092_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__5));
v___x_2093_ = l_Lean_stringToMessageData(v___x_2092_);
return v___x_2093_;
}
}
lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f(lean_object* v_e_2094_, lean_object* v_dec_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_){
_start:
{
lean_object* v___x_2104_; 
v___x_2104_ = l_Lean_Elab_Do_Forward_matchApp_x3f(v_e_2094_);
if (lean_obj_tag(v___x_2104_) == 1)
{
lean_object* v_val_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2275_; 
v_val_2105_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2107_ = v___x_2104_;
v_isShared_2108_ = v_isSharedCheck_2275_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_val_2105_);
lean_dec(v___x_2104_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2275_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v_fst_2109_; lean_object* v_snd_2110_; lean_object* v___f_2111_; lean_object* v___x_2112_; 
v_fst_2109_ = lean_ctor_get(v_val_2105_, 0);
lean_inc_n(v_fst_2109_, 2);
v_snd_2110_ = lean_ctor_get(v_val_2105_, 1);
lean_inc(v_snd_2110_);
lean_dec(v_val_2105_);
lean_inc(v_a_2100_);
lean_inc_ref(v_a_2099_);
lean_inc(v_a_2098_);
lean_inc_ref(v_a_2097_);
v___f_2111_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___boxed), 8, 5);
lean_closure_set(v___f_2111_, 0, v_a_2097_);
lean_closure_set(v___f_2111_, 1, v_a_2098_);
lean_closure_set(v___f_2111_, 2, v_a_2099_);
lean_closure_set(v___f_2111_, 3, v_a_2100_);
lean_closure_set(v___f_2111_, 4, v_fst_2109_);
v___x_2112_ = l_Lean_Core_withFreshMacroScope___redArg(v___f_2111_, v_a_2101_, v_a_2102_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v_fst_2114_; lean_object* v_snd_2115_; lean_object* v___x_2116_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc(v_a_2113_);
lean_dec_ref_known(v___x_2112_, 1);
v_fst_2114_ = lean_ctor_get(v_a_2113_, 0);
lean_inc_n(v_fst_2114_, 2);
v_snd_2115_ = lean_ctor_get(v_a_2113_, 1);
lean_inc_n(v_snd_2115_, 2);
lean_dec(v_a_2113_);
v___x_2116_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder(v_fst_2109_, v_fst_2114_, v_snd_2115_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_binders_2117_; lean_object* v_body_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2258_; 
lean_dec_ref_known(v___x_2116_, 1);
v_binders_2117_ = lean_ctor_get(v_snd_2110_, 0);
v_body_2118_ = lean_ctor_get(v_snd_2110_, 1);
v_isSharedCheck_2258_ = !lean_is_exclusive(v_snd_2110_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2120_ = v_snd_2110_;
v_isShared_2121_ = v_isSharedCheck_2258_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_body_2118_);
lean_inc(v_binders_2117_);
lean_dec(v_snd_2110_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2258_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___f_2122_; lean_object* v___x_2123_; 
lean_inc(v_body_2118_);
v___f_2122_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__1___boxed), 10, 1);
lean_closure_set(v___f_2122_, 0, v_body_2118_);
v___x_2123_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_body_2118_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; lean_object* v___x_2125_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_a_2124_);
lean_dec_ref_known(v___x_2123_, 1);
v___x_2125_ = l_Lean_Elab_Do_EffectForwarder_ofCont(v_a_2124_, v_dec_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
lean_dec(v_a_2124_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v___y_2128_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2132_; lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2166_; lean_object* v___f_2198_; lean_object* v___x_2199_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc_n(v_a_2126_, 2);
lean_dec_ref_known(v___x_2125_, 1);
lean_inc_ref(v_a_2096_);
v___f_2198_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__2___boxed), 12, 3);
lean_closure_set(v___f_2198_, 0, v_a_2126_);
lean_closure_set(v___f_2198_, 1, v___f_2122_);
lean_closure_set(v___f_2198_, 2, v_a_2096_);
lean_inc(v_a_2102_);
lean_inc_ref(v_a_2101_);
lean_inc(v_a_2100_);
lean_inc_ref(v_a_2099_);
lean_inc(v_fst_2114_);
v___x_2199_ = lean_infer_type(v_fst_2114_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v___x_2201_; lean_object* v_a_2202_; lean_object* v_ref_2203_; uint8_t v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2209_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
lean_inc(v_a_2200_);
lean_dec_ref_known(v___x_2199_, 1);
v___x_2201_ = l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___redArg(v_a_2200_, v_a_2100_);
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_a_2202_);
lean_dec_ref(v___x_2201_);
v_ref_2203_ = lean_ctor_get(v_a_2101_, 2);
v___x_2204_ = 0;
v___x_2205_ = l_Lean_SourceInfo_fromRef(v_ref_2203_, v___x_2204_);
v___x_2206_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__3));
v___x_2207_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__4));
lean_inc(v___x_2205_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set_tag(v___x_2120_, 2);
lean_ctor_set(v___x_2120_, 1, v___x_2207_);
lean_ctor_set(v___x_2120_, 0, v___x_2205_);
v___x_2209_ = v___x_2120_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2205_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v___x_2207_);
v___x_2209_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
lean_object* v___x_2210_; size_t v_sz_2211_; size_t v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2210_ = l_Lean_Syntax_node1(v___x_2205_, v___x_2206_, v___x_2209_);
v_sz_2211_ = lean_array_size(v_binders_2117_);
v___x_2212_ = ((size_t)0ULL);
v___x_2213_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__2(v_sz_2211_, v___x_2212_, v_binders_2117_);
v___x_2214_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandFunBinders___boxed), 4, 2);
lean_closure_set(v___x_2214_, 0, v___x_2213_);
lean_closure_set(v___x_2214_, 1, v___x_2210_);
v___x_2215_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg(v___x_2214_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; lean_object* v_snd_2217_; lean_object* v_snd_2218_; uint8_t v___x_2219_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_a_2216_);
lean_dec_ref_known(v___x_2215_, 1);
v_snd_2217_ = lean_ctor_get(v_a_2216_, 1);
v_snd_2218_ = lean_ctor_get(v_snd_2217_, 1);
v___x_2219_ = lean_unbox(v_snd_2218_);
if (v___x_2219_ == 0)
{
lean_object* v_fst_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v_fst_2220_ = lean_ctor_get(v_a_2216_, 0);
lean_inc(v_fst_2220_);
lean_dec(v_a_2216_);
v___x_2221_ = lean_box(0);
v___x_2222_ = l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__3(v_a_2202_, v_fst_2220_, v___f_2198_, v___x_2221_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
lean_dec(v_fst_2220_);
v___y_2166_ = v___x_2222_;
goto v___jp_2165_;
}
else
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
lean_dec(v_a_2216_);
lean_dec(v_a_2202_);
lean_dec_ref(v___f_2198_);
lean_dec(v_a_2126_);
lean_dec(v_snd_2115_);
lean_dec(v_fst_2114_);
lean_del_object(v___x_2107_);
v___x_2223_ = lean_obj_once(&l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__6, &l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__6_once, _init_l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__6);
v___x_2224_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg(v___x_2223_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2224_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2224_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2225_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
lean_dec(v_a_2202_);
lean_dec_ref(v___f_2198_);
lean_dec(v_a_2126_);
lean_dec(v_snd_2115_);
lean_dec(v_fst_2114_);
lean_del_object(v___x_2107_);
v_a_2233_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___x_2215_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2215_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2233_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
}
else
{
lean_dec_ref(v___f_2198_);
lean_del_object(v___x_2120_);
lean_dec_ref(v_binders_2117_);
v___y_2166_ = v___x_2199_;
goto v___jp_2165_;
}
v___jp_2127_:
{
lean_object* v___x_2135_; 
v___x_2135_ = l_Lean_Elab_Do_EffectForwarder_restoreCont(v_a_2126_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2137_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2136_);
lean_dec_ref_known(v___x_2135_, 1);
v___x_2137_ = l_Lean_Elab_Do_DoElemCont_mkBindUnlessPure(v_a_2136_, v_snd_2115_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2148_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2140_ = v___x_2137_;
v_isShared_2141_ = v_isSharedCheck_2148_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2137_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2148_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 0, v_a_2138_);
v___x_2143_ = v___x_2107_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
lean_object* v___x_2145_; 
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 0, v___x_2143_);
v___x_2145_ = v___x_2140_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2143_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
else
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
lean_del_object(v___x_2107_);
v_a_2149_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2151_ = v___x_2137_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2137_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_a_2149_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
else
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
lean_dec(v_snd_2115_);
lean_del_object(v___x_2107_);
v_a_2157_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___x_2135_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2135_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
v___x_2162_ = v___x_2159_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2157_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
v___jp_2165_:
{
if (lean_obj_tag(v___y_2166_) == 0)
{
lean_object* v_a_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v_a_2167_ = lean_ctor_get(v___y_2166_, 0);
lean_inc(v_a_2167_);
lean_dec_ref_known(v___y_2166_, 1);
v___x_2168_ = l_Lean_Expr_mvarId_x21(v_fst_2114_);
lean_dec(v_fst_2114_);
lean_inc(v_a_2102_);
lean_inc_ref(v_a_2101_);
lean_inc(v_a_2100_);
lean_inc_ref(v_a_2099_);
v___x_2169_ = lean_checked_assign(v___x_2168_, v_a_2167_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; uint8_t v___x_2171_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_a_2170_);
lean_dec_ref_known(v___x_2169_, 1);
v___x_2171_ = lean_unbox(v_a_2170_);
lean_dec(v_a_2170_);
if (v___x_2171_ == 0)
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
lean_dec(v_a_2126_);
lean_dec(v_snd_2115_);
lean_del_object(v___x_2107_);
v___x_2172_ = lean_obj_once(&l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__1, &l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__1_once, _init_l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__1);
v___x_2173_ = l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0___redArg(v___x_2172_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2173_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2173_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2174_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
else
{
v___y_2128_ = v_a_2096_;
v___y_2129_ = v_a_2097_;
v___y_2130_ = v_a_2098_;
v___y_2131_ = v_a_2099_;
v___y_2132_ = v_a_2100_;
v___y_2133_ = v_a_2101_;
v___y_2134_ = v_a_2102_;
goto v___jp_2127_;
}
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_dec(v_a_2126_);
lean_dec(v_snd_2115_);
lean_del_object(v___x_2107_);
v_a_2182_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2169_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2169_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_dec(v_a_2126_);
lean_dec(v_snd_2115_);
lean_dec(v_fst_2114_);
lean_del_object(v___x_2107_);
v_a_2190_ = lean_ctor_get(v___y_2166_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___y_2166_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___y_2166_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___y_2166_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
}
else
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2249_; 
lean_dec_ref(v___f_2122_);
lean_del_object(v___x_2120_);
lean_dec_ref(v_binders_2117_);
lean_dec(v_snd_2115_);
lean_dec(v_fst_2114_);
lean_del_object(v___x_2107_);
v_a_2242_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2244_ = v___x_2125_;
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2125_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2247_; 
if (v_isShared_2245_ == 0)
{
v___x_2247_ = v___x_2244_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2242_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
lean_dec_ref(v___f_2122_);
lean_del_object(v___x_2120_);
lean_dec_ref(v_binders_2117_);
lean_dec(v_snd_2115_);
lean_dec(v_fst_2114_);
lean_del_object(v___x_2107_);
lean_dec_ref(v_dec_2095_);
v_a_2250_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2123_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2123_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2255_; 
if (v_isShared_2253_ == 0)
{
v___x_2255_ = v___x_2252_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2250_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
}
else
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
lean_dec(v_snd_2115_);
lean_dec(v_fst_2114_);
lean_dec(v_snd_2110_);
lean_del_object(v___x_2107_);
lean_dec_ref(v_dec_2095_);
v_a_2259_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___x_2116_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2116_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_a_2259_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
lean_dec(v_snd_2110_);
lean_dec(v_fst_2109_);
lean_del_object(v___x_2107_);
lean_dec_ref(v_dec_2095_);
v_a_2267_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v___x_2112_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2112_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2272_; 
if (v_isShared_2270_ == 0)
{
v___x_2272_ = v___x_2269_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_a_2267_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
}
else
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
lean_dec(v___x_2104_);
lean_dec_ref(v_dec_2095_);
v___x_2276_ = lean_box(0);
v___x_2277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2276_);
return v___x_2277_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_tryElabForwardApp_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2094_ = stack[0].m_obj;
lean_object* v_dec_2095_ = stack[1].m_obj;
lean_object* v_a_2096_ = stack[2].m_obj;
lean_object* v_a_2097_ = stack[3].m_obj;
lean_object* v_a_2098_ = stack[4].m_obj;
lean_object* v_a_2099_ = stack[5].m_obj;
lean_object* v_a_2100_ = stack[6].m_obj;
lean_object* v_a_2101_ = stack[7].m_obj;
lean_object* v_a_2102_ = stack[8].m_obj;
lean_object* v_res_2278_;
v_res_2278_ = l_Lean_Elab_Do_tryElabForwardApp_x3f(v_e_2094_, v_dec_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
stack->m_obj
 = v_res_2278_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___boxed(lean_object* v_e_2279_, lean_object* v_dec_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l_Lean_Elab_Do_tryElabForwardApp_x3f(v_e_2279_, v_dec_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
lean_dec(v_a_2287_);
lean_dec_ref(v_a_2286_);
lean_dec(v_a_2285_);
lean_dec_ref(v_a_2284_);
lean_dec(v_a_2283_);
lean_dec_ref(v_a_2282_);
lean_dec_ref(v_a_2281_);
return v_res_2289_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0(lean_object* v_00_u03b1_2290_, lean_object* v_msg_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v___x_2300_; 
v___x_2300_ = l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0___redArg(v_msg_2291_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
return v___x_2300_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2291_ = stack[1].m_obj;
lean_object* v___y_2292_ = stack[2].m_obj;
lean_object* v___y_2293_ = stack[3].m_obj;
lean_object* v___y_2294_ = stack[4].m_obj;
lean_object* v___y_2295_ = stack[5].m_obj;
lean_object* v___y_2296_ = stack[6].m_obj;
lean_object* v___y_2297_ = stack[7].m_obj;
lean_object* v___y_2298_ = stack[8].m_obj;
lean_object* v_res_2301_;
v_res_2301_ = l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0(lean_box(0), v_msg_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
stack->m_obj
 = v_res_2301_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0___boxed(lean_object* v_00_u03b1_2302_, lean_object* v_msg_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0(v_00_u03b1_2302_, v_msg_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec_ref(v___y_2304_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4(lean_object* v_00_u03b1_2313_, lean_object* v_x_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v___x_2317_; 
v___x_2317_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___redArg(v_x_2314_, v___y_2316_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2318_, lean_object* v_x_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4(v_00_u03b1_2318_, v_x_2319_, v___y_2320_, v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec_ref(v_x_2319_);
return v_res_2322_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9(lean_object* v_00_u03b1_2323_, lean_object* v_ref_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
lean_object* v___x_2332_; 
v___x_2332_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg(v_ref_2324_);
return v___x_2332_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2324_ = stack[1].m_obj;
lean_object* v___y_2325_ = stack[2].m_obj;
lean_object* v___y_2326_ = stack[3].m_obj;
lean_object* v___y_2327_ = stack[4].m_obj;
lean_object* v___y_2328_ = stack[5].m_obj;
lean_object* v___y_2329_ = stack[6].m_obj;
lean_object* v___y_2330_ = stack[7].m_obj;
lean_object* v_res_2333_;
v_res_2333_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9(lean_box(0), v_ref_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
stack->m_obj
 = v_res_2333_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___boxed(lean_object* v_00_u03b1_2334_, lean_object* v_ref_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9(v_00_u03b1_2334_, v_ref_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
lean_dec(v___y_2339_);
lean_dec_ref(v___y_2338_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
return v_res_2343_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10(lean_object* v_00_u03b1_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v___x_2352_; 
v___x_2352_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg();
return v___x_2352_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2345_ = stack[1].m_obj;
lean_object* v___y_2346_ = stack[2].m_obj;
lean_object* v___y_2347_ = stack[3].m_obj;
lean_object* v___y_2348_ = stack[4].m_obj;
lean_object* v___y_2349_ = stack[5].m_obj;
lean_object* v___y_2350_ = stack[6].m_obj;
lean_object* v_res_2353_;
v_res_2353_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10(lean_box(0), v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
stack->m_obj
 = v_res_2353_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___boxed(lean_object* v_00_u03b1_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10(v_00_u03b1_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
return v_res_2362_;
}
}
lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3(lean_object* v_00_u03b1_2363_, lean_object* v_x_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
lean_object* v___x_2372_; 
v___x_2372_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg(v_x_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
return v___x_2372_;
}
}
LEAN_EXPORT void l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2364_ = stack[1].m_obj;
lean_object* v___y_2365_ = stack[2].m_obj;
lean_object* v___y_2366_ = stack[3].m_obj;
lean_object* v___y_2367_ = stack[4].m_obj;
lean_object* v___y_2368_ = stack[5].m_obj;
lean_object* v___y_2369_ = stack[6].m_obj;
lean_object* v___y_2370_ = stack[7].m_obj;
lean_object* v_res_2373_;
v_res_2373_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3(lean_box(0), v_x_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
stack->m_obj
 = v_res_2373_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___boxed(lean_object* v_00_u03b1_2374_, lean_object* v_x_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3(v_00_u03b1_2374_, v_x_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
return v_res_2383_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3(lean_object* v_cls_2384_, lean_object* v_msg_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v___x_2393_; 
v___x_2393_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg(v_cls_2384_, v_msg_2385_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2393_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2384_ = stack[0].m_obj;
lean_object* v_msg_2385_ = stack[1].m_obj;
lean_object* v___y_2386_ = stack[2].m_obj;
lean_object* v___y_2387_ = stack[3].m_obj;
lean_object* v___y_2388_ = stack[4].m_obj;
lean_object* v___y_2389_ = stack[5].m_obj;
lean_object* v___y_2390_ = stack[6].m_obj;
lean_object* v___y_2391_ = stack[7].m_obj;
lean_object* v_res_2394_;
v_res_2394_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3(v_cls_2384_, v_msg_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
stack->m_obj
 = v_res_2394_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___boxed(lean_object* v_cls_2395_, lean_object* v_msg_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3(v_cls_2395_, v_msg_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
return v_res_2404_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6(lean_object* v_as_2405_, lean_object* v_as_x27_2406_, lean_object* v_b_2407_, lean_object* v_a_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v___x_2416_; 
v___x_2416_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6___redArg(v_as_x27_2406_, v_b_2407_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
return v___x_2416_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2405_ = stack[0].m_obj;
lean_object* v_as_x27_2406_ = stack[1].m_obj;
lean_object* v_b_2407_ = stack[2].m_obj;
lean_object* v___y_2409_ = stack[4].m_obj;
lean_object* v___y_2410_ = stack[5].m_obj;
lean_object* v___y_2411_ = stack[6].m_obj;
lean_object* v___y_2412_ = stack[7].m_obj;
lean_object* v___y_2413_ = stack[8].m_obj;
lean_object* v___y_2414_ = stack[9].m_obj;
lean_object* v_res_2417_;
v_res_2417_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6(v_as_2405_, v_as_x27_2406_, v_b_2407_, lean_box(0), v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
stack->m_obj
 = v_res_2417_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6___boxed(lean_object* v_as_2418_, lean_object* v_as_x27_2419_, lean_object* v_b_2420_, lean_object* v_a_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v_res_2429_; 
v_res_2429_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6(v_as_2418_, v_as_x27_2419_, v_b_2420_, v_a_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v_as_x27_2419_);
lean_dec(v_as_2418_);
return v_res_2429_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8(lean_object* v_00_u03b1_2430_, lean_object* v_ref_2431_, lean_object* v_msg_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_){
_start:
{
lean_object* v___x_2440_; 
v___x_2440_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8___redArg(v_ref_2431_, v_msg_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_);
return v___x_2440_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2431_ = stack[1].m_obj;
lean_object* v_msg_2432_ = stack[2].m_obj;
lean_object* v___y_2433_ = stack[3].m_obj;
lean_object* v___y_2434_ = stack[4].m_obj;
lean_object* v___y_2435_ = stack[5].m_obj;
lean_object* v___y_2436_ = stack[6].m_obj;
lean_object* v___y_2437_ = stack[7].m_obj;
lean_object* v___y_2438_ = stack[8].m_obj;
lean_object* v_res_2441_;
v_res_2441_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8(lean_box(0), v_ref_2431_, v_msg_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_);
stack->m_obj
 = v_res_2441_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8___boxed(lean_object* v_00_u03b1_2442_, lean_object* v_ref_2443_, lean_object* v_msg_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8(v_00_u03b1_2442_, v_ref_2443_, v_msg_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v_ref_2443_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_2453_, lean_object* v_m_2454_, lean_object* v_a_2455_){
_start:
{
lean_object* v___x_2456_; 
v___x_2456_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8___redArg(v_m_2454_, v_a_2455_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_2457_, lean_object* v_m_2458_, lean_object* v_a_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8(v_00_u03b2_2457_, v_m_2458_, v_a_2459_);
lean_dec(v_a_2459_);
lean_dec_ref(v_m_2458_);
return v_res_2460_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9(lean_object* v_00_u03b2_2461_, lean_object* v_x_2462_, lean_object* v_x_2463_){
_start:
{
uint8_t v___x_2464_; 
v___x_2464_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9___redArg(v_x_2462_, v_x_2463_);
return v___x_2464_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2462_ = stack[1].m_obj;
lean_object* v_x_2463_ = stack[2].m_obj;
uint8_t v_res_2465_;
v_res_2465_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9(lean_box(0), v_x_2462_, v_x_2463_);
stack->m_num = v_res_2465_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9___boxed(lean_object* v_00_u03b2_2466_, lean_object* v_x_2467_, lean_object* v_x_2468_){
_start:
{
uint8_t v_res_2469_; lean_object* v_r_2470_; 
v_res_2469_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9(v_00_u03b2_2466_, v_x_2467_, v_x_2468_);
lean_dec_ref(v_x_2468_);
lean_dec_ref(v_x_2467_);
v_r_2470_ = lean_box(v_res_2469_);
return v_r_2470_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12(lean_object* v_00_u03b2_2471_, lean_object* v_a_2472_, lean_object* v_x_2473_){
_start:
{
lean_object* v___x_2474_; 
v___x_2474_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12___redArg(v_a_2472_, v_x_2473_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12___boxed(lean_object* v_00_u03b2_2475_, lean_object* v_a_2476_, lean_object* v_x_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12(v_00_u03b2_2475_, v_a_2476_, v_x_2477_);
lean_dec(v_x_2477_);
lean_dec(v_a_2476_);
return v_res_2478_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13(lean_object* v_00_u03b2_2479_, lean_object* v_x_2480_, size_t v_x_2481_, lean_object* v_x_2482_){
_start:
{
uint8_t v___x_2483_; 
v___x_2483_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13___redArg(v_x_2480_, v_x_2481_, v_x_2482_);
return v___x_2483_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2480_ = stack[1].m_obj;
size_t v_x_2481_ = stack[2].m_num;
lean_object* v_x_2482_ = stack[3].m_obj;
uint8_t v_res_2484_;
v_res_2484_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13(lean_box(0), v_x_2480_, v_x_2481_, v_x_2482_);
stack->m_num = v_res_2484_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13___boxed(lean_object* v_00_u03b2_2485_, lean_object* v_x_2486_, lean_object* v_x_2487_, lean_object* v_x_2488_){
_start:
{
size_t v_x_31193__boxed_2489_; uint8_t v_res_2490_; lean_object* v_r_2491_; 
v_x_31193__boxed_2489_ = lean_unbox_usize(v_x_2487_);
lean_dec(v_x_2487_);
v_res_2490_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13(v_00_u03b2_2485_, v_x_2486_, v_x_31193__boxed_2489_, v_x_2488_);
lean_dec_ref(v_x_2488_);
lean_dec_ref(v_x_2486_);
v_r_2491_ = lean_box(v_res_2490_);
return v_r_2491_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16(lean_object* v_00_u03b2_2492_, lean_object* v_keys_2493_, lean_object* v_vals_2494_, lean_object* v_heq_2495_, lean_object* v_i_2496_, lean_object* v_k_2497_){
_start:
{
uint8_t v___x_2498_; 
v___x_2498_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16___redArg(v_keys_2493_, v_i_2496_, v_k_2497_);
return v___x_2498_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_2493_ = stack[1].m_obj;
lean_object* v_vals_2494_ = stack[2].m_obj;
lean_object* v_i_2496_ = stack[4].m_obj;
lean_object* v_k_2497_ = stack[5].m_obj;
uint8_t v_res_2499_;
v_res_2499_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16(lean_box(0), v_keys_2493_, v_vals_2494_, lean_box(0), v_i_2496_, v_k_2497_);
stack->m_num = v_res_2499_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16___boxed(lean_object* v_00_u03b2_2500_, lean_object* v_keys_2501_, lean_object* v_vals_2502_, lean_object* v_heq_2503_, lean_object* v_i_2504_, lean_object* v_k_2505_){
_start:
{
uint8_t v_res_2506_; lean_object* v_r_2507_; 
v_res_2506_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16(v_00_u03b2_2500_, v_keys_2501_, v_vals_2502_, v_heq_2503_, v_i_2504_, v_k_2505_);
lean_dec_ref(v_k_2505_);
lean_dec_ref(v_vals_2502_);
lean_dec_ref(v_keys_2501_);
v_r_2507_ = lean_box(v_res_2506_);
return v_r_2507_;
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
