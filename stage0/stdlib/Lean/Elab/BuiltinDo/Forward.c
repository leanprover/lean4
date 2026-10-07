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
lean_object* v___x_91_; lean_object* v_env_92_; uint8_t v___x_93_; lean_object* v_env_94_; lean_object* v___x_95_; lean_object* v_toCold_96_; lean_object* v_mctx_97_; lean_object* v_lctx_98_; lean_object* v_options_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_91_ = lean_st_ref_get(v___y_89_);
v_env_92_ = lean_ctor_get(v___x_91_, 0);
lean_inc_ref(v_env_92_);
lean_dec(v___x_91_);
v___x_93_ = 0;
v_env_94_ = l_Lean_Environment_setRecordingDeps(v_env_92_, v___x_93_);
v___x_95_ = lean_st_ref_get(v___y_87_);
v_toCold_96_ = lean_ctor_get(v___y_88_, 0);
v_mctx_97_ = lean_ctor_get(v___x_95_, 0);
lean_inc_ref(v_mctx_97_);
lean_dec(v___x_95_);
v_lctx_98_ = lean_ctor_get(v___y_86_, 2);
v_options_99_ = lean_ctor_get(v_toCold_96_, 2);
lean_inc_ref(v_options_99_);
lean_inc_ref(v_lctx_98_);
v___x_100_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_100_, 0, v_env_94_);
lean_ctor_set(v___x_100_, 1, v_mctx_97_);
lean_ctor_set(v___x_100_, 2, v_lctx_98_);
lean_ctor_set(v___x_100_, 3, v_options_99_);
v___x_101_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v_msgData_85_);
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0___boxed(lean_object* v_msgData_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0(v_msgData_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_106_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg(lean_object* v_msg_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_ref_118_; lean_object* v_macroStack_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v_a_122_; lean_object* v___x_123_; lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_132_; 
v_ref_118_ = lean_ctor_get(v___y_115_, 2);
v_macroStack_119_ = lean_ctor_get(v___y_111_, 1);
v___x_120_ = l_Lean_Elab_getBetterRef(v_ref_118_, v_macroStack_119_);
v___x_121_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0(v_msg_110_, v___y_113_, v___y_114_, v___y_115_, v___y_116_);
v_a_122_ = lean_ctor_get(v___x_121_, 0);
lean_inc(v_a_122_);
lean_dec_ref(v___x_121_);
lean_inc(v_macroStack_119_);
v___x_123_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg(v_a_122_, v_macroStack_119_, v___y_115_);
v_a_124_ = lean_ctor_get(v___x_123_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_132_ == 0)
{
v___x_126_ = v___x_123_;
v_isShared_127_ = v_isSharedCheck_132_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_dec(v___x_123_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_132_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_128_; lean_object* v___x_130_; 
v___x_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_120_);
lean_ctor_set(v___x_128_, 1, v_a_124_);
if (v_isShared_127_ == 0)
{
lean_ctor_set_tag(v___x_126_, 1);
lean_ctor_set(v___x_126_, 0, v___x_128_);
v___x_130_ = v___x_126_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_128_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg___boxed(lean_object* v_msg_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg(v_msg_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
return v_res_141_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoForward___redArg___closed__1(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = ((lean_object*)(l_Lean_Elab_Do_elabDoForward___redArg___closed__0));
v___x_144_ = l_Lean_stringToMessageData(v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoForward___redArg(lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_obj_once(&l_Lean_Elab_Do_elabDoForward___redArg___closed__1, &l_Lean_Elab_Do_elabDoForward___redArg___closed__1_once, _init_l_Lean_Elab_Do_elabDoForward___redArg___closed__1);
v___x_153_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg(v___x_152_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoForward___redArg___boxed(lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_Elab_Do_elabDoForward___redArg(v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_);
lean_dec(v_a_159_);
lean_dec_ref(v_a_158_);
lean_dec(v_a_157_);
lean_dec_ref(v_a_156_);
lean_dec(v_a_155_);
lean_dec_ref(v_a_154_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoForward(lean_object* v_x_162_, lean_object* v_x_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l_Lean_Elab_Do_elabDoForward___redArg(v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoForward___boxed(lean_object* v_x_172_, lean_object* v_x_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lean_Elab_Do_elabDoForward(v_x_172_, v_x_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_);
lean_dec(v_a_179_);
lean_dec_ref(v_a_178_);
lean_dec(v_a_177_);
lean_dec_ref(v_a_176_);
lean_dec(v_a_175_);
lean_dec_ref(v_a_174_);
lean_dec(v_x_173_);
lean_dec(v_x_172_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0(lean_object* v_00_u03b1_182_, lean_object* v_msg_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg(v_msg_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___boxed(lean_object* v_00_u03b1_192_, lean_object* v_msg_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0(v_00_u03b1_192_, v_msg_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1(lean_object* v_msgData_202_, lean_object* v_macroStack_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg(v_msgData_202_, v_macroStack_203_, v___y_208_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___boxed(lean_object* v_msgData_212_, lean_object* v_macroStack_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1(v_msgData_212_, v_macroStack_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1(){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_240_ = l_Lean_Elab_Term_termElabAttribute;
v___x_241_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__4));
v___x_242_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__8));
v___x_243_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoForward___boxed), 9, 0);
v___x_244_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_240_, v___x_241_, v___x_242_, v___x_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___boxed(lean_object* v_a_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1();
return v_res_246_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__0));
v___x_249_ = l_Lean_stringToMessageData(v___x_248_);
return v___x_249_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__3(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__2));
v___x_252_ = l_Lean_stringToMessageData(v___x_251_);
return v___x_252_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__5(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__4));
v___x_255_ = l_Lean_stringToMessageData(v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint(lean_object* v_headApp_256_, lean_object* v_reason_257_){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_258_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1);
v___x_259_ = l_Lean_MessageData_ofSyntax(v_headApp_256_);
v___x_260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_258_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
v___x_261_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__3, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__3);
v___x_262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_260_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
v___x_263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v_reason_257_);
v___x_264_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__5, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__5_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__5);
v___x_265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_263_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(lean_object* v_e_266_, lean_object* v___y_267_){
_start:
{
uint8_t v___x_269_; 
v___x_269_ = l_Lean_Expr_hasMVar(v_e_266_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; 
v___x_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_270_, 0, v_e_266_);
return v___x_270_;
}
else
{
lean_object* v___x_271_; lean_object* v_mctx_272_; lean_object* v___x_273_; lean_object* v_fst_274_; lean_object* v_snd_275_; lean_object* v___x_276_; lean_object* v_cache_277_; lean_object* v_zetaDeltaFVarIds_278_; lean_object* v_postponed_279_; lean_object* v_diag_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_289_; 
v___x_271_ = lean_st_ref_get(v___y_267_);
v_mctx_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc_ref(v_mctx_272_);
lean_dec(v___x_271_);
v___x_273_ = l_Lean_instantiateMVarsCore(v_mctx_272_, v_e_266_);
v_fst_274_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_fst_274_);
v_snd_275_ = lean_ctor_get(v___x_273_, 1);
lean_inc(v_snd_275_);
lean_dec_ref(v___x_273_);
v___x_276_ = lean_st_ref_take(v___y_267_);
v_cache_277_ = lean_ctor_get(v___x_276_, 1);
v_zetaDeltaFVarIds_278_ = lean_ctor_get(v___x_276_, 2);
v_postponed_279_ = lean_ctor_get(v___x_276_, 3);
v_diag_280_ = lean_ctor_get(v___x_276_, 4);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_289_ == 0)
{
lean_object* v_unused_290_; 
v_unused_290_ = lean_ctor_get(v___x_276_, 0);
lean_dec(v_unused_290_);
v___x_282_ = v___x_276_;
v_isShared_283_ = v_isSharedCheck_289_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_diag_280_);
lean_inc(v_postponed_279_);
lean_inc(v_zetaDeltaFVarIds_278_);
lean_inc(v_cache_277_);
lean_dec(v___x_276_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_289_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v_snd_275_);
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_snd_275_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v_cache_277_);
lean_ctor_set(v_reuseFailAlloc_288_, 2, v_zetaDeltaFVarIds_278_);
lean_ctor_set(v_reuseFailAlloc_288_, 3, v_postponed_279_);
lean_ctor_set(v_reuseFailAlloc_288_, 4, v_diag_280_);
v___x_285_ = v_reuseFailAlloc_288_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = lean_st_ref_put(v___y_267_, v___x_285_);
v___x_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_287_, 0, v_fst_274_);
return v___x_287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg___boxed(lean_object* v_e_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_e_291_, v___y_292_);
lean_dec(v___y_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1(lean_object* v_e_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_e_295_, v___y_297_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___boxed(lean_object* v_e_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1(v_e_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___lam__0(lean_object* v_k_309_, lean_object* v_b_310_, lean_object* v_c_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v___x_317_; 
lean_inc(v___y_315_);
lean_inc_ref(v___y_314_);
lean_inc(v___y_313_);
lean_inc_ref(v___y_312_);
v___x_317_ = lean_apply_7(v_k_309_, v_b_310_, v_c_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, lean_box(0));
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___lam__0___boxed(lean_object* v_k_318_, lean_object* v_b_319_, lean_object* v_c_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___lam__0(v_k_318_, v_b_319_, v_c_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg(lean_object* v_type_327_, lean_object* v_k_328_, uint8_t v_cleanupAnnotations_329_, uint8_t v_whnfType_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v___f_336_; lean_object* v___x_337_; 
v___f_336_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_336_, 0, v_k_328_);
v___x_337_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_327_, v___f_336_, v_cleanupAnnotations_329_, v_whnfType_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_345_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_345_ == 0)
{
v___x_340_ = v___x_337_;
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_337_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_341_ == 0)
{
v___x_343_ = v___x_340_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_a_338_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
v_a_346_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_337_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_337_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___boxed(lean_object* v_type_354_, lean_object* v_k_355_, lean_object* v_cleanupAnnotations_356_, lean_object* v_whnfType_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_363_; uint8_t v_whnfType_boxed_364_; lean_object* v_res_365_; 
v_cleanupAnnotations_boxed_363_ = lean_unbox(v_cleanupAnnotations_356_);
v_whnfType_boxed_364_ = lean_unbox(v_whnfType_357_);
v_res_365_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg(v_type_354_, v_k_355_, v_cleanupAnnotations_boxed_363_, v_whnfType_boxed_364_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4(lean_object* v_00_u03b1_366_, lean_object* v_type_367_, lean_object* v_k_368_, uint8_t v_cleanupAnnotations_369_, uint8_t v_whnfType_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg(v_type_367_, v_k_368_, v_cleanupAnnotations_369_, v_whnfType_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___boxed(lean_object* v_00_u03b1_377_, lean_object* v_type_378_, lean_object* v_k_379_, lean_object* v_cleanupAnnotations_380_, lean_object* v_whnfType_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_387_; uint8_t v_whnfType_boxed_388_; lean_object* v_res_389_; 
v_cleanupAnnotations_boxed_387_ = lean_unbox(v_cleanupAnnotations_380_);
v_whnfType_boxed_388_ = lean_unbox(v_whnfType_381_);
v_res_389_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4(v_00_u03b1_377_, v_type_378_, v_k_379_, v_cleanupAnnotations_boxed_387_, v_whnfType_boxed_388_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(lean_object* v_msg_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_ref_396_; lean_object* v___x_397_; lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_406_; 
v_ref_396_ = lean_ctor_get(v___y_393_, 2);
v___x_397_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0(v_msg_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_);
v_a_398_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_406_ == 0)
{
v___x_400_ = v___x_397_;
v_isShared_401_ = v_isSharedCheck_406_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_397_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_406_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v___x_404_; 
lean_inc(v_ref_396_);
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v_ref_396_);
lean_ctor_set(v___x_402_, 1, v_a_398_);
if (v_isShared_401_ == 0)
{
lean_ctor_set_tag(v___x_400_, 1);
lean_ctor_set(v___x_400_, 0, v___x_402_);
v___x_404_ = v___x_400_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg___boxed(lean_object* v_msg_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v_msg_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0(lean_object* v_headApp_414_, lean_object* v_00_u03b1_415_, lean_object* v_reason_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint(v_headApp_414_, v_reason_416_);
v___x_423_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v___x_422_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0___boxed(lean_object* v_headApp_424_, lean_object* v_00_u03b1_425_, lean_object* v_reason_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0(v_headApp_424_, v_00_u03b1_425_, v_reason_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
return v_res_432_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0(lean_object* v_arg_433_, lean_object* v_x_434_){
_start:
{
lean_object* v___x_435_; uint8_t v___x_436_; 
v___x_435_ = l_Lean_Expr_mvarId_x21(v_arg_433_);
v___x_436_ = l_Lean_instBEqMVarId_beq(v_x_434_, v___x_435_);
lean_dec(v___x_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0___boxed(lean_object* v_arg_437_, lean_object* v_x_438_){
_start:
{
uint8_t v_res_439_; lean_object* v_r_440_; 
v_res_439_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0(v_arg_437_, v_x_438_);
lean_dec(v_x_438_);
lean_dec_ref(v_arg_437_);
v_r_440_ = lean_box(v_res_439_);
return v_r_440_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__0));
v___x_443_ = l_Lean_stringToMessageData(v___x_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4(lean_object* v_arg_444_, lean_object* v_headApp_445_, lean_object* v_as_446_, size_t v_sz_447_, size_t v_i_448_, lean_object* v_b_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_a_456_; uint8_t v___x_460_; 
v___x_460_ = lean_usize_dec_lt(v_i_448_, v_sz_447_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; 
lean_dec(v_headApp_445_);
lean_dec_ref(v_arg_444_);
v___x_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_461_, 0, v_b_449_);
return v___x_461_;
}
else
{
lean_object* v___f_462_; lean_object* v___x_463_; lean_object* v_a_464_; lean_object* v___x_465_; 
lean_inc_ref(v_arg_444_);
v___f_462_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_462_, 0, v_arg_444_);
v___x_463_ = lean_box(0);
v_a_464_ = lean_array_uget_borrowed(v_as_446_, v_i_448_);
lean_inc(v___y_453_);
lean_inc_ref(v___y_452_);
lean_inc(v___y_451_);
lean_inc_ref(v___y_450_);
lean_inc(v_a_464_);
v___x_465_ = lean_infer_type(v_a_464_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v_a_466_; lean_object* v___x_467_; 
v_a_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc_n(v_a_466_, 2);
lean_dec_ref_known(v___x_465_, 1);
v___x_467_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_a_466_, v___y_451_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_a_468_);
lean_dec_ref_known(v___x_467_, 1);
v___x_469_ = lean_box(0);
v___x_470_ = l_Lean_FindMVar_main(v___f_462_, v_a_468_, v___x_469_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_dec(v_a_466_);
v_a_456_ = v___x_463_;
goto v___jp_455_;
}
else
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
lean_dec_ref_known(v___x_470_, 1);
v___x_471_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1);
v___x_472_ = l_Lean_MessageData_ofExpr(v_a_466_);
v___x_473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_471_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
v___x_474_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1);
v___x_475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_473_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
lean_inc(v_headApp_445_);
v___x_476_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint(v_headApp_445_, v___x_475_);
v___x_477_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v___x_476_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_dec_ref_known(v___x_477_, 1);
v_a_456_ = v___x_463_;
goto v___jp_455_;
}
else
{
lean_dec(v_headApp_445_);
lean_dec_ref(v_arg_444_);
return v___x_477_;
}
}
}
else
{
lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_485_; 
lean_dec(v_a_466_);
lean_dec_ref(v___f_462_);
lean_dec(v_headApp_445_);
lean_dec_ref(v_arg_444_);
v_a_478_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_485_ == 0)
{
v___x_480_ = v___x_467_;
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___x_467_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_483_; 
if (v_isShared_481_ == 0)
{
v___x_483_ = v___x_480_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_a_478_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
}
else
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
lean_dec_ref(v___f_462_);
lean_dec(v_headApp_445_);
lean_dec_ref(v_arg_444_);
v_a_486_ = lean_ctor_get(v___x_465_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___x_465_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_465_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
v___jp_455_:
{
size_t v___x_457_; size_t v___x_458_; 
v___x_457_ = ((size_t)1ULL);
v___x_458_ = lean_usize_add(v_i_448_, v___x_457_);
v_i_448_ = v___x_458_;
v_b_449_ = v_a_456_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___boxed(lean_object* v_arg_494_, lean_object* v_headApp_495_, lean_object* v_as_496_, lean_object* v_sz_497_, lean_object* v_i_498_, lean_object* v_b_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
size_t v_sz_boxed_505_; size_t v_i_boxed_506_; lean_object* v_res_507_; 
v_sz_boxed_505_ = lean_unbox_usize(v_sz_497_);
lean_dec(v_sz_497_);
v_i_boxed_506_ = lean_unbox_usize(v_i_498_);
lean_dec(v_i_498_);
v_res_507_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4(v_arg_494_, v_headApp_495_, v_as_496_, v_sz_boxed_505_, v_i_boxed_506_, v_b_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec_ref(v_as_496_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3(lean_object* v_arg_508_, lean_object* v_headApp_509_, lean_object* v_as_510_, size_t v_sz_511_, size_t v_i_512_, lean_object* v_b_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v_a_520_; uint8_t v___x_524_; 
v___x_524_ = lean_usize_dec_lt(v_i_512_, v_sz_511_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; 
lean_dec(v_headApp_509_);
lean_dec_ref(v_arg_508_);
v___x_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_525_, 0, v_b_513_);
return v___x_525_;
}
else
{
lean_object* v___f_526_; lean_object* v___x_527_; lean_object* v_a_528_; lean_object* v___x_529_; 
lean_inc_ref(v_arg_508_);
v___f_526_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_526_, 0, v_arg_508_);
v___x_527_ = lean_box(0);
v_a_528_ = lean_array_uget_borrowed(v_as_510_, v_i_512_);
lean_inc(v___y_517_);
lean_inc_ref(v___y_516_);
lean_inc(v___y_515_);
lean_inc_ref(v___y_514_);
lean_inc(v_a_528_);
v___x_529_ = lean_infer_type(v_a_528_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; lean_object* v___x_531_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc_n(v_a_530_, 2);
lean_dec_ref_known(v___x_529_, 1);
v___x_531_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_a_530_, v___y_515_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v_a_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v_a_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_a_532_);
lean_dec_ref_known(v___x_531_, 1);
v___x_533_ = lean_box(0);
v___x_534_ = l_Lean_FindMVar_main(v___f_526_, v_a_532_, v___x_533_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_dec(v_a_530_);
v_a_520_ = v___x_527_;
goto v___jp_519_;
}
else
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
lean_dec_ref_known(v___x_534_, 1);
v___x_535_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1);
v___x_536_ = l_Lean_MessageData_ofExpr(v_a_530_);
v___x_537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1);
v___x_539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_537_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
lean_inc(v_headApp_509_);
v___x_540_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint(v_headApp_509_, v___x_539_);
v___x_541_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v___x_540_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_dec_ref_known(v___x_541_, 1);
v_a_520_ = v___x_527_;
goto v___jp_519_;
}
else
{
lean_dec(v_headApp_509_);
lean_dec_ref(v_arg_508_);
return v___x_541_;
}
}
}
else
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
lean_dec(v_a_530_);
lean_dec_ref(v___f_526_);
lean_dec(v_headApp_509_);
lean_dec_ref(v_arg_508_);
v_a_542_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_531_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_531_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
else
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
lean_dec_ref(v___f_526_);
lean_dec(v_headApp_509_);
lean_dec_ref(v_arg_508_);
v_a_550_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_529_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_529_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
v___jp_519_:
{
size_t v___x_521_; size_t v___x_522_; lean_object* v___x_523_; 
v___x_521_ = ((size_t)1ULL);
v___x_522_ = lean_usize_add(v_i_512_, v___x_521_);
v___x_523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4(v_arg_508_, v_headApp_509_, v_as_510_, v_sz_511_, v___x_522_, v_a_520_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
return v___x_523_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3___boxed(lean_object* v_arg_558_, lean_object* v_headApp_559_, lean_object* v_as_560_, lean_object* v_sz_561_, lean_object* v_i_562_, lean_object* v_b_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
size_t v_sz_boxed_569_; size_t v_i_boxed_570_; lean_object* v_res_571_; 
v_sz_boxed_569_ = lean_unbox_usize(v_sz_561_);
lean_dec(v_sz_561_);
v_i_boxed_570_ = lean_unbox_usize(v_i_562_);
lean_dec(v_i_562_);
v_res_571_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3(v_arg_558_, v_headApp_559_, v_as_560_, v_sz_boxed_569_, v_i_boxed_570_, v_b_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec_ref(v_as_560_);
return v_res_571_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__1(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__0));
v___x_574_ = l_Lean_stringToMessageData(v___x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1(lean_object* v_arg_575_, lean_object* v_headApp_576_, lean_object* v_a_577_, lean_object* v_reject_578_, lean_object* v_args_579_, lean_object* v_body_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v___x_599_; lean_object* v_a_600_; lean_object* v___x_601_; 
v___x_599_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_body_580_, v___y_582_);
v_a_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_a_600_);
lean_dec_ref(v___x_599_);
v___x_601_ = l_Lean_Meta_whnfD(v_a_600_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; lean_object* v___x_603_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_a_602_);
lean_dec_ref_known(v___x_601_, 1);
v___x_603_ = l_Lean_Meta_isExprDefEq(v_a_577_, v_a_602_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v_a_604_; uint8_t v___x_605_; 
v_a_604_ = lean_ctor_get(v___x_603_, 0);
lean_inc(v_a_604_);
lean_dec_ref_known(v___x_603_, 1);
v___x_605_ = lean_unbox(v_a_604_);
lean_dec(v_a_604_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__1);
lean_inc(v___y_584_);
lean_inc_ref(v___y_583_);
lean_inc(v___y_582_);
lean_inc_ref(v___y_581_);
v___x_607_ = lean_apply_7(v_reject_578_, lean_box(0), v___x_606_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, lean_box(0));
if (lean_obj_tag(v___x_607_) == 0)
{
lean_dec_ref_known(v___x_607_, 1);
goto v___jp_586_;
}
else
{
lean_dec(v_headApp_576_);
lean_dec_ref(v_arg_575_);
return v___x_607_;
}
}
else
{
lean_dec_ref(v_reject_578_);
goto v___jp_586_;
}
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
lean_dec_ref(v_reject_578_);
lean_dec(v_headApp_576_);
lean_dec_ref(v_arg_575_);
v_a_608_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_603_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_603_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
else
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
lean_dec_ref(v_reject_578_);
lean_dec_ref(v_a_577_);
lean_dec(v_headApp_576_);
lean_dec_ref(v_arg_575_);
v_a_616_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_601_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_601_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
v___jp_586_:
{
lean_object* v___x_587_; size_t v_sz_588_; size_t v___x_589_; lean_object* v___x_590_; 
v___x_587_ = lean_box(0);
v_sz_588_ = lean_array_size(v_args_579_);
v___x_589_ = ((size_t)0ULL);
v___x_590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3(v_arg_575_, v_headApp_576_, v_args_579_, v_sz_588_, v___x_589_, v___x_587_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_597_ == 0)
{
lean_object* v_unused_598_; 
v_unused_598_ = lean_ctor_get(v___x_590_, 0);
lean_dec(v_unused_598_);
v___x_592_ = v___x_590_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_dec(v___x_590_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v___x_587_);
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_587_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
else
{
return v___x_590_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___boxed(lean_object* v_arg_624_, lean_object* v_headApp_625_, lean_object* v_a_626_, lean_object* v_reject_627_, lean_object* v_args_628_, lean_object* v_body_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1(v_arg_624_, v_headApp_625_, v_a_626_, v_reject_627_, v_args_628_, v_body_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec_ref(v_args_628_);
return v_res_635_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__0));
v___x_638_ = l_Lean_stringToMessageData(v___x_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2(lean_object* v_forwarded_639_, lean_object* v_arg_640_, lean_object* v_headApp_641_, lean_object* v_as_642_, size_t v_sz_643_, size_t v_i_644_, lean_object* v_b_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v_a_652_; uint8_t v___x_656_; 
v___x_656_ = lean_usize_dec_lt(v_i_644_, v_sz_643_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; 
lean_dec(v_headApp_641_);
lean_dec_ref(v_arg_640_);
v___x_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_657_, 0, v_b_645_);
return v___x_657_;
}
else
{
lean_object* v_a_658_; lean_object* v_fst_659_; lean_object* v_snd_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_720_; 
v_a_658_ = lean_array_uget(v_as_642_, v_i_644_);
v_fst_659_ = lean_ctor_get(v_a_658_, 0);
v_snd_660_ = lean_ctor_get(v_a_658_, 1);
v_isSharedCheck_720_ = !lean_is_exclusive(v_a_658_);
if (v_isSharedCheck_720_ == 0)
{
v___x_662_ = v_a_658_;
v_isShared_663_ = v_isSharedCheck_720_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_snd_660_);
lean_inc(v_fst_659_);
lean_dec(v_a_658_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_720_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___f_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
lean_inc_ref(v_arg_640_);
v___f_664_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_664_, 0, v_arg_640_);
v___x_665_ = lean_box(0);
v___x_666_ = l_Lean_Expr_fvarId_x21(v_fst_659_);
lean_dec(v_fst_659_);
v___x_667_ = l_Lean_FVarId_getDecl___redArg(v___x_666_, v___y_646_, v___y_648_, v___y_649_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_a_668_; uint8_t v___x_669_; 
v_a_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_a_668_);
lean_dec_ref_known(v___x_667_, 1);
v___x_669_ = l_Lean_LocalDecl_binderInfo(v_a_668_);
lean_dec(v_a_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; 
v___x_670_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_snd_660_, v___y_647_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; uint8_t v___x_672_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_a_671_);
lean_dec_ref_known(v___x_670_, 1);
v___x_672_ = lean_expr_eqv(v_a_671_, v_forwarded_639_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; 
lean_inc(v___y_649_);
lean_inc_ref(v___y_648_);
lean_inc(v___y_647_);
lean_inc_ref(v___y_646_);
v___x_673_ = lean_infer_type(v_a_671_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v___x_675_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc_n(v_a_674_, 2);
lean_dec_ref_known(v___x_673_, 1);
v___x_675_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_a_674_, v___y_647_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_a_676_);
lean_dec_ref_known(v___x_675_, 1);
v___x_677_ = lean_box(0);
v___x_678_ = l_Lean_FindMVar_main(v___f_664_, v_a_676_, v___x_677_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_dec(v_a_674_);
lean_del_object(v___x_662_);
v_a_652_ = v___x_665_;
goto v___jp_651_;
}
else
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_682_; 
lean_dec_ref_known(v___x_678_, 1);
v___x_679_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1);
v___x_680_ = l_Lean_MessageData_ofExpr(v_a_674_);
if (v_isShared_663_ == 0)
{
lean_ctor_set_tag(v___x_662_, 7);
lean_ctor_set(v___x_662_, 1, v___x_680_);
lean_ctor_set(v___x_662_, 0, v___x_679_);
v___x_682_ = v___x_662_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_679_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v___x_680_);
v___x_682_ = v_reuseFailAlloc_687_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_683_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1);
v___x_684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_682_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
lean_inc(v_headApp_641_);
v___x_685_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint(v_headApp_641_, v___x_684_);
v___x_686_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v___x_685_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_dec_ref_known(v___x_686_, 1);
v_a_652_ = v___x_665_;
goto v___jp_651_;
}
else
{
lean_dec(v_headApp_641_);
lean_dec_ref(v_arg_640_);
return v___x_686_;
}
}
}
}
else
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
lean_dec(v_a_674_);
lean_dec_ref(v___f_664_);
lean_del_object(v___x_662_);
lean_dec(v_headApp_641_);
lean_dec_ref(v_arg_640_);
v_a_688_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v___x_675_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_675_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_688_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
lean_dec_ref(v___f_664_);
lean_del_object(v___x_662_);
lean_dec(v_headApp_641_);
lean_dec_ref(v_arg_640_);
v_a_696_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_673_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_673_);
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
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
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
else
{
lean_dec(v_a_671_);
lean_dec_ref(v___f_664_);
lean_del_object(v___x_662_);
v_a_652_ = v___x_665_;
goto v___jp_651_;
}
}
else
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
lean_dec_ref(v___f_664_);
lean_del_object(v___x_662_);
lean_dec(v_headApp_641_);
lean_dec_ref(v_arg_640_);
v_a_704_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_670_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_670_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_704_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
else
{
lean_dec_ref(v___f_664_);
lean_del_object(v___x_662_);
lean_dec(v_snd_660_);
v_a_652_ = v___x_665_;
goto v___jp_651_;
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
lean_dec_ref(v___f_664_);
lean_del_object(v___x_662_);
lean_dec(v_snd_660_);
lean_dec(v_headApp_641_);
lean_dec_ref(v_arg_640_);
v_a_712_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_667_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_667_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_712_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
}
v___jp_651_:
{
size_t v___x_653_; size_t v___x_654_; 
v___x_653_ = ((size_t)1ULL);
v___x_654_ = lean_usize_add(v_i_644_, v___x_653_);
v_i_644_ = v___x_654_;
v_b_645_ = v_a_652_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___boxed(lean_object* v_forwarded_721_, lean_object* v_arg_722_, lean_object* v_headApp_723_, lean_object* v_as_724_, lean_object* v_sz_725_, lean_object* v_i_726_, lean_object* v_b_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
size_t v_sz_boxed_733_; size_t v_i_boxed_734_; lean_object* v_res_735_; 
v_sz_boxed_733_ = lean_unbox_usize(v_sz_725_);
lean_dec(v_sz_725_);
v_i_boxed_734_ = lean_unbox_usize(v_i_726_);
lean_dec(v_i_726_);
v_res_735_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2(v_forwarded_721_, v_arg_722_, v_headApp_723_, v_as_724_, v_sz_boxed_733_, v_i_boxed_734_, v_b_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec_ref(v_as_724_);
lean_dec_ref(v_forwarded_721_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2(lean_object* v_forwarded_736_, lean_object* v_arg_737_, lean_object* v_headApp_738_, lean_object* v_as_739_, size_t v_sz_740_, size_t v_i_741_, lean_object* v_b_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v_a_749_; uint8_t v___x_753_; 
v___x_753_ = lean_usize_dec_lt(v_i_741_, v_sz_740_);
if (v___x_753_ == 0)
{
lean_object* v___x_754_; 
lean_dec(v_headApp_738_);
lean_dec_ref(v_arg_737_);
v___x_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_754_, 0, v_b_742_);
return v___x_754_;
}
else
{
lean_object* v_a_755_; lean_object* v_fst_756_; lean_object* v_snd_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_817_; 
v_a_755_ = lean_array_uget(v_as_739_, v_i_741_);
v_fst_756_ = lean_ctor_get(v_a_755_, 0);
v_snd_757_ = lean_ctor_get(v_a_755_, 1);
v_isSharedCheck_817_ = !lean_is_exclusive(v_a_755_);
if (v_isSharedCheck_817_ == 0)
{
v___x_759_ = v_a_755_;
v_isShared_760_ = v_isSharedCheck_817_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_snd_757_);
lean_inc(v_fst_756_);
lean_dec(v_a_755_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_817_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___f_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
lean_inc_ref(v_arg_737_);
v___f_761_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_761_, 0, v_arg_737_);
v___x_762_ = lean_box(0);
v___x_763_ = l_Lean_Expr_fvarId_x21(v_fst_756_);
lean_dec(v_fst_756_);
v___x_764_ = l_Lean_FVarId_getDecl___redArg(v___x_763_, v___y_743_, v___y_745_, v___y_746_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; uint8_t v___x_766_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_a_765_);
lean_dec_ref_known(v___x_764_, 1);
v___x_766_ = l_Lean_LocalDecl_binderInfo(v_a_765_);
lean_dec(v_a_765_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_snd_757_, v___y_744_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; uint8_t v___x_769_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_a_768_);
lean_dec_ref_known(v___x_767_, 1);
v___x_769_ = lean_expr_eqv(v_a_768_, v_forwarded_736_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; 
lean_inc(v___y_746_);
lean_inc_ref(v___y_745_);
lean_inc(v___y_744_);
lean_inc_ref(v___y_743_);
v___x_770_ = lean_infer_type(v_a_768_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_772_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc_n(v_a_771_, 2);
lean_dec_ref_known(v___x_770_, 1);
v___x_772_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_a_771_, v___y_744_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_a_773_);
lean_dec_ref_known(v___x_772_, 1);
v___x_774_ = lean_box(0);
v___x_775_ = l_Lean_FindMVar_main(v___f_761_, v_a_773_, v___x_774_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_dec(v_a_771_);
lean_del_object(v___x_759_);
v_a_749_ = v___x_762_;
goto v___jp_748_;
}
else
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_779_; 
lean_dec_ref_known(v___x_775_, 1);
v___x_776_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1);
v___x_777_ = l_Lean_MessageData_ofExpr(v_a_771_);
if (v_isShared_760_ == 0)
{
lean_ctor_set_tag(v___x_759_, 7);
lean_ctor_set(v___x_759_, 1, v___x_777_);
lean_ctor_set(v___x_759_, 0, v___x_776_);
v___x_779_ = v___x_759_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v___x_777_);
v___x_779_ = v_reuseFailAlloc_784_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_780_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1);
v___x_781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_779_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
lean_inc(v_headApp_738_);
v___x_782_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint(v_headApp_738_, v___x_781_);
v___x_783_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v___x_782_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_dec_ref_known(v___x_783_, 1);
v_a_749_ = v___x_762_;
goto v___jp_748_;
}
else
{
lean_dec(v_headApp_738_);
lean_dec_ref(v_arg_737_);
return v___x_783_;
}
}
}
}
else
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
lean_dec(v_a_771_);
lean_dec_ref(v___f_761_);
lean_del_object(v___x_759_);
lean_dec(v_headApp_738_);
lean_dec_ref(v_arg_737_);
v_a_785_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_772_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_772_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
else
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_800_; 
lean_dec_ref(v___f_761_);
lean_del_object(v___x_759_);
lean_dec(v_headApp_738_);
lean_dec_ref(v_arg_737_);
v_a_793_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_800_ == 0)
{
v___x_795_ = v___x_770_;
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_770_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_a_793_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
else
{
lean_dec(v_a_768_);
lean_dec_ref(v___f_761_);
lean_del_object(v___x_759_);
v_a_749_ = v___x_762_;
goto v___jp_748_;
}
}
else
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_808_; 
lean_dec_ref(v___f_761_);
lean_del_object(v___x_759_);
lean_dec(v_headApp_738_);
lean_dec_ref(v_arg_737_);
v_a_801_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_808_ == 0)
{
v___x_803_ = v___x_767_;
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_767_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_a_801_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
else
{
lean_dec_ref(v___f_761_);
lean_del_object(v___x_759_);
lean_dec(v_snd_757_);
v_a_749_ = v___x_762_;
goto v___jp_748_;
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec_ref(v___f_761_);
lean_del_object(v___x_759_);
lean_dec(v_snd_757_);
lean_dec(v_headApp_738_);
lean_dec_ref(v_arg_737_);
v_a_809_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_764_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_764_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
}
v___jp_748_:
{
size_t v___x_750_; size_t v___x_751_; lean_object* v___x_752_; 
v___x_750_ = ((size_t)1ULL);
v___x_751_ = lean_usize_add(v_i_741_, v___x_750_);
v___x_752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2(v_forwarded_736_, v_arg_737_, v_headApp_738_, v_as_739_, v_sz_740_, v___x_751_, v_a_749_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
return v___x_752_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___boxed(lean_object* v_forwarded_818_, lean_object* v_arg_819_, lean_object* v_headApp_820_, lean_object* v_as_821_, lean_object* v_sz_822_, lean_object* v_i_823_, lean_object* v_b_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
size_t v_sz_boxed_830_; size_t v_i_boxed_831_; lean_object* v_res_832_; 
v_sz_boxed_830_ = lean_unbox_usize(v_sz_822_);
lean_dec(v_sz_822_);
v_i_boxed_831_ = lean_unbox_usize(v_i_823_);
lean_dec(v_i_823_);
v_res_832_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2(v_forwarded_818_, v_arg_819_, v_headApp_820_, v_as_821_, v_sz_boxed_830_, v_i_boxed_831_, v_b_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec_ref(v_as_821_);
lean_dec_ref(v_forwarded_818_);
return v_res_832_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___closed__0(void){
_start:
{
lean_object* v___x_833_; lean_object* v_dummy_834_; 
v___x_833_ = lean_box(0);
v_dummy_834_ = l_Lean_Expr_sort___override(v___x_833_);
return v_dummy_834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2(lean_object* v_probeExpr_835_, lean_object* v_forwarded_836_, lean_object* v_arg_837_, lean_object* v_headApp_838_, lean_object* v_fvars_839_, lean_object* v_x_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_dummy_846_; lean_object* v_nargs_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; size_t v_sz_854_; size_t v___x_855_; lean_object* v___x_856_; 
v_dummy_846_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___closed__0, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___closed__0_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___closed__0);
v_nargs_847_ = l_Lean_Expr_getAppNumArgs(v_probeExpr_835_);
lean_inc(v_nargs_847_);
v___x_848_ = lean_mk_array(v_nargs_847_, v_dummy_846_);
v___x_849_ = lean_unsigned_to_nat(1u);
v___x_850_ = lean_nat_sub(v_nargs_847_, v___x_849_);
lean_dec(v_nargs_847_);
v___x_851_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_probeExpr_835_, v___x_848_, v___x_850_);
v___x_852_ = l_Array_zip___redArg(v_fvars_839_, v___x_851_);
lean_dec_ref(v___x_851_);
v___x_853_ = lean_box(0);
v_sz_854_ = lean_array_size(v___x_852_);
v___x_855_ = ((size_t)0ULL);
v___x_856_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2(v_forwarded_836_, v_arg_837_, v_headApp_838_, v___x_852_, v_sz_854_, v___x_855_, v___x_853_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
lean_dec_ref(v___x_852_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_863_ == 0)
{
lean_object* v_unused_864_; 
v_unused_864_ = lean_ctor_get(v___x_856_, 0);
lean_dec(v_unused_864_);
v___x_858_ = v___x_856_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_dec(v___x_856_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_853_);
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_853_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
else
{
return v___x_856_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___boxed(lean_object* v_probeExpr_865_, lean_object* v_forwarded_866_, lean_object* v_arg_867_, lean_object* v_headApp_868_, lean_object* v_fvars_869_, lean_object* v_x_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2(v_probeExpr_865_, v_forwarded_866_, v_arg_867_, v_headApp_868_, v_fvars_869_, v_x_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec_ref(v_x_870_);
lean_dec_ref(v_fvars_869_);
lean_dec_ref(v_forwarded_866_);
return v_res_876_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__1(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__0));
v___x_879_ = l_Lean_stringToMessageData(v___x_878_);
return v___x_879_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__3(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__2));
v___x_882_ = l_Lean_stringToMessageData(v___x_881_);
return v___x_882_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__5(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__4));
v___x_885_ = l_Lean_stringToMessageData(v___x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder(lean_object* v_headApp_886_, lean_object* v_forwarded_887_, lean_object* v_probeExpr_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
lean_object* v_reject_894_; lean_object* v___x_895_; 
lean_inc(v_headApp_886_);
v_reject_894_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0___boxed), 8, 1);
lean_closure_set(v_reject_894_, 0, v_headApp_886_);
lean_inc(v_a_892_);
lean_inc_ref(v_a_891_);
lean_inc(v_a_890_);
lean_inc_ref(v_a_889_);
lean_inc_ref(v_probeExpr_888_);
v___x_895_ = lean_infer_type(v_probeExpr_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v_a_896_; lean_object* v___x_897_; lean_object* v_a_898_; lean_object* v___x_899_; 
v_a_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_a_896_);
lean_dec_ref_known(v___x_895_, 1);
v___x_897_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_a_896_, v_a_890_);
v_a_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_a_898_);
lean_dec_ref(v___x_897_);
v___x_899_ = l_Lean_Meta_whnfD(v_a_898_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref_known(v___x_899_, 1);
if (lean_obj_tag(v_a_900_) == 5)
{
lean_object* v_arg_901_; lean_object* v___f_902_; lean_object* v___f_903_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; uint8_t v___x_933_; 
v_arg_901_ = lean_ctor_get(v_a_900_, 1);
lean_inc_ref_n(v_arg_901_, 3);
lean_inc_n(v_headApp_886_, 2);
v___f_902_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___boxed), 11, 4);
lean_closure_set(v___f_902_, 0, v_arg_901_);
lean_closure_set(v___f_902_, 1, v_headApp_886_);
lean_closure_set(v___f_902_, 2, v_a_900_);
lean_closure_set(v___f_902_, 3, v_reject_894_);
lean_inc_ref(v_forwarded_887_);
lean_inc_ref(v_probeExpr_888_);
v___f_903_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___boxed), 11, 4);
lean_closure_set(v___f_903_, 0, v_probeExpr_888_);
lean_closure_set(v___f_903_, 1, v_forwarded_887_);
lean_closure_set(v___f_903_, 2, v_arg_901_);
lean_closure_set(v___f_903_, 3, v_headApp_886_);
v___x_933_ = l_Lean_Expr_isMVar(v_arg_901_);
lean_dec_ref(v_arg_901_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; lean_object* v___x_935_; 
lean_dec_ref(v___f_903_);
lean_dec_ref(v___f_902_);
lean_dec_ref(v_probeExpr_888_);
lean_dec_ref(v_forwarded_887_);
v___x_934_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__1);
v___x_935_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0(v_headApp_886_, lean_box(0), v___x_934_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
return v___x_935_;
}
else
{
lean_dec(v_headApp_886_);
v___y_905_ = v_a_889_;
v___y_906_ = v_a_890_;
v___y_907_ = v_a_891_;
v___y_908_ = v_a_892_;
goto v___jp_904_;
}
v___jp_904_:
{
lean_object* v___x_909_; 
lean_inc(v___y_908_);
lean_inc_ref(v___y_907_);
lean_inc(v___y_906_);
lean_inc_ref(v___y_905_);
v___x_909_ = lean_infer_type(v_forwarded_887_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; uint8_t v___x_911_; lean_object* v___x_912_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_910_);
lean_dec_ref_known(v___x_909_, 1);
v___x_911_ = 0;
v___x_912_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg(v_a_910_, v___f_902_, v___x_911_, v___x_911_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v___x_913_; lean_object* v___x_914_; 
lean_dec_ref_known(v___x_912_, 1);
v___x_913_ = l_Lean_Expr_getAppFn(v_probeExpr_888_);
lean_dec_ref(v_probeExpr_888_);
lean_inc(v___y_908_);
lean_inc_ref(v___y_907_);
lean_inc(v___y_906_);
lean_inc_ref(v___y_905_);
v___x_914_ = lean_infer_type(v___x_913_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_916_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_a_915_);
lean_dec_ref_known(v___x_914_, 1);
v___x_916_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg(v_a_915_, v___f_903_, v___x_911_, v___x_911_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
return v___x_916_;
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec_ref(v___f_903_);
v_a_917_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_914_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_914_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
else
{
lean_dec_ref(v___f_903_);
lean_dec_ref(v_probeExpr_888_);
return v___x_912_;
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec_ref(v___f_903_);
lean_dec_ref(v___f_902_);
lean_dec_ref(v_probeExpr_888_);
v_a_925_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_909_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_909_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
}
else
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
lean_dec_ref(v_reject_894_);
lean_dec_ref(v_probeExpr_888_);
lean_dec_ref(v_forwarded_887_);
v___x_936_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__3, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__3);
v___x_937_ = l_Lean_MessageData_ofExpr(v_a_900_);
v___x_938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_936_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
v___x_939_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__5, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__5_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__5);
v___x_940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_938_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v___x_941_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0(v_headApp_886_, lean_box(0), v___x_940_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
return v___x_941_;
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_dec_ref(v_reject_894_);
lean_dec_ref(v_probeExpr_888_);
lean_dec_ref(v_forwarded_887_);
lean_dec(v_headApp_886_);
v_a_942_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_899_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_899_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_dec_ref(v_reject_894_);
lean_dec_ref(v_probeExpr_888_);
lean_dec_ref(v_forwarded_887_);
lean_dec(v_headApp_886_);
v_a_950_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_895_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_895_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___boxed(lean_object* v_headApp_958_, lean_object* v_forwarded_959_, lean_object* v_probeExpr_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder(v_headApp_958_, v_forwarded_959_, v_probeExpr_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0(lean_object* v_00_u03b1_967_, lean_object* v_msg_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v_msg_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___boxed(lean_object* v_00_u03b1_975_, lean_object* v_msg_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0(v_00_u03b1_975_, v_msg_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___redArg(lean_object* v_e_983_, lean_object* v___y_984_){
_start:
{
uint8_t v___x_986_; 
v___x_986_ = l_Lean_Expr_hasMVar(v_e_983_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; 
v___x_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_987_, 0, v_e_983_);
return v___x_987_;
}
else
{
lean_object* v___x_988_; lean_object* v_mctx_989_; lean_object* v___x_990_; lean_object* v_fst_991_; lean_object* v_snd_992_; lean_object* v___x_993_; lean_object* v_cache_994_; lean_object* v_zetaDeltaFVarIds_995_; lean_object* v_postponed_996_; lean_object* v_diag_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1006_; 
v___x_988_ = lean_st_ref_get(v___y_984_);
v_mctx_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc_ref(v_mctx_989_);
lean_dec(v___x_988_);
v___x_990_ = l_Lean_instantiateMVarsCore(v_mctx_989_, v_e_983_);
v_fst_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_fst_991_);
v_snd_992_ = lean_ctor_get(v___x_990_, 1);
lean_inc(v_snd_992_);
lean_dec_ref(v___x_990_);
v___x_993_ = lean_st_ref_take(v___y_984_);
v_cache_994_ = lean_ctor_get(v___x_993_, 1);
v_zetaDeltaFVarIds_995_ = lean_ctor_get(v___x_993_, 2);
v_postponed_996_ = lean_ctor_get(v___x_993_, 3);
v_diag_997_ = lean_ctor_get(v___x_993_, 4);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1006_ == 0)
{
lean_object* v_unused_1007_; 
v_unused_1007_ = lean_ctor_get(v___x_993_, 0);
lean_dec(v_unused_1007_);
v___x_999_ = v___x_993_;
v_isShared_1000_ = v_isSharedCheck_1006_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_diag_997_);
lean_inc(v_postponed_996_);
lean_inc(v_zetaDeltaFVarIds_995_);
lean_inc(v_cache_994_);
lean_dec(v___x_993_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1006_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v_snd_992_);
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_snd_992_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v_cache_994_);
lean_ctor_set(v_reuseFailAlloc_1005_, 2, v_zetaDeltaFVarIds_995_);
lean_ctor_set(v_reuseFailAlloc_1005_, 3, v_postponed_996_);
lean_ctor_set(v_reuseFailAlloc_1005_, 4, v_diag_997_);
v___x_1002_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = lean_st_ref_put(v___y_984_, v___x_1002_);
v___x_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1004_, 0, v_fst_991_);
return v___x_1004_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___redArg___boxed(lean_object* v_e_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___redArg(v_e_1008_, v___y_1009_);
lean_dec(v___y_1009_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1(lean_object* v_e_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___redArg(v_e_1012_, v___y_1016_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___boxed(lean_object* v_e_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1(v_e_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
return v_res_1029_;
}
}
static lean_object* _init_l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__3));
v___x_1039_ = l_String_toRawSubstring_x27(v___x_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0(lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_fst_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_toCold_1059_; lean_object* v_ref_1060_; lean_object* v_quotContext_1061_; lean_object* v_currMacroScope_1062_; uint8_t v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; uint8_t v___x_1075_; lean_object* v___x_1076_; 
v_toCold_1059_ = lean_ctor_get(v___y_1056_, 0);
v_ref_1060_ = lean_ctor_get(v___y_1056_, 2);
v_quotContext_1061_ = lean_ctor_get(v_toCold_1059_, 8);
v_currMacroScope_1062_ = lean_ctor_get(v_toCold_1059_, 9);
v___x_1063_ = 0;
v___x_1064_ = l_Lean_SourceInfo_fromRef(v_ref_1060_, v___x_1063_);
v___x_1065_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__1));
v___x_1066_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__2));
lean_inc_n(v___x_1064_, 3);
v___x_1067_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1064_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
v___x_1068_ = lean_obj_once(&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__4, &l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__4_once, _init_l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__4);
v___x_1069_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__5));
lean_inc(v_currMacroScope_1062_);
lean_inc(v_quotContext_1061_);
v___x_1070_ = l_Lean_addMacroScope(v_quotContext_1061_, v___x_1069_, v_currMacroScope_1062_);
v___x_1071_ = lean_box(0);
v___x_1072_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1064_);
lean_ctor_set(v___x_1072_, 1, v___x_1068_);
lean_ctor_set(v___x_1072_, 2, v___x_1070_);
lean_ctor_set(v___x_1072_, 3, v___x_1071_);
v___x_1073_ = l_Lean_Syntax_node2(v___x_1064_, v___x_1065_, v___x_1067_, v___x_1072_);
v___x_1074_ = lean_box(0);
v___x_1075_ = 1;
lean_inc(v___x_1073_);
v___x_1076_ = l_Lean_Elab_Term_elabTerm(v___x_1073_, v___x_1074_, v___x_1075_, v___x_1075_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v___y_1056_, v___y_1057_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1077_);
lean_dec_ref_known(v___x_1076_, 1);
v___x_1078_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__7));
v___x_1079_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__9));
lean_inc(v___x_1064_);
v___x_1080_ = l_Lean_Syntax_node1(v___x_1064_, v___x_1079_, v___x_1073_);
v___x_1081_ = l_Lean_Syntax_node2(v___x_1064_, v___x_1078_, v_fst_1055_, v___x_1080_);
v___x_1082_ = l_Lean_Elab_Term_elabTerm(v___x_1081_, v___x_1074_, v___x_1075_, v___x_1075_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v___y_1056_, v___y_1057_);
lean_dec_ref(v___y_1056_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1091_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1085_ = v___x_1082_;
v_isShared_1086_ = v_isSharedCheck_1091_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1082_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1091_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1087_; lean_object* v___x_1089_; 
v___x_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1087_, 0, v_a_1077_);
lean_ctor_set(v___x_1087_, 1, v_a_1083_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v___x_1087_);
v___x_1089_ = v___x_1085_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1087_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
lean_dec(v_a_1077_);
v_a_1092_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1082_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1082_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_dec(v___x_1073_);
lean_dec(v___x_1064_);
lean_dec_ref(v___y_1056_);
lean_dec(v_fst_1055_);
v_a_1100_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1076_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1076_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___boxed(lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_fst_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0(v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_fst_1112_, v___y_1113_, v___y_1114_);
lean_dec(v___y_1114_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
lean_dec(v_a_1109_);
lean_dec_ref(v_a_1108_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__1(lean_object* v_body_1117_, lean_object* v_cont_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
uint8_t v___x_1127_; lean_object* v___x_1128_; 
v___x_1127_ = 1;
v___x_1128_ = l_Lean_Elab_Do_elabDoSeq(v_body_1117_, v_cont_1118_, v___x_1127_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__1___boxed(lean_object* v_body_1129_, lean_object* v_cont_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__1(v_body_1129_, v_cont_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec_ref(v___y_1131_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__2(lean_object* v_a_1140_, lean_object* v___f_1141_, lean_object* v_a_1142_, lean_object* v_bsExpr_1143_, lean_object* v_x_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = l_Lean_Elab_Do_EffectForwarder_lift(v_a_1140_, v___f_1141_, v_a_1142_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v_a_1153_; uint8_t v___x_1154_; uint8_t v___x_1155_; uint8_t v___x_1156_; lean_object* v___x_1157_; 
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
lean_inc(v_a_1153_);
lean_dec_ref_known(v___x_1152_, 1);
v___x_1154_ = 0;
v___x_1155_ = 1;
v___x_1156_ = 1;
v___x_1157_ = l_Lean_Meta_mkLambdaFVars(v_bsExpr_1143_, v_a_1153_, v___x_1154_, v___x_1155_, v___x_1154_, v___x_1155_, v___x_1156_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
return v___x_1157_;
}
else
{
return v___x_1152_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__2___boxed(lean_object* v_a_1158_, lean_object* v___f_1159_, lean_object* v_a_1160_, lean_object* v_bsExpr_1161_, lean_object* v_x_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__2(v_a_1158_, v___f_1159_, v_a_1160_, v_bsExpr_1161_, v_x_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v_x_1162_);
lean_dec_ref(v_bsExpr_1161_);
lean_dec_ref(v_a_1160_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__3(lean_object* v_a_1171_, lean_object* v_fst_1172_, lean_object* v___f_1173_, lean_object* v_____r_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1182_, 0, v_a_1171_);
v___x_1183_ = l_Lean_Elab_Term_elabFunBinders___redArg(v_fst_1172_, v___x_1182_, v___f_1173_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__3___boxed(lean_object* v_a_1184_, lean_object* v_fst_1185_, lean_object* v___f_1186_, lean_object* v_____r_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__3(v_a_1184_, v_fst_1185_, v___f_1186_, v_____r_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec_ref(v_fst_1185_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0___redArg(lean_object* v_msg_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v_ref_1202_; lean_object* v___x_1203_; lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1212_; 
v_ref_1202_ = lean_ctor_get(v___y_1199_, 2);
v___x_1203_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0(v_msg_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1206_ = v___x_1203_;
v_isShared_1207_ = v_isSharedCheck_1212_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1203_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1212_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1208_; lean_object* v___x_1210_; 
lean_inc(v_ref_1202_);
v___x_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1208_, 0, v_ref_1202_);
lean_ctor_set(v___x_1208_, 1, v_a_1204_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set_tag(v___x_1206_, 1);
lean_ctor_set(v___x_1206_, 0, v___x_1208_);
v___x_1210_ = v___x_1206_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1208_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0___redArg___boxed(lean_object* v_msg_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0___redArg(v_msg_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__2(size_t v_sz_1220_, size_t v_i_1221_, lean_object* v_bs_1222_){
_start:
{
uint8_t v___x_1223_; 
v___x_1223_ = lean_usize_dec_lt(v_i_1221_, v_sz_1220_);
if (v___x_1223_ == 0)
{
return v_bs_1222_;
}
else
{
lean_object* v_v_1224_; lean_object* v___x_1225_; lean_object* v_bs_x27_1226_; size_t v___x_1227_; size_t v___x_1228_; lean_object* v___x_1229_; 
v_v_1224_ = lean_array_uget(v_bs_1222_, v_i_1221_);
v___x_1225_ = lean_unsigned_to_nat(0u);
v_bs_x27_1226_ = lean_array_uset(v_bs_1222_, v_i_1221_, v___x_1225_);
v___x_1227_ = ((size_t)1ULL);
v___x_1228_ = lean_usize_add(v_i_1221_, v___x_1227_);
v___x_1229_ = lean_array_uset(v_bs_x27_1226_, v_i_1221_, v_v_1224_);
v_i_1221_ = v___x_1228_;
v_bs_1222_ = v___x_1229_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__2___boxed(lean_object* v_sz_1231_, lean_object* v_i_1232_, lean_object* v_bs_1233_){
_start:
{
size_t v_sz_boxed_1234_; size_t v_i_boxed_1235_; lean_object* v_res_1236_; 
v_sz_boxed_1234_ = lean_unbox_usize(v_sz_1231_);
lean_dec(v_sz_1231_);
v_i_boxed_1235_ = lean_unbox_usize(v_i_1232_);
lean_dec(v_i_1232_);
v_res_1236_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__2(v_sz_boxed_1234_, v_i_boxed_1235_, v_bs_1233_);
return v_res_1236_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16___redArg(lean_object* v_keys_1237_, lean_object* v_i_1238_, lean_object* v_k_1239_){
_start:
{
lean_object* v___x_1240_; uint8_t v___x_1241_; 
v___x_1240_ = lean_array_get_size(v_keys_1237_);
v___x_1241_ = lean_nat_dec_lt(v_i_1238_, v___x_1240_);
if (v___x_1241_ == 0)
{
lean_dec(v_i_1238_);
return v___x_1241_;
}
else
{
lean_object* v_k_x27_1242_; uint8_t v___x_1243_; 
v_k_x27_1242_ = lean_array_fget_borrowed(v_keys_1237_, v_i_1238_);
v___x_1243_ = l_Lean_instBEqExtraModUse_beq(v_k_1239_, v_k_x27_1242_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = lean_unsigned_to_nat(1u);
v___x_1245_ = lean_nat_add(v_i_1238_, v___x_1244_);
lean_dec(v_i_1238_);
v_i_1238_ = v___x_1245_;
goto _start;
}
else
{
lean_dec(v_i_1238_);
return v___x_1241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16___redArg___boxed(lean_object* v_keys_1247_, lean_object* v_i_1248_, lean_object* v_k_1249_){
_start:
{
uint8_t v_res_1250_; lean_object* v_r_1251_; 
v_res_1250_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16___redArg(v_keys_1247_, v_i_1248_, v_k_1249_);
lean_dec_ref(v_k_1249_);
lean_dec_ref(v_keys_1247_);
v_r_1251_ = lean_box(v_res_1250_);
return v_r_1251_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13___redArg(lean_object* v_x_1252_, size_t v_x_1253_, lean_object* v_x_1254_){
_start:
{
if (lean_obj_tag(v_x_1252_) == 0)
{
lean_object* v_es_1255_; lean_object* v___x_1256_; size_t v___x_1257_; size_t v___x_1258_; lean_object* v_j_1259_; lean_object* v___x_1260_; 
v_es_1255_ = lean_ctor_get(v_x_1252_, 0);
v___x_1256_ = lean_box(2);
v___x_1257_ = ((size_t)31ULL);
v___x_1258_ = lean_usize_land(v_x_1253_, v___x_1257_);
v_j_1259_ = lean_usize_to_nat(v___x_1258_);
v___x_1260_ = lean_array_get_borrowed(v___x_1256_, v_es_1255_, v_j_1259_);
lean_dec(v_j_1259_);
switch(lean_obj_tag(v___x_1260_))
{
case 0:
{
lean_object* v_key_1261_; uint8_t v___x_1262_; 
v_key_1261_ = lean_ctor_get(v___x_1260_, 0);
v___x_1262_ = l_Lean_instBEqExtraModUse_beq(v_x_1254_, v_key_1261_);
return v___x_1262_;
}
case 1:
{
lean_object* v_node_1263_; size_t v___x_1264_; size_t v___x_1265_; 
v_node_1263_ = lean_ctor_get(v___x_1260_, 0);
v___x_1264_ = ((size_t)5ULL);
v___x_1265_ = lean_usize_shift_right(v_x_1253_, v___x_1264_);
v_x_1252_ = v_node_1263_;
v_x_1253_ = v___x_1265_;
goto _start;
}
default: 
{
uint8_t v___x_1267_; 
v___x_1267_ = 0;
return v___x_1267_;
}
}
}
else
{
lean_object* v_ks_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v_ks_1268_ = lean_ctor_get(v_x_1252_, 0);
v___x_1269_ = lean_unsigned_to_nat(0u);
v___x_1270_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16___redArg(v_ks_1268_, v___x_1269_, v_x_1254_);
return v___x_1270_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13___redArg___boxed(lean_object* v_x_1271_, lean_object* v_x_1272_, lean_object* v_x_1273_){
_start:
{
size_t v_x_28318__boxed_1274_; uint8_t v_res_1275_; lean_object* v_r_1276_; 
v_x_28318__boxed_1274_ = lean_unbox_usize(v_x_1272_);
lean_dec(v_x_1272_);
v_res_1275_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13___redArg(v_x_1271_, v_x_28318__boxed_1274_, v_x_1273_);
lean_dec_ref(v_x_1273_);
lean_dec_ref(v_x_1271_);
v_r_1276_ = lean_box(v_res_1275_);
return v_r_1276_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9___redArg(lean_object* v_x_1277_, lean_object* v_x_1278_){
_start:
{
uint64_t v___x_1279_; size_t v___x_1280_; uint8_t v___x_1281_; 
v___x_1279_ = l_Lean_instHashableExtraModUse_hash(v_x_1278_);
v___x_1280_ = lean_uint64_to_usize(v___x_1279_);
v___x_1281_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13___redArg(v_x_1277_, v___x_1280_, v_x_1278_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9___redArg___boxed(lean_object* v_x_1282_, lean_object* v_x_1283_){
_start:
{
uint8_t v_res_1284_; lean_object* v_r_1285_; 
v_res_1284_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9___redArg(v_x_1282_, v_x_1283_);
lean_dec_ref(v_x_1283_);
lean_dec_ref(v_x_1282_);
v_r_1285_ = lean_box(v_res_1284_);
return v_r_1285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___lam__0(lean_object* v___x_1286_, lean_object* v_entry_1287_, lean_object* v_s_1288_){
_start:
{
lean_object* v_addEntryFn_1289_; lean_object* v_importedEntries_1290_; lean_object* v_state_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1299_; 
v_addEntryFn_1289_ = lean_ctor_get(v___x_1286_, 3);
lean_inc(v_addEntryFn_1289_);
lean_dec_ref(v___x_1286_);
v_importedEntries_1290_ = lean_ctor_get(v_s_1288_, 0);
v_state_1291_ = lean_ctor_get(v_s_1288_, 1);
v_isSharedCheck_1299_ = !lean_is_exclusive(v_s_1288_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1293_ = v_s_1288_;
v_isShared_1294_ = v_isSharedCheck_1299_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_state_1291_);
lean_inc(v_importedEntries_1290_);
lean_dec(v_s_1288_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1299_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v_state_1295_; lean_object* v___x_1297_; 
v_state_1295_ = lean_apply_2(v_addEntryFn_1289_, v_state_1291_, v_entry_1287_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 1, v_state_1295_);
v___x_1297_ = v___x_1293_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_importedEntries_1290_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v_state_1295_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1300_; double v___x_1301_; 
v___x_1300_ = lean_unsigned_to_nat(0u);
v___x_1301_ = lean_float_of_nat(v___x_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg(lean_object* v_cls_1305_, lean_object* v_msg_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v_ref_1312_; lean_object* v___x_1313_; lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1359_; 
v_ref_1312_ = lean_ctor_get(v___y_1309_, 2);
v___x_1313_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0(v_msg_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1316_ = v___x_1313_;
v_isShared_1317_ = v_isSharedCheck_1359_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1313_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1359_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1318_; lean_object* v_traceState_1319_; lean_object* v_env_1320_; lean_object* v_nextMacroScope_1321_; lean_object* v_ngen_1322_; lean_object* v_auxDeclNGen_1323_; lean_object* v_cache_1324_; lean_object* v_recordedDeps_1325_; lean_object* v_messages_1326_; lean_object* v_infoState_1327_; lean_object* v_snapshotTasks_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1358_; 
v___x_1318_ = lean_st_ref_take(v___y_1310_);
v_traceState_1319_ = lean_ctor_get(v___x_1318_, 4);
v_env_1320_ = lean_ctor_get(v___x_1318_, 0);
v_nextMacroScope_1321_ = lean_ctor_get(v___x_1318_, 1);
v_ngen_1322_ = lean_ctor_get(v___x_1318_, 2);
v_auxDeclNGen_1323_ = lean_ctor_get(v___x_1318_, 3);
v_cache_1324_ = lean_ctor_get(v___x_1318_, 5);
v_recordedDeps_1325_ = lean_ctor_get(v___x_1318_, 6);
v_messages_1326_ = lean_ctor_get(v___x_1318_, 7);
v_infoState_1327_ = lean_ctor_get(v___x_1318_, 8);
v_snapshotTasks_1328_ = lean_ctor_get(v___x_1318_, 9);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1330_ = v___x_1318_;
v_isShared_1331_ = v_isSharedCheck_1358_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_snapshotTasks_1328_);
lean_inc(v_infoState_1327_);
lean_inc(v_messages_1326_);
lean_inc(v_recordedDeps_1325_);
lean_inc(v_cache_1324_);
lean_inc(v_traceState_1319_);
lean_inc(v_auxDeclNGen_1323_);
lean_inc(v_ngen_1322_);
lean_inc(v_nextMacroScope_1321_);
lean_inc(v_env_1320_);
lean_dec(v___x_1318_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1358_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
uint64_t v_tid_1332_; lean_object* v_traces_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1357_; 
v_tid_1332_ = lean_ctor_get_uint64(v_traceState_1319_, sizeof(void*)*1);
v_traces_1333_ = lean_ctor_get(v_traceState_1319_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v_traceState_1319_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1335_ = v_traceState_1319_;
v_isShared_1336_ = v_isSharedCheck_1357_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_traces_1333_);
lean_dec(v_traceState_1319_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1357_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; double v___x_1339_; uint8_t v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1337_ = lean_box(0);
v___x_1338_ = lean_box(0);
v___x_1339_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___closed__0);
v___x_1340_ = 0;
v___x_1341_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___closed__1));
v___x_1342_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1342_, 0, v_cls_1305_);
lean_ctor_set(v___x_1342_, 1, v___x_1338_);
lean_ctor_set(v___x_1342_, 2, v___x_1341_);
lean_ctor_set_float(v___x_1342_, sizeof(void*)*3, v___x_1339_);
lean_ctor_set_float(v___x_1342_, sizeof(void*)*3 + 8, v___x_1339_);
lean_ctor_set_uint8(v___x_1342_, sizeof(void*)*3 + 16, v___x_1340_);
v___x_1343_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___closed__2));
v___x_1344_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1342_);
lean_ctor_set(v___x_1344_, 1, v_a_1314_);
lean_ctor_set(v___x_1344_, 2, v___x_1343_);
lean_inc(v_ref_1312_);
v___x_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1345_, 0, v_ref_1312_);
lean_ctor_set(v___x_1345_, 1, v___x_1344_);
v___x_1346_ = l_Lean_PersistentArray_push___redArg(v_traces_1333_, v___x_1345_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v___x_1346_);
v___x_1348_ = v___x_1335_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1346_);
lean_ctor_set_uint64(v_reuseFailAlloc_1356_, sizeof(void*)*1, v_tid_1332_);
v___x_1348_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v___x_1350_; 
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 4, v___x_1348_);
v___x_1350_ = v___x_1330_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_env_1320_);
lean_ctor_set(v_reuseFailAlloc_1355_, 1, v_nextMacroScope_1321_);
lean_ctor_set(v_reuseFailAlloc_1355_, 2, v_ngen_1322_);
lean_ctor_set(v_reuseFailAlloc_1355_, 3, v_auxDeclNGen_1323_);
lean_ctor_set(v_reuseFailAlloc_1355_, 4, v___x_1348_);
lean_ctor_set(v_reuseFailAlloc_1355_, 5, v_cache_1324_);
lean_ctor_set(v_reuseFailAlloc_1355_, 6, v_recordedDeps_1325_);
lean_ctor_set(v_reuseFailAlloc_1355_, 7, v_messages_1326_);
lean_ctor_set(v_reuseFailAlloc_1355_, 8, v_infoState_1327_);
lean_ctor_set(v_reuseFailAlloc_1355_, 9, v_snapshotTasks_1328_);
v___x_1350_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1351_ = lean_st_ref_put(v___y_1310_, v___x_1350_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 0, v___x_1337_);
v___x_1353_ = v___x_1316_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1337_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___boxed(lean_object* v_cls_1360_, lean_object* v_msg_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg(v_cls_1360_, v_msg_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
return v_res_1367_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__0(void){
_start:
{
lean_object* v___x_1368_; 
v___x_1368_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1368_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__1(void){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__0);
v___x_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1369_);
return v___x_1370_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__2(void){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__1);
v___x_1372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
lean_ctor_set(v___x_1372_, 1, v___x_1371_);
return v___x_1372_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__3(void){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__1);
v___x_1374_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1373_);
lean_ctor_set(v___x_1374_, 1, v___x_1373_);
lean_ctor_set(v___x_1374_, 2, v___x_1373_);
lean_ctor_set(v___x_1374_, 3, v___x_1373_);
lean_ctor_set(v___x_1374_, 4, v___x_1373_);
lean_ctor_set(v___x_1374_, 5, v___x_1373_);
return v___x_1374_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__4(void){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1375_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__8(void){
_start:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1380_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__7));
v___x_1381_ = l_Lean_stringToMessageData(v___x_1380_);
return v___x_1381_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__10(void){
_start:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1383_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__9));
v___x_1384_ = l_Lean_stringToMessageData(v___x_1383_);
return v___x_1384_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__11(void){
_start:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___closed__1));
v___x_1386_ = l_Lean_stringToMessageData(v___x_1385_);
return v___x_1386_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__14(void){
_start:
{
lean_object* v_cls_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v_cls_1390_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__6));
v___x_1391_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__13));
v___x_1392_ = l_Lean_Name_append(v___x_1391_, v_cls_1390_);
return v___x_1392_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__16(void){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1394_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__15));
v___x_1395_ = l_Lean_stringToMessageData(v___x_1394_);
return v___x_1395_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__18(void){
_start:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1397_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__17));
v___x_1398_ = l_Lean_stringToMessageData(v___x_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6(lean_object* v_mod_1403_, uint8_t v_isMeta_1404_, lean_object* v_hint_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v_env_1447_; uint8_t v_isExporting_1448_; lean_object* v_entry_1449_; lean_object* v___x_1450_; lean_object* v_env_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; uint8_t v___x_1456_; 
v___x_1445_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__4);
v___x_1446_ = lean_st_ref_get(v___y_1411_);
v_env_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc_ref(v_env_1447_);
lean_dec(v___x_1446_);
v_isExporting_1448_ = lean_ctor_get_uint8(v_env_1447_, sizeof(void*)*13);
lean_dec_ref(v_env_1447_);
lean_inc(v_mod_1403_);
v_entry_1449_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1449_, 0, v_mod_1403_);
lean_ctor_set_uint8(v_entry_1449_, sizeof(void*)*1, v_isExporting_1448_);
lean_ctor_set_uint8(v_entry_1449_, sizeof(void*)*1 + 1, v_isMeta_1404_);
v___x_1450_ = lean_st_ref_get(v___y_1411_);
v_env_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc_ref(v_env_1451_);
lean_dec(v___x_1450_);
v___x_1452_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1453_ = lean_box(1);
v___x_1454_ = lean_box(0);
v___x_1455_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1445_, v___x_1452_, v_env_1451_, v___x_1453_, v___x_1454_);
v___x_1456_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9___redArg(v___x_1455_, v_entry_1449_);
lean_dec(v___x_1455_);
if (v___x_1456_ == 0)
{
lean_object* v_toCold_1457_; lean_object* v_options_1458_; lean_object* v_inheritedTraceOptions_1459_; uint8_t v_hasTrace_1460_; lean_object* v___f_1461_; uint8_t v___x_1462_; lean_object* v___y_1464_; lean_object* v___y_1465_; 
v_toCold_1457_ = lean_ctor_get(v___y_1410_, 0);
v_options_1458_ = lean_ctor_get(v_toCold_1457_, 2);
v_inheritedTraceOptions_1459_ = lean_ctor_get(v_toCold_1457_, 11);
v_hasTrace_1460_ = lean_ctor_get_uint8(v_options_1458_, sizeof(void*)*1);
v___f_1461_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___lam__0), 3, 2);
lean_closure_set(v___f_1461_, 0, v___x_1452_);
lean_closure_set(v___f_1461_, 1, v_entry_1449_);
v___x_1462_ = 1;
if (v_hasTrace_1460_ == 0)
{
lean_dec(v_hint_1405_);
lean_dec(v_mod_1403_);
v___y_1464_ = v___y_1409_;
v___y_1465_ = v___y_1411_;
goto v___jp_1463_;
}
else
{
lean_object* v_cls_1492_; lean_object* v___y_1494_; lean_object* v___y_1495_; lean_object* v___y_1499_; lean_object* v___y_1500_; lean_object* v___x_1512_; uint8_t v___x_1513_; 
v_cls_1492_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__6));
v___x_1512_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__14);
v___x_1513_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1459_, v_options_1458_, v___x_1512_);
if (v___x_1513_ == 0)
{
lean_dec(v_hint_1405_);
lean_dec(v_mod_1403_);
v___y_1464_ = v___y_1409_;
v___y_1465_ = v___y_1411_;
goto v___jp_1463_;
}
else
{
lean_object* v___x_1514_; lean_object* v___y_1516_; 
v___x_1514_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__16);
if (v_isExporting_1448_ == 0)
{
lean_object* v___x_1523_; 
v___x_1523_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__21));
v___y_1516_ = v___x_1523_;
goto v___jp_1515_;
}
else
{
lean_object* v___x_1524_; 
v___x_1524_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__22));
v___y_1516_ = v___x_1524_;
goto v___jp_1515_;
}
v___jp_1515_:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
lean_inc_ref(v___y_1516_);
v___x_1517_ = l_Lean_stringToMessageData(v___y_1516_);
v___x_1518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1514_);
lean_ctor_set(v___x_1518_, 1, v___x_1517_);
v___x_1519_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__18);
v___x_1520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1518_);
lean_ctor_set(v___x_1520_, 1, v___x_1519_);
if (v_isMeta_1404_ == 0)
{
lean_object* v___x_1521_; 
v___x_1521_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__19));
v___y_1499_ = v___x_1520_;
v___y_1500_ = v___x_1521_;
goto v___jp_1498_;
}
else
{
lean_object* v___x_1522_; 
v___x_1522_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__20));
v___y_1499_ = v___x_1520_;
v___y_1500_ = v___x_1522_;
goto v___jp_1498_;
}
}
}
v___jp_1493_:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1496_, 0, v___y_1494_);
lean_ctor_set(v___x_1496_, 1, v___y_1495_);
v___x_1497_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg(v_cls_1492_, v___x_1496_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_dec_ref_known(v___x_1497_, 1);
v___y_1464_ = v___y_1409_;
v___y_1465_ = v___y_1411_;
goto v___jp_1463_;
}
else
{
lean_dec_ref(v___f_1461_);
return v___x_1497_;
}
}
v___jp_1498_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; uint8_t v___x_1507_; 
lean_inc_ref(v___y_1500_);
v___x_1501_ = l_Lean_stringToMessageData(v___y_1500_);
v___x_1502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1502_, 0, v___y_1499_);
lean_ctor_set(v___x_1502_, 1, v___x_1501_);
v___x_1503_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__8);
v___x_1504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1502_);
lean_ctor_set(v___x_1504_, 1, v___x_1503_);
v___x_1505_ = l_Lean_MessageData_ofName(v_mod_1403_);
v___x_1506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1504_);
lean_ctor_set(v___x_1506_, 1, v___x_1505_);
v___x_1507_ = l_Lean_Name_isAnonymous(v_hint_1405_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1508_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__10);
v___x_1509_ = l_Lean_MessageData_ofName(v_hint_1405_);
v___x_1510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1508_);
lean_ctor_set(v___x_1510_, 1, v___x_1509_);
v___y_1494_ = v___x_1506_;
v___y_1495_ = v___x_1510_;
goto v___jp_1493_;
}
else
{
lean_object* v___x_1511_; 
lean_dec(v_hint_1405_);
v___x_1511_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__11);
v___y_1494_ = v___x_1506_;
v___y_1495_ = v___x_1511_;
goto v___jp_1493_;
}
}
}
v___jp_1463_:
{
lean_object* v___x_1466_; lean_object* v_toEnvExtension_1467_; uint8_t v_logWrites_1468_; 
v___x_1466_ = lean_st_ref_take(v___y_1465_);
v_toEnvExtension_1467_ = lean_ctor_get(v___x_1452_, 0);
v_logWrites_1468_ = lean_ctor_get_uint8(v_toEnvExtension_1467_, sizeof(void*)*6);
if (v_logWrites_1468_ == 0)
{
lean_object* v_env_1469_; lean_object* v_nextMacroScope_1470_; lean_object* v_ngen_1471_; lean_object* v_auxDeclNGen_1472_; lean_object* v_traceState_1473_; lean_object* v_recordedDeps_1474_; lean_object* v_messages_1475_; lean_object* v_infoState_1476_; lean_object* v_snapshotTasks_1477_; lean_object* v_asyncMode_1478_; lean_object* v___x_1479_; 
v_env_1469_ = lean_ctor_get(v___x_1466_, 0);
lean_inc_ref(v_env_1469_);
v_nextMacroScope_1470_ = lean_ctor_get(v___x_1466_, 1);
lean_inc(v_nextMacroScope_1470_);
v_ngen_1471_ = lean_ctor_get(v___x_1466_, 2);
lean_inc_ref(v_ngen_1471_);
v_auxDeclNGen_1472_ = lean_ctor_get(v___x_1466_, 3);
lean_inc_ref(v_auxDeclNGen_1472_);
v_traceState_1473_ = lean_ctor_get(v___x_1466_, 4);
lean_inc_ref(v_traceState_1473_);
v_recordedDeps_1474_ = lean_ctor_get(v___x_1466_, 6);
lean_inc_ref(v_recordedDeps_1474_);
v_messages_1475_ = lean_ctor_get(v___x_1466_, 7);
lean_inc_ref(v_messages_1475_);
v_infoState_1476_ = lean_ctor_get(v___x_1466_, 8);
lean_inc_ref(v_infoState_1476_);
v_snapshotTasks_1477_ = lean_ctor_get(v___x_1466_, 9);
lean_inc_ref(v_snapshotTasks_1477_);
lean_dec(v___x_1466_);
v_asyncMode_1478_ = lean_ctor_get(v_toEnvExtension_1467_, 2);
lean_inc_ref(v_toEnvExtension_1467_);
v___x_1479_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1467_, v_env_1469_, v___f_1461_, v_asyncMode_1478_, v___x_1454_, v___x_1462_);
v___y_1414_ = v_auxDeclNGen_1472_;
v___y_1415_ = v_traceState_1473_;
v___y_1416_ = v_nextMacroScope_1470_;
v___y_1417_ = v_infoState_1476_;
v___y_1418_ = v_ngen_1471_;
v___y_1419_ = v_snapshotTasks_1477_;
v___y_1420_ = v___y_1464_;
v___y_1421_ = v_messages_1475_;
v___y_1422_ = v___y_1465_;
v___y_1423_ = v_recordedDeps_1474_;
v___y_1424_ = v___x_1479_;
goto v___jp_1413_;
}
else
{
lean_object* v_env_1480_; lean_object* v_nextMacroScope_1481_; lean_object* v_ngen_1482_; lean_object* v_auxDeclNGen_1483_; lean_object* v_traceState_1484_; lean_object* v_recordedDeps_1485_; lean_object* v_messages_1486_; lean_object* v_infoState_1487_; lean_object* v_snapshotTasks_1488_; lean_object* v_asyncMode_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v_env_1480_ = lean_ctor_get(v___x_1466_, 0);
lean_inc_ref(v_env_1480_);
v_nextMacroScope_1481_ = lean_ctor_get(v___x_1466_, 1);
lean_inc(v_nextMacroScope_1481_);
v_ngen_1482_ = lean_ctor_get(v___x_1466_, 2);
lean_inc_ref(v_ngen_1482_);
v_auxDeclNGen_1483_ = lean_ctor_get(v___x_1466_, 3);
lean_inc_ref(v_auxDeclNGen_1483_);
v_traceState_1484_ = lean_ctor_get(v___x_1466_, 4);
lean_inc_ref(v_traceState_1484_);
v_recordedDeps_1485_ = lean_ctor_get(v___x_1466_, 6);
lean_inc_ref(v_recordedDeps_1485_);
v_messages_1486_ = lean_ctor_get(v___x_1466_, 7);
lean_inc_ref(v_messages_1486_);
v_infoState_1487_ = lean_ctor_get(v___x_1466_, 8);
lean_inc_ref(v_infoState_1487_);
v_snapshotTasks_1488_ = lean_ctor_get(v___x_1466_, 9);
lean_inc_ref(v_snapshotTasks_1488_);
lean_dec(v___x_1466_);
v_asyncMode_1489_ = lean_ctor_get(v_toEnvExtension_1467_, 2);
lean_inc_ref_n(v_toEnvExtension_1467_, 2);
v___x_1490_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1467_, v_env_1480_);
lean_dec_ref(v_env_1480_);
v___x_1491_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1467_, v___x_1490_, v___f_1461_, v_asyncMode_1489_, v___x_1454_, v___x_1462_);
v___y_1414_ = v_auxDeclNGen_1483_;
v___y_1415_ = v_traceState_1484_;
v___y_1416_ = v_nextMacroScope_1481_;
v___y_1417_ = v_infoState_1487_;
v___y_1418_ = v_ngen_1482_;
v___y_1419_ = v_snapshotTasks_1488_;
v___y_1420_ = v___y_1464_;
v___y_1421_ = v_messages_1486_;
v___y_1422_ = v___y_1465_;
v___y_1423_ = v_recordedDeps_1485_;
v___y_1424_ = v___x_1491_;
goto v___jp_1413_;
}
}
}
else
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
lean_dec_ref_known(v_entry_1449_, 1);
lean_dec(v_hint_1405_);
lean_dec(v_mod_1403_);
v___x_1525_ = lean_box(0);
v___x_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
return v___x_1526_;
}
v___jp_1413_:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v_mctx_1429_; lean_object* v_zetaDeltaFVarIds_1430_; lean_object* v_postponed_1431_; lean_object* v_diag_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1443_; 
v___x_1425_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__2);
v___x_1426_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1426_, 0, v___y_1424_);
lean_ctor_set(v___x_1426_, 1, v___y_1416_);
lean_ctor_set(v___x_1426_, 2, v___y_1418_);
lean_ctor_set(v___x_1426_, 3, v___y_1414_);
lean_ctor_set(v___x_1426_, 4, v___y_1415_);
lean_ctor_set(v___x_1426_, 5, v___x_1425_);
lean_ctor_set(v___x_1426_, 6, v___y_1423_);
lean_ctor_set(v___x_1426_, 7, v___y_1421_);
lean_ctor_set(v___x_1426_, 8, v___y_1417_);
lean_ctor_set(v___x_1426_, 9, v___y_1419_);
v___x_1427_ = lean_st_ref_put(v___y_1422_, v___x_1426_);
v___x_1428_ = lean_st_ref_take(v___y_1420_);
v_mctx_1429_ = lean_ctor_get(v___x_1428_, 0);
v_zetaDeltaFVarIds_1430_ = lean_ctor_get(v___x_1428_, 2);
v_postponed_1431_ = lean_ctor_get(v___x_1428_, 3);
v_diag_1432_ = lean_ctor_get(v___x_1428_, 4);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1443_ == 0)
{
lean_object* v_unused_1444_; 
v_unused_1444_ = lean_ctor_get(v___x_1428_, 1);
lean_dec(v_unused_1444_);
v___x_1434_ = v___x_1428_;
v_isShared_1435_ = v_isSharedCheck_1443_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_diag_1432_);
lean_inc(v_postponed_1431_);
lean_inc(v_zetaDeltaFVarIds_1430_);
lean_inc(v_mctx_1429_);
lean_dec(v___x_1428_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1443_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1439_; 
v___x_1436_ = lean_box(0);
v___x_1437_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__3);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 1, v___x_1437_);
v___x_1439_ = v___x_1434_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_mctx_1429_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v___x_1437_);
lean_ctor_set(v_reuseFailAlloc_1442_, 2, v_zetaDeltaFVarIds_1430_);
lean_ctor_set(v_reuseFailAlloc_1442_, 3, v_postponed_1431_);
lean_ctor_set(v_reuseFailAlloc_1442_, 4, v_diag_1432_);
v___x_1439_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1440_ = lean_st_ref_put(v___y_1420_, v___x_1439_);
v___x_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1436_);
return v___x_1441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___boxed(lean_object* v_mod_1527_, lean_object* v_isMeta_1528_, lean_object* v_hint_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
uint8_t v_isMeta_boxed_1537_; lean_object* v_res_1538_; 
v_isMeta_boxed_1537_ = lean_unbox(v_isMeta_1528_);
v_res_1538_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6(v_mod_1527_, v_isMeta_boxed_1537_, v_hint_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__7(lean_object* v___x_1539_, lean_object* v_declName_1540_, lean_object* v_as_1541_, size_t v_sz_1542_, size_t v_i_1543_, lean_object* v_b_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
uint8_t v___x_1552_; 
v___x_1552_ = lean_usize_dec_lt(v_i_1543_, v_sz_1542_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; 
lean_dec(v_declName_1540_);
v___x_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1553_, 0, v_b_1544_);
return v___x_1553_;
}
else
{
lean_object* v___x_1554_; lean_object* v_modules_1555_; lean_object* v___x_1556_; lean_object* v_a_1557_; lean_object* v___x_1558_; lean_object* v_toImport_1559_; lean_object* v_module_1560_; lean_object* v___x_1561_; uint8_t v___x_1562_; lean_object* v___x_1563_; 
v___x_1554_ = l_Lean_Environment_header(v___x_1539_);
v_modules_1555_ = lean_ctor_get(v___x_1554_, 3);
lean_inc_ref(v_modules_1555_);
lean_dec_ref(v___x_1554_);
v___x_1556_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1557_ = lean_array_uget_borrowed(v_as_1541_, v_i_1543_);
v___x_1558_ = lean_array_get(v___x_1556_, v_modules_1555_, v_a_1557_);
lean_dec_ref(v_modules_1555_);
v_toImport_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc_ref(v_toImport_1559_);
lean_dec(v___x_1558_);
v_module_1560_ = lean_ctor_get(v_toImport_1559_, 0);
lean_inc(v_module_1560_);
lean_dec_ref(v_toImport_1559_);
v___x_1561_ = lean_box(0);
v___x_1562_ = 0;
lean_inc(v_declName_1540_);
v___x_1563_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6(v_module_1560_, v___x_1562_, v_declName_1540_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
if (lean_obj_tag(v___x_1563_) == 0)
{
size_t v___x_1564_; size_t v___x_1565_; 
lean_dec_ref_known(v___x_1563_, 1);
v___x_1564_ = ((size_t)1ULL);
v___x_1565_ = lean_usize_add(v_i_1543_, v___x_1564_);
v_i_1543_ = v___x_1565_;
v_b_1544_ = v___x_1561_;
goto _start;
}
else
{
lean_dec(v_declName_1540_);
return v___x_1563_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__7___boxed(lean_object* v___x_1567_, lean_object* v_declName_1568_, lean_object* v_as_1569_, lean_object* v_sz_1570_, lean_object* v_i_1571_, lean_object* v_b_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
size_t v_sz_boxed_1580_; size_t v_i_boxed_1581_; lean_object* v_res_1582_; 
v_sz_boxed_1580_ = lean_unbox_usize(v_sz_1570_);
lean_dec(v_sz_1570_);
v_i_boxed_1581_ = lean_unbox_usize(v_i_1571_);
lean_dec(v_i_1571_);
v_res_1582_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__7(v___x_1567_, v_declName_1568_, v_as_1569_, v_sz_boxed_1580_, v_i_boxed_1581_, v_b_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
lean_dec_ref(v_as_1569_);
lean_dec_ref(v___x_1567_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12___redArg(lean_object* v_a_1583_, lean_object* v_x_1584_){
_start:
{
if (lean_obj_tag(v_x_1584_) == 0)
{
lean_object* v___x_1585_; 
v___x_1585_ = lean_box(0);
return v___x_1585_;
}
else
{
lean_object* v_key_1586_; lean_object* v_value_1587_; lean_object* v_tail_1588_; uint8_t v___x_1589_; 
v_key_1586_ = lean_ctor_get(v_x_1584_, 0);
v_value_1587_ = lean_ctor_get(v_x_1584_, 1);
v_tail_1588_ = lean_ctor_get(v_x_1584_, 2);
v___x_1589_ = lean_name_eq(v_key_1586_, v_a_1583_);
if (v___x_1589_ == 0)
{
v_x_1584_ = v_tail_1588_;
goto _start;
}
else
{
lean_object* v___x_1591_; 
lean_inc(v_value_1587_);
v___x_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1591_, 0, v_value_1587_);
return v___x_1591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12___redArg___boxed(lean_object* v_a_1592_, lean_object* v_x_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12___redArg(v_a_1592_, v_x_1593_);
lean_dec(v_x_1593_);
lean_dec(v_a_1592_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8___redArg(lean_object* v_m_1595_, lean_object* v_a_1596_){
_start:
{
lean_object* v_buckets_1597_; lean_object* v___x_1598_; uint64_t v___y_1600_; 
v_buckets_1597_ = lean_ctor_get(v_m_1595_, 1);
v___x_1598_ = lean_array_get_size(v_buckets_1597_);
if (lean_obj_tag(v_a_1596_) == 0)
{
uint64_t v___x_1614_; 
v___x_1614_ = 1723ULL;
v___y_1600_ = v___x_1614_;
goto v___jp_1599_;
}
else
{
uint64_t v_hash_1615_; 
v_hash_1615_ = lean_ctor_get_uint64(v_a_1596_, sizeof(void*)*2);
v___y_1600_ = v_hash_1615_;
goto v___jp_1599_;
}
v___jp_1599_:
{
uint64_t v___x_1601_; uint64_t v___x_1602_; uint64_t v_fold_1603_; uint64_t v___x_1604_; uint64_t v___x_1605_; uint64_t v___x_1606_; size_t v___x_1607_; size_t v___x_1608_; size_t v___x_1609_; size_t v___x_1610_; size_t v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1601_ = 32ULL;
v___x_1602_ = lean_uint64_shift_right(v___y_1600_, v___x_1601_);
v_fold_1603_ = lean_uint64_xor(v___y_1600_, v___x_1602_);
v___x_1604_ = 16ULL;
v___x_1605_ = lean_uint64_shift_right(v_fold_1603_, v___x_1604_);
v___x_1606_ = lean_uint64_xor(v_fold_1603_, v___x_1605_);
v___x_1607_ = lean_uint64_to_usize(v___x_1606_);
v___x_1608_ = lean_usize_of_nat(v___x_1598_);
v___x_1609_ = ((size_t)1ULL);
v___x_1610_ = lean_usize_sub(v___x_1608_, v___x_1609_);
v___x_1611_ = lean_usize_land(v___x_1607_, v___x_1610_);
v___x_1612_ = lean_array_uget_borrowed(v_buckets_1597_, v___x_1611_);
v___x_1613_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12___redArg(v_a_1596_, v___x_1612_);
return v___x_1613_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_m_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8___redArg(v_m_1616_, v_a_1617_);
lean_dec(v_a_1617_);
lean_dec_ref(v_m_1616_);
return v_res_1618_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5(lean_object* v_declName_1622_, uint8_t v_isMeta_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v_env_1636_; lean_object* v___y_1638_; lean_object* v___x_1651_; 
v___x_1631_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5___closed__0);
v___x_1632_ = lean_st_ref_get(v___y_1629_);
v_env_1636_ = lean_ctor_get(v___x_1632_, 0);
lean_inc_ref(v_env_1636_);
lean_dec(v___x_1632_);
v___x_1651_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1636_, v_declName_1622_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_dec_ref(v_env_1636_);
lean_dec(v_declName_1622_);
goto v___jp_1633_;
}
else
{
lean_object* v_val_1652_; lean_object* v___x_1653_; lean_object* v_modules_1654_; lean_object* v___x_1655_; uint8_t v___x_1656_; 
v_val_1652_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_val_1652_);
lean_dec_ref_known(v___x_1651_, 1);
v___x_1653_ = l_Lean_Environment_header(v_env_1636_);
v_modules_1654_ = lean_ctor_get(v___x_1653_, 3);
lean_inc_ref(v_modules_1654_);
lean_dec_ref(v___x_1653_);
v___x_1655_ = lean_array_get_size(v_modules_1654_);
v___x_1656_ = lean_nat_dec_lt(v_val_1652_, v___x_1655_);
if (v___x_1656_ == 0)
{
lean_dec_ref(v_modules_1654_);
lean_dec(v_val_1652_);
lean_dec_ref(v_env_1636_);
lean_dec(v_declName_1622_);
goto v___jp_1633_;
}
else
{
lean_object* v___x_1657_; lean_object* v___x_1658_; uint8_t v___y_1660_; 
v___x_1657_ = lean_array_fget(v_modules_1654_, v_val_1652_);
lean_dec(v_val_1652_);
lean_dec_ref(v_modules_1654_);
v___x_1658_ = lean_st_ref_get(v___y_1629_);
if (v_isMeta_1623_ == 0)
{
lean_dec(v___x_1658_);
v___y_1660_ = v_isMeta_1623_;
goto v___jp_1659_;
}
else
{
lean_object* v_env_1671_; uint8_t v___x_1672_; 
v_env_1671_ = lean_ctor_get(v___x_1658_, 0);
lean_inc_ref(v_env_1671_);
lean_dec(v___x_1658_);
lean_inc(v_declName_1622_);
v___x_1672_ = l_Lean_isMarkedMeta(v_env_1671_, v_declName_1622_);
if (v___x_1672_ == 0)
{
v___y_1660_ = v_isMeta_1623_;
goto v___jp_1659_;
}
else
{
uint8_t v___x_1673_; 
v___x_1673_ = 0;
v___y_1660_ = v___x_1673_;
goto v___jp_1659_;
}
}
v___jp_1659_:
{
lean_object* v_toImport_1661_; lean_object* v_module_1662_; lean_object* v___x_1663_; 
v_toImport_1661_ = lean_ctor_get(v___x_1657_, 0);
lean_inc_ref(v_toImport_1661_);
lean_dec(v___x_1657_);
v_module_1662_ = lean_ctor_get(v_toImport_1661_, 0);
lean_inc(v_module_1662_);
lean_dec_ref(v_toImport_1661_);
lean_inc(v_declName_1622_);
v___x_1663_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6(v_module_1662_, v___y_1660_, v_declName_1622_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
lean_dec_ref_known(v___x_1663_, 1);
v___x_1664_ = l_Lean_indirectModUseExt;
v___x_1665_ = lean_box(1);
v___x_1666_ = lean_box(0);
lean_inc_ref(v_env_1636_);
v___x_1667_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1631_, v___x_1664_, v_env_1636_, v___x_1665_, v___x_1666_);
v___x_1668_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8___redArg(v___x_1667_, v_declName_1622_);
lean_dec(v___x_1667_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v___x_1669_; 
v___x_1669_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5___closed__1));
v___y_1638_ = v___x_1669_;
goto v___jp_1637_;
}
else
{
lean_object* v_val_1670_; 
v_val_1670_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_val_1670_);
lean_dec_ref_known(v___x_1668_, 1);
v___y_1638_ = v_val_1670_;
goto v___jp_1637_;
}
}
else
{
lean_dec_ref(v_env_1636_);
lean_dec(v_declName_1622_);
return v___x_1663_;
}
}
}
}
v___jp_1633_:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = lean_box(0);
v___x_1635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1634_);
return v___x_1635_;
}
v___jp_1637_:
{
lean_object* v___x_1639_; size_t v_sz_1640_; size_t v___x_1641_; lean_object* v___x_1642_; 
v___x_1639_ = lean_box(0);
v_sz_1640_ = lean_array_size(v___y_1638_);
v___x_1641_ = ((size_t)0ULL);
v___x_1642_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__7(v_env_1636_, v_declName_1622_, v___y_1638_, v_sz_1640_, v___x_1641_, v___x_1639_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
lean_dec_ref(v___y_1638_);
lean_dec_ref(v_env_1636_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1649_ == 0)
{
lean_object* v_unused_1650_; 
v_unused_1650_ = lean_ctor_get(v___x_1642_, 0);
lean_dec(v_unused_1650_);
v___x_1644_ = v___x_1642_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_dec(v___x_1642_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 0, v___x_1639_);
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1639_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
else
{
return v___x_1642_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5___boxed(lean_object* v_declName_1674_, lean_object* v_isMeta_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
uint8_t v_isMeta_boxed_1683_; lean_object* v_res_1684_; 
v_isMeta_boxed_1683_ = lean_unbox(v_isMeta_1675_);
v_res_1684_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5(v_declName_1674_, v_isMeta_boxed_1683_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6___redArg(lean_object* v_as_x27_1685_, lean_object* v_b_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
if (lean_obj_tag(v_as_x27_1685_) == 0)
{
lean_object* v___x_1694_; 
v___x_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1694_, 0, v_b_1686_);
return v___x_1694_;
}
else
{
lean_object* v_head_1695_; lean_object* v_tail_1696_; lean_object* v___x_1697_; uint8_t v___x_1698_; lean_object* v___x_1699_; 
v_head_1695_ = lean_ctor_get(v_as_x27_1685_, 0);
v_tail_1696_ = lean_ctor_get(v_as_x27_1685_, 1);
v___x_1697_ = lean_box(0);
v___x_1698_ = 1;
lean_inc(v_head_1695_);
v___x_1699_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5(v_head_1695_, v___x_1698_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_dec_ref_known(v___x_1699_, 1);
v_as_x27_1685_ = v_tail_1696_;
v_b_1686_ = v___x_1697_;
goto _start;
}
else
{
return v___x_1699_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6___redArg___boxed(lean_object* v_as_x27_1701_, lean_object* v_b_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6___redArg(v_as_x27_1701_, v_b_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v_as_x27_1701_);
return v_res_1710_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = l_Lean_maxRecDepthErrorMessage;
v___x_1717_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1716_);
return v___x_1717_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__4(void){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1718_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__3);
v___x_1719_ = l_Lean_MessageData_ofFormat(v___x_1718_);
return v___x_1719_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1720_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__4);
v___x_1721_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__2));
v___x_1722_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1721_);
lean_ctor_set(v___x_1722_, 1, v___x_1720_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg(lean_object* v_ref_1723_){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1725_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__5);
v___x_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1726_, 0, v_ref_1723_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
v___x_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1726_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___boxed(lean_object* v_ref_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg(v_ref_1728_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__2(lean_object* v_currNamespace_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1734_, 0, v_currNamespace_1731_);
lean_ctor_set(v___x_1734_, 1, v___y_1733_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__2___boxed(lean_object* v_currNamespace_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__2(v_currNamespace_1735_, v___y_1736_, v___y_1737_);
lean_dec_ref(v___y_1736_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__0(lean_object* v_env_1739_, lean_object* v_declName_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
uint8_t v___x_1743_; lean_object* v_env_1744_; lean_object* v___x_1745_; uint8_t v___x_1746_; uint8_t v___x_1747_; 
v___x_1743_ = 0;
v_env_1744_ = l_Lean_Environment_setExporting(v_env_1739_, v___x_1743_);
lean_inc(v_declName_1740_);
v___x_1745_ = l_Lean_mkPrivateName(v_env_1744_, v_declName_1740_);
v___x_1746_ = 1;
lean_inc_ref(v_env_1744_);
v___x_1747_ = l_Lean_Environment_contains(v_env_1744_, v___x_1745_, v___x_1746_);
if (v___x_1747_ == 0)
{
lean_object* v___x_1748_; uint8_t v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1748_ = l_Lean_privateToUserName(v_declName_1740_);
v___x_1749_ = l_Lean_Environment_contains(v_env_1744_, v___x_1748_, v___x_1746_);
v___x_1750_ = lean_box(v___x_1749_);
v___x_1751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
lean_ctor_set(v___x_1751_, 1, v___y_1742_);
return v___x_1751_;
}
else
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
lean_dec_ref(v_env_1744_);
lean_dec(v_declName_1740_);
v___x_1752_ = lean_box(v___x_1747_);
v___x_1753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
lean_ctor_set(v___x_1753_, 1, v___y_1742_);
return v___x_1753_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__0___boxed(lean_object* v_env_1754_, lean_object* v_declName_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__0(v_env_1754_, v_declName_1755_, v___y_1756_, v___y_1757_);
lean_dec_ref(v___y_1756_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__4(lean_object* v_env_1759_, lean_object* v_currNamespace_1760_, lean_object* v_openDecls_1761_, lean_object* v_n_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1765_ = l_Lean_ResolveName_resolveNamespace(v_env_1759_, v_currNamespace_1760_, v_openDecls_1761_, v_n_1762_);
v___x_1766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1765_);
lean_ctor_set(v___x_1766_, 1, v___y_1764_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__4___boxed(lean_object* v_env_1767_, lean_object* v_currNamespace_1768_, lean_object* v_openDecls_1769_, lean_object* v_n_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__4(v_env_1767_, v_currNamespace_1768_, v_openDecls_1769_, v_n_1770_, v___y_1771_, v___y_1772_);
lean_dec_ref(v___y_1771_);
return v_res_1773_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1774_ = lean_box(0);
v___x_1775_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
lean_ctor_set(v___x_1776_, 1, v___x_1774_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg(){
_start:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg___closed__0);
v___x_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1778_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg___boxed(lean_object* v___y_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg();
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__7(lean_object* v_as_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
if (lean_obj_tag(v_as_1782_) == 0)
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1790_ = lean_box(0);
v___x_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1790_);
return v___x_1791_;
}
else
{
lean_object* v_toCold_1792_; lean_object* v_options_1793_; uint8_t v_hasTrace_1794_; 
v_toCold_1792_ = lean_ctor_get(v___y_1787_, 0);
v_options_1793_ = lean_ctor_get(v_toCold_1792_, 2);
v_hasTrace_1794_ = lean_ctor_get_uint8(v_options_1793_, sizeof(void*)*1);
if (v_hasTrace_1794_ == 0)
{
lean_object* v_tail_1795_; 
v_tail_1795_ = lean_ctor_get(v_as_1782_, 1);
lean_inc(v_tail_1795_);
lean_dec_ref_known(v_as_1782_, 2);
v_as_1782_ = v_tail_1795_;
goto _start;
}
else
{
lean_object* v_head_1797_; lean_object* v_tail_1798_; lean_object* v_fst_1799_; lean_object* v_snd_1800_; lean_object* v_inheritedTraceOptions_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; uint8_t v___x_1804_; 
v_head_1797_ = lean_ctor_get(v_as_1782_, 0);
lean_inc(v_head_1797_);
v_tail_1798_ = lean_ctor_get(v_as_1782_, 1);
lean_inc(v_tail_1798_);
lean_dec_ref_known(v_as_1782_, 2);
v_fst_1799_ = lean_ctor_get(v_head_1797_, 0);
lean_inc_n(v_fst_1799_, 2);
v_snd_1800_ = lean_ctor_get(v_head_1797_, 1);
lean_inc(v_snd_1800_);
lean_dec(v_head_1797_);
v_inheritedTraceOptions_1801_ = lean_ctor_get(v_toCold_1792_, 11);
v___x_1802_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__13));
v___x_1803_ = l_Lean_Name_append(v___x_1802_, v_fst_1799_);
v___x_1804_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1801_, v_options_1793_, v___x_1803_);
lean_dec(v___x_1803_);
if (v___x_1804_ == 0)
{
lean_dec(v_snd_1800_);
lean_dec(v_fst_1799_);
v_as_1782_ = v_tail_1798_;
goto _start;
}
else
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1806_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1806_, 0, v_snd_1800_);
v___x_1807_ = l_Lean_MessageData_ofFormat(v___x_1806_);
v___x_1808_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg(v_fst_1799_, v___x_1807_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_dec_ref_known(v___x_1808_, 1);
v_as_1782_ = v_tail_1798_;
goto _start;
}
else
{
lean_dec(v_tail_1798_);
return v___x_1808_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__7___boxed(lean_object* v_as_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__7(v_as_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__3(lean_object* v_env_1819_, lean_object* v___x_1820_, lean_object* v_currNamespace_1821_, lean_object* v_openDecls_1822_, lean_object* v_n_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1826_ = l_Lean_ResolveName_resolveGlobalName(v_env_1819_, v___x_1820_, v_currNamespace_1821_, v_openDecls_1822_, v_n_1823_);
v___x_1827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
lean_ctor_set(v___x_1827_, 1, v___y_1825_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__3___boxed(lean_object* v_env_1828_, lean_object* v___x_1829_, lean_object* v_currNamespace_1830_, lean_object* v_openDecls_1831_, lean_object* v_n_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__3(v_env_1828_, v___x_1829_, v_currNamespace_1830_, v_openDecls_1831_, v_n_1832_, v___y_1833_, v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec_ref(v___x_1829_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8___redArg(lean_object* v_ref_1836_, lean_object* v_msg_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v_toCold_1845_; lean_object* v_currRecDepth_1846_; lean_object* v_ref_1847_; uint16_t v_optionFlags_1848_; uint8_t v_suppressElabErrors_1849_; uint8_t v_isRecordingDeps_1850_; lean_object* v_ref_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v_toCold_1845_ = lean_ctor_get(v___y_1842_, 0);
v_currRecDepth_1846_ = lean_ctor_get(v___y_1842_, 1);
v_ref_1847_ = lean_ctor_get(v___y_1842_, 2);
v_optionFlags_1848_ = lean_ctor_get_uint16(v___y_1842_, sizeof(void*)*3);
v_suppressElabErrors_1849_ = lean_ctor_get_uint8(v___y_1842_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1850_ = lean_ctor_get_uint8(v___y_1842_, sizeof(void*)*3 + 3);
v_ref_1851_ = l_Lean_replaceRef(v_ref_1836_, v_ref_1847_);
lean_inc(v_currRecDepth_1846_);
lean_inc_ref(v_toCold_1845_);
v___x_1852_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1852_, 0, v_toCold_1845_);
lean_ctor_set(v___x_1852_, 1, v_currRecDepth_1846_);
lean_ctor_set(v___x_1852_, 2, v_ref_1851_);
lean_ctor_set_uint16(v___x_1852_, sizeof(void*)*3, v_optionFlags_1848_);
lean_ctor_set_uint8(v___x_1852_, sizeof(void*)*3 + 2, v_suppressElabErrors_1849_);
lean_ctor_set_uint8(v___x_1852_, sizeof(void*)*3 + 3, v_isRecordingDeps_1850_);
v___x_1853_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg(v_msg_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___x_1852_, v___y_1843_);
lean_dec_ref_known(v___x_1852_, 3);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8___redArg___boxed(lean_object* v_ref_1854_, lean_object* v_msg_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8___redArg(v_ref_1854_, v_msg_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v_ref_1854_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___redArg(lean_object* v_x_1864_, lean_object* v___y_1865_){
_start:
{
if (lean_obj_tag(v_x_1864_) == 0)
{
lean_object* v_a_1866_; lean_object* v___x_1867_; 
v_a_1866_ = lean_ctor_get(v_x_1864_, 0);
lean_inc(v_a_1866_);
v___x_1867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1867_, 0, v_a_1866_);
lean_ctor_set(v___x_1867_, 1, v___y_1865_);
return v___x_1867_;
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1869_; 
v_a_1868_ = lean_ctor_get(v_x_1864_, 0);
lean_inc(v_a_1868_);
v___x_1869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1869_, 0, v_a_1868_);
lean_ctor_set(v___x_1869_, 1, v___y_1865_);
return v___x_1869_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___redArg___boxed(lean_object* v_x_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___redArg(v_x_1870_, v___y_1871_);
lean_dec_ref(v_x_1870_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__1(lean_object* v_env_1873_, lean_object* v_stx_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v___x_1877_; 
v___x_1877_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1873_, v_stx_1874_, v___y_1875_, v___y_1876_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1878_; 
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_a_1878_);
if (lean_obj_tag(v_a_1878_) == 0)
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1887_; 
v_a_1879_ = lean_ctor_get(v___x_1877_, 1);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1887_ == 0)
{
lean_object* v_unused_1888_; 
v_unused_1888_ = lean_ctor_get(v___x_1877_, 0);
lean_dec(v_unused_1888_);
v___x_1881_ = v___x_1877_;
v_isShared_1882_ = v_isSharedCheck_1887_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1877_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1887_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1883_; lean_object* v___x_1885_; 
v___x_1883_ = lean_box(0);
if (v_isShared_1882_ == 0)
{
lean_ctor_set(v___x_1881_, 0, v___x_1883_);
v___x_1885_ = v___x_1881_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1883_);
lean_ctor_set(v_reuseFailAlloc_1886_, 1, v_a_1879_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
else
{
lean_object* v_val_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1917_; 
v_val_1889_ = lean_ctor_get(v_a_1878_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v_a_1878_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1891_ = v_a_1878_;
v_isShared_1892_ = v_isSharedCheck_1917_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_val_1889_);
lean_dec(v_a_1878_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1917_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v_snd_1893_; 
v_snd_1893_ = lean_ctor_get(v_val_1889_, 1);
lean_inc(v_snd_1893_);
lean_dec(v_val_1889_);
if (lean_obj_tag(v_snd_1893_) == 0)
{
lean_object* v_a_1894_; lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1903_; 
lean_del_object(v___x_1891_);
v_a_1894_ = lean_ctor_get(v___x_1877_, 1);
lean_inc(v_a_1894_);
lean_dec_ref_known(v___x_1877_, 2);
v_a_1895_ = lean_ctor_get(v_snd_1893_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v_snd_1893_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1897_ = v_snd_1893_;
v_isShared_1898_ = v_isSharedCheck_1903_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v_snd_1893_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1903_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1895_);
v___x_1900_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
lean_object* v___x_1901_; 
v___x_1901_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___redArg(v___x_1900_, v_a_1894_);
lean_dec_ref(v___x_1900_);
return v___x_1901_;
}
}
}
else
{
lean_object* v_a_1904_; lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1916_; 
v_a_1904_ = lean_ctor_get(v___x_1877_, 1);
lean_inc(v_a_1904_);
lean_dec_ref_known(v___x_1877_, 2);
v_a_1905_ = lean_ctor_get(v_snd_1893_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v_snd_1893_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1907_ = v_snd_1893_;
v_isShared_1908_ = v_isSharedCheck_1916_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v_snd_1893_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1916_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v_a_1905_);
v___x_1910_ = v___x_1891_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
lean_object* v___x_1912_; 
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v___x_1910_);
v___x_1912_ = v___x_1907_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1910_);
v___x_1912_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
lean_object* v___x_1913_; 
v___x_1913_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___redArg(v___x_1912_, v_a_1904_);
lean_dec_ref(v___x_1912_);
return v___x_1913_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1918_; lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
v_a_1918_ = lean_ctor_get(v___x_1877_, 0);
v_a_1919_ = lean_ctor_get(v___x_1877_, 1);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1877_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_inc(v_a_1918_);
lean_dec(v___x_1877_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1918_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__1___boxed(lean_object* v_env_1927_, lean_object* v_stx_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__1(v_env_1927_, v_stx_1928_, v___y_1929_, v___y_1930_);
lean_dec_ref(v___y_1929_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg(lean_object* v_x_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v___x_1941_; lean_object* v_toCold_1942_; lean_object* v_env_1943_; lean_object* v_currRecDepth_1944_; lean_object* v_ref_1945_; lean_object* v_maxRecDepth_1946_; lean_object* v_currNamespace_1947_; lean_object* v_openDecls_1948_; lean_object* v_quotContext_1949_; lean_object* v_currMacroScope_1950_; lean_object* v___f_1951_; lean_object* v___f_1952_; lean_object* v___x_1953_; lean_object* v___f_1954_; lean_object* v___f_1955_; lean_object* v___f_1956_; lean_object* v_methods_1957_; lean_object* v___x_1958_; lean_object* v_nextMacroScope_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1941_ = lean_st_ref_get(v___y_1939_);
v_toCold_1942_ = lean_ctor_get(v___y_1938_, 0);
v_env_1943_ = lean_ctor_get(v___x_1941_, 0);
lean_inc_ref_n(v_env_1943_, 4);
lean_dec(v___x_1941_);
v_currRecDepth_1944_ = lean_ctor_get(v___y_1938_, 1);
v_ref_1945_ = lean_ctor_get(v___y_1938_, 2);
v_maxRecDepth_1946_ = lean_ctor_get(v_toCold_1942_, 3);
v_currNamespace_1947_ = lean_ctor_get(v_toCold_1942_, 4);
v_openDecls_1948_ = lean_ctor_get(v_toCold_1942_, 5);
v_quotContext_1949_ = lean_ctor_get(v_toCold_1942_, 8);
v_currMacroScope_1950_ = lean_ctor_get(v_toCold_1942_, 9);
v___f_1951_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1951_, 0, v_env_1943_);
v___f_1952_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1952_, 0, v_env_1943_);
v___x_1953_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1938_);
lean_inc_n(v_currNamespace_1947_, 3);
v___f_1954_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_1954_, 0, v_currNamespace_1947_);
lean_inc_n(v_openDecls_1948_, 2);
v___f_1955_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__3___boxed), 7, 4);
lean_closure_set(v___f_1955_, 0, v_env_1943_);
lean_closure_set(v___f_1955_, 1, v___x_1953_);
lean_closure_set(v___f_1955_, 2, v_currNamespace_1947_);
lean_closure_set(v___f_1955_, 3, v_openDecls_1948_);
v___f_1956_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_1956_, 0, v_env_1943_);
lean_closure_set(v___f_1956_, 1, v_currNamespace_1947_);
lean_closure_set(v___f_1956_, 2, v_openDecls_1948_);
v_methods_1957_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1957_, 0, v___f_1952_);
lean_ctor_set(v_methods_1957_, 1, v___f_1954_);
lean_ctor_set(v_methods_1957_, 2, v___f_1951_);
lean_ctor_set(v_methods_1957_, 3, v___f_1956_);
lean_ctor_set(v_methods_1957_, 4, v___f_1955_);
v___x_1958_ = lean_st_ref_get(v___y_1939_);
v_nextMacroScope_1959_ = lean_ctor_get(v___x_1958_, 1);
lean_inc(v_nextMacroScope_1959_);
lean_dec(v___x_1958_);
lean_inc(v_ref_1945_);
lean_inc(v_maxRecDepth_1946_);
lean_inc(v_currRecDepth_1944_);
lean_inc(v_currMacroScope_1950_);
lean_inc(v_quotContext_1949_);
v___x_1960_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1960_, 0, v_methods_1957_);
lean_ctor_set(v___x_1960_, 1, v_quotContext_1949_);
lean_ctor_set(v___x_1960_, 2, v_currMacroScope_1950_);
lean_ctor_set(v___x_1960_, 3, v_currRecDepth_1944_);
lean_ctor_set(v___x_1960_, 4, v_maxRecDepth_1946_);
lean_ctor_set(v___x_1960_, 5, v_ref_1945_);
v___x_1961_ = lean_box(0);
v___x_1962_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1962_, 0, v_nextMacroScope_1959_);
lean_ctor_set(v___x_1962_, 1, v___x_1961_);
lean_ctor_set(v___x_1962_, 2, v___x_1961_);
v___x_1963_ = lean_apply_2(v_x_1933_, v___x_1960_, v___x_1962_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v_a_1964_; lean_object* v_a_1965_; lean_object* v_macroScope_1966_; lean_object* v_traceMsgs_1967_; lean_object* v_expandedMacroDecls_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v_a_1964_ = lean_ctor_get(v___x_1963_, 1);
lean_inc(v_a_1964_);
v_a_1965_ = lean_ctor_get(v___x_1963_, 0);
lean_inc(v_a_1965_);
lean_dec_ref_known(v___x_1963_, 2);
v_macroScope_1966_ = lean_ctor_get(v_a_1964_, 0);
lean_inc(v_macroScope_1966_);
v_traceMsgs_1967_ = lean_ctor_get(v_a_1964_, 1);
lean_inc(v_traceMsgs_1967_);
v_expandedMacroDecls_1968_ = lean_ctor_get(v_a_1964_, 2);
lean_inc(v_expandedMacroDecls_1968_);
lean_dec(v_a_1964_);
v___x_1969_ = lean_box(0);
v___x_1970_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6___redArg(v_expandedMacroDecls_1968_, v___x_1969_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
lean_dec(v_expandedMacroDecls_1968_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v___x_1971_; lean_object* v_env_1972_; lean_object* v_ngen_1973_; lean_object* v_auxDeclNGen_1974_; lean_object* v_traceState_1975_; lean_object* v_cache_1976_; lean_object* v_recordedDeps_1977_; lean_object* v_messages_1978_; lean_object* v_infoState_1979_; lean_object* v_snapshotTasks_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_2006_; 
lean_dec_ref_known(v___x_1970_, 1);
v___x_1971_ = lean_st_ref_take(v___y_1939_);
v_env_1972_ = lean_ctor_get(v___x_1971_, 0);
v_ngen_1973_ = lean_ctor_get(v___x_1971_, 2);
v_auxDeclNGen_1974_ = lean_ctor_get(v___x_1971_, 3);
v_traceState_1975_ = lean_ctor_get(v___x_1971_, 4);
v_cache_1976_ = lean_ctor_get(v___x_1971_, 5);
v_recordedDeps_1977_ = lean_ctor_get(v___x_1971_, 6);
v_messages_1978_ = lean_ctor_get(v___x_1971_, 7);
v_infoState_1979_ = lean_ctor_get(v___x_1971_, 8);
v_snapshotTasks_1980_ = lean_ctor_get(v___x_1971_, 9);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_2006_ == 0)
{
lean_object* v_unused_2007_; 
v_unused_2007_ = lean_ctor_get(v___x_1971_, 1);
lean_dec(v_unused_2007_);
v___x_1982_ = v___x_1971_;
v_isShared_1983_ = v_isSharedCheck_2006_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_snapshotTasks_1980_);
lean_inc(v_infoState_1979_);
lean_inc(v_messages_1978_);
lean_inc(v_recordedDeps_1977_);
lean_inc(v_cache_1976_);
lean_inc(v_traceState_1975_);
lean_inc(v_auxDeclNGen_1974_);
lean_inc(v_ngen_1973_);
lean_inc(v_env_1972_);
lean_dec(v___x_1971_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_2006_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 1, v_macroScope_1966_);
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_env_1972_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v_macroScope_1966_);
lean_ctor_set(v_reuseFailAlloc_2005_, 2, v_ngen_1973_);
lean_ctor_set(v_reuseFailAlloc_2005_, 3, v_auxDeclNGen_1974_);
lean_ctor_set(v_reuseFailAlloc_2005_, 4, v_traceState_1975_);
lean_ctor_set(v_reuseFailAlloc_2005_, 5, v_cache_1976_);
lean_ctor_set(v_reuseFailAlloc_2005_, 6, v_recordedDeps_1977_);
lean_ctor_set(v_reuseFailAlloc_2005_, 7, v_messages_1978_);
lean_ctor_set(v_reuseFailAlloc_2005_, 8, v_infoState_1979_);
lean_ctor_set(v_reuseFailAlloc_2005_, 9, v_snapshotTasks_1980_);
v___x_1985_ = v_reuseFailAlloc_2005_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1986_ = lean_st_ref_put(v___y_1939_, v___x_1985_);
v___x_1987_ = l_List_reverse___redArg(v_traceMsgs_1967_);
v___x_1988_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__7(v___x_1987_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_1995_ == 0)
{
lean_object* v_unused_1996_; 
v_unused_1996_ = lean_ctor_get(v___x_1988_, 0);
lean_dec(v_unused_1996_);
v___x_1990_ = v___x_1988_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_dec(v___x_1988_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 0, v_a_1965_);
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1965_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
else
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
lean_dec(v_a_1965_);
v_a_1997_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1999_ = v___x_1988_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1988_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1997_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
}
}
else
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
lean_dec(v_traceMsgs_1967_);
lean_dec(v_macroScope_1966_);
lean_dec(v_a_1965_);
v_a_2008_ = lean_ctor_get(v___x_1970_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1970_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_1970_);
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
lean_object* v_a_2016_; 
v_a_2016_ = lean_ctor_get(v___x_1963_, 0);
lean_inc(v_a_2016_);
lean_dec_ref_known(v___x_1963_, 2);
if (lean_obj_tag(v_a_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v_a_2018_; lean_object* v___x_2019_; uint8_t v___x_2020_; 
v_a_2017_ = lean_ctor_get(v_a_2016_, 0);
lean_inc(v_a_2017_);
v_a_2018_ = lean_ctor_get(v_a_2016_, 1);
lean_inc_ref(v_a_2018_);
lean_dec_ref_known(v_a_2016_, 2);
v___x_2019_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___closed__0));
v___x_2020_ = lean_string_dec_eq(v_a_2018_, v___x_2019_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2021_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2021_, 0, v_a_2018_);
v___x_2022_ = l_Lean_MessageData_ofFormat(v___x_2021_);
v___x_2023_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8___redArg(v_a_2017_, v___x_2022_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
lean_dec(v_a_2017_);
return v___x_2023_;
}
else
{
lean_object* v___x_2024_; 
lean_dec_ref(v_a_2018_);
v___x_2024_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg(v_a_2017_);
return v___x_2024_;
}
}
else
{
lean_object* v___x_2025_; 
v___x_2025_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg();
return v___x_2025_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___boxed(lean_object* v_x_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg(v_x_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
return v_res_2034_;
}
}
static lean_object* _init_l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__1(void){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2036_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__0));
v___x_2037_ = l_Lean_stringToMessageData(v___x_2036_);
return v___x_2037_;
}
}
static lean_object* _init_l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__6(void){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__5));
v___x_2047_ = l_Lean_stringToMessageData(v___x_2046_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f(lean_object* v_e_2048_, lean_object* v_dec_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_){
_start:
{
lean_object* v___x_2058_; 
v___x_2058_ = l_Lean_Elab_Do_Forward_matchApp_x3f(v_e_2048_);
if (lean_obj_tag(v___x_2058_) == 1)
{
lean_object* v_val_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2229_; 
v_val_2059_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2061_ = v___x_2058_;
v_isShared_2062_ = v_isSharedCheck_2229_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_val_2059_);
lean_dec(v___x_2058_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2229_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v_fst_2063_; lean_object* v_snd_2064_; lean_object* v___f_2065_; lean_object* v___x_2066_; 
v_fst_2063_ = lean_ctor_get(v_val_2059_, 0);
lean_inc_n(v_fst_2063_, 2);
v_snd_2064_ = lean_ctor_get(v_val_2059_, 1);
lean_inc(v_snd_2064_);
lean_dec(v_val_2059_);
lean_inc(v_a_2054_);
lean_inc_ref(v_a_2053_);
lean_inc(v_a_2052_);
lean_inc_ref(v_a_2051_);
v___f_2065_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___boxed), 8, 5);
lean_closure_set(v___f_2065_, 0, v_a_2051_);
lean_closure_set(v___f_2065_, 1, v_a_2052_);
lean_closure_set(v___f_2065_, 2, v_a_2053_);
lean_closure_set(v___f_2065_, 3, v_a_2054_);
lean_closure_set(v___f_2065_, 4, v_fst_2063_);
v___x_2066_ = l_Lean_Core_withFreshMacroScope___redArg(v___f_2065_, v_a_2055_, v_a_2056_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v_fst_2068_; lean_object* v_snd_2069_; lean_object* v___x_2070_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_a_2067_);
lean_dec_ref_known(v___x_2066_, 1);
v_fst_2068_ = lean_ctor_get(v_a_2067_, 0);
lean_inc_n(v_fst_2068_, 2);
v_snd_2069_ = lean_ctor_get(v_a_2067_, 1);
lean_inc_n(v_snd_2069_, 2);
lean_dec(v_a_2067_);
v___x_2070_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder(v_fst_2063_, v_fst_2068_, v_snd_2069_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_binders_2071_; lean_object* v_body_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2212_; 
lean_dec_ref_known(v___x_2070_, 1);
v_binders_2071_ = lean_ctor_get(v_snd_2064_, 0);
v_body_2072_ = lean_ctor_get(v_snd_2064_, 1);
v_isSharedCheck_2212_ = !lean_is_exclusive(v_snd_2064_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2074_ = v_snd_2064_;
v_isShared_2075_ = v_isSharedCheck_2212_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_body_2072_);
lean_inc(v_binders_2071_);
lean_dec(v_snd_2064_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2212_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___f_2076_; lean_object* v___x_2077_; 
lean_inc(v_body_2072_);
v___f_2076_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__1___boxed), 10, 1);
lean_closure_set(v___f_2076_, 0, v_body_2072_);
v___x_2077_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_body_2072_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; lean_object* v___x_2079_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_a_2078_);
lean_dec_ref_known(v___x_2077_, 1);
v___x_2079_ = l_Lean_Elab_Do_EffectForwarder_ofCont(v_a_2078_, v_dec_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_);
lean_dec(v_a_2078_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; lean_object* v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v___y_2120_; lean_object* v___f_2152_; lean_object* v___x_2153_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc_n(v_a_2080_, 2);
lean_dec_ref_known(v___x_2079_, 1);
lean_inc_ref(v_a_2050_);
v___f_2152_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__2___boxed), 12, 3);
lean_closure_set(v___f_2152_, 0, v_a_2080_);
lean_closure_set(v___f_2152_, 1, v___f_2076_);
lean_closure_set(v___f_2152_, 2, v_a_2050_);
lean_inc(v_a_2056_);
lean_inc_ref(v_a_2055_);
lean_inc(v_a_2054_);
lean_inc_ref(v_a_2053_);
lean_inc(v_fst_2068_);
v___x_2153_ = lean_infer_type(v_fst_2068_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v_a_2154_; lean_object* v___x_2155_; lean_object* v_a_2156_; lean_object* v_ref_2157_; uint8_t v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2163_; 
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_a_2154_);
lean_dec_ref_known(v___x_2153_, 1);
v___x_2155_ = l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___redArg(v_a_2154_, v_a_2054_);
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
lean_inc(v_a_2156_);
lean_dec_ref(v___x_2155_);
v_ref_2157_ = lean_ctor_get(v_a_2055_, 2);
v___x_2158_ = 0;
v___x_2159_ = l_Lean_SourceInfo_fromRef(v_ref_2157_, v___x_2158_);
v___x_2160_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__3));
v___x_2161_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__4));
lean_inc(v___x_2159_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set_tag(v___x_2074_, 2);
lean_ctor_set(v___x_2074_, 1, v___x_2161_);
lean_ctor_set(v___x_2074_, 0, v___x_2159_);
v___x_2163_ = v___x_2074_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2159_);
lean_ctor_set(v_reuseFailAlloc_2195_, 1, v___x_2161_);
v___x_2163_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
lean_object* v___x_2164_; size_t v_sz_2165_; size_t v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2164_ = l_Lean_Syntax_node1(v___x_2159_, v___x_2160_, v___x_2163_);
v_sz_2165_ = lean_array_size(v_binders_2071_);
v___x_2166_ = ((size_t)0ULL);
v___x_2167_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__2(v_sz_2165_, v___x_2166_, v_binders_2071_);
v___x_2168_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandFunBinders___boxed), 4, 2);
lean_closure_set(v___x_2168_, 0, v___x_2167_);
lean_closure_set(v___x_2168_, 1, v___x_2164_);
v___x_2169_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg(v___x_2168_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v_snd_2171_; lean_object* v_snd_2172_; uint8_t v___x_2173_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_a_2170_);
lean_dec_ref_known(v___x_2169_, 1);
v_snd_2171_ = lean_ctor_get(v_a_2170_, 1);
v_snd_2172_ = lean_ctor_get(v_snd_2171_, 1);
v___x_2173_ = lean_unbox(v_snd_2172_);
if (v___x_2173_ == 0)
{
lean_object* v_fst_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v_fst_2174_ = lean_ctor_get(v_a_2170_, 0);
lean_inc(v_fst_2174_);
lean_dec(v_a_2170_);
v___x_2175_ = lean_box(0);
v___x_2176_ = l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__3(v_a_2156_, v_fst_2174_, v___f_2152_, v___x_2175_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_);
lean_dec(v_fst_2174_);
v___y_2120_ = v___x_2176_;
goto v___jp_2119_;
}
else
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
lean_dec(v_a_2170_);
lean_dec(v_a_2156_);
lean_dec_ref(v___f_2152_);
lean_dec(v_a_2080_);
lean_dec(v_snd_2069_);
lean_dec(v_fst_2068_);
lean_del_object(v___x_2061_);
v___x_2177_ = lean_obj_once(&l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__6, &l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__6_once, _init_l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__6);
v___x_2178_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg(v___x_2177_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_);
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2178_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2178_);
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
else
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2194_; 
lean_dec(v_a_2156_);
lean_dec_ref(v___f_2152_);
lean_dec(v_a_2080_);
lean_dec(v_snd_2069_);
lean_dec(v_fst_2068_);
lean_del_object(v___x_2061_);
v_a_2187_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2189_ = v___x_2169_;
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2169_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2192_; 
if (v_isShared_2190_ == 0)
{
v___x_2192_ = v___x_2189_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2187_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
}
else
{
lean_dec_ref(v___f_2152_);
lean_del_object(v___x_2074_);
lean_dec_ref(v_binders_2071_);
v___y_2120_ = v___x_2153_;
goto v___jp_2119_;
}
v___jp_2081_:
{
lean_object* v___x_2089_; 
v___x_2089_ = l_Lean_Elab_Do_EffectForwarder_restoreCont(v_a_2080_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v___x_2091_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2090_);
lean_dec_ref_known(v___x_2089_, 1);
v___x_2091_ = l_Lean_Elab_Do_DoElemCont_mkBindUnlessPure(v_a_2090_, v_snd_2069_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2102_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2094_ = v___x_2091_;
v_isShared_2095_ = v_isSharedCheck_2102_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2091_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2102_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2097_; 
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 0, v_a_2092_);
v___x_2097_ = v___x_2061_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2092_);
v___x_2097_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
lean_object* v___x_2099_; 
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v___x_2097_);
v___x_2099_ = v___x_2094_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2097_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
else
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2110_; 
lean_del_object(v___x_2061_);
v_a_2103_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2105_ = v___x_2091_;
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2091_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
if (v_isShared_2106_ == 0)
{
v___x_2108_ = v___x_2105_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2103_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
lean_dec(v_snd_2069_);
lean_del_object(v___x_2061_);
v_a_2111_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2089_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2089_);
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
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
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
v___jp_2119_:
{
if (lean_obj_tag(v___y_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v_a_2121_ = lean_ctor_get(v___y_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref_known(v___y_2120_, 1);
v___x_2122_ = l_Lean_Expr_mvarId_x21(v_fst_2068_);
lean_dec(v_fst_2068_);
lean_inc(v_a_2056_);
lean_inc_ref(v_a_2055_);
lean_inc(v_a_2054_);
lean_inc_ref(v_a_2053_);
v___x_2123_ = lean_checked_assign(v___x_2122_, v_a_2121_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; uint8_t v___x_2125_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_a_2124_);
lean_dec_ref_known(v___x_2123_, 1);
v___x_2125_ = lean_unbox(v_a_2124_);
lean_dec(v_a_2124_);
if (v___x_2125_ == 0)
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
lean_dec(v_a_2080_);
lean_dec(v_snd_2069_);
lean_del_object(v___x_2061_);
v___x_2126_ = lean_obj_once(&l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__1, &l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__1_once, _init_l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__1);
v___x_2127_ = l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0___redArg(v___x_2126_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_);
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2130_ = v___x_2127_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2127_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2128_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
else
{
v___y_2082_ = v_a_2050_;
v___y_2083_ = v_a_2051_;
v___y_2084_ = v_a_2052_;
v___y_2085_ = v_a_2053_;
v___y_2086_ = v_a_2054_;
v___y_2087_ = v_a_2055_;
v___y_2088_ = v_a_2056_;
goto v___jp_2081_;
}
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_dec(v_a_2080_);
lean_dec(v_snd_2069_);
lean_del_object(v___x_2061_);
v_a_2136_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2123_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2123_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
lean_dec(v_a_2080_);
lean_dec(v_snd_2069_);
lean_dec(v_fst_2068_);
lean_del_object(v___x_2061_);
v_a_2144_ = lean_ctor_get(v___y_2120_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___y_2120_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___y_2120_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___y_2120_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2144_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
}
else
{
lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2203_; 
lean_dec_ref(v___f_2076_);
lean_del_object(v___x_2074_);
lean_dec_ref(v_binders_2071_);
lean_dec(v_snd_2069_);
lean_dec(v_fst_2068_);
lean_del_object(v___x_2061_);
v_a_2196_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2198_ = v___x_2079_;
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v___x_2079_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2199_ == 0)
{
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_a_2196_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
lean_dec_ref(v___f_2076_);
lean_del_object(v___x_2074_);
lean_dec_ref(v_binders_2071_);
lean_dec(v_snd_2069_);
lean_dec(v_fst_2068_);
lean_del_object(v___x_2061_);
lean_dec_ref(v_dec_2049_);
v_a_2204_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_2077_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2077_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
lean_dec(v_snd_2069_);
lean_dec(v_fst_2068_);
lean_dec(v_snd_2064_);
lean_del_object(v___x_2061_);
lean_dec_ref(v_dec_2049_);
v_a_2213_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2070_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2070_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
lean_dec(v_snd_2064_);
lean_dec(v_fst_2063_);
lean_del_object(v___x_2061_);
lean_dec_ref(v_dec_2049_);
v_a_2221_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2223_ = v___x_2066_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2066_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2221_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
}
else
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
lean_dec(v___x_2058_);
lean_dec_ref(v_dec_2049_);
v___x_2230_ = lean_box(0);
v___x_2231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2230_);
return v___x_2231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___boxed(lean_object* v_e_2232_, lean_object* v_dec_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l_Lean_Elab_Do_tryElabForwardApp_x3f(v_e_2232_, v_dec_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
lean_dec(v_a_2240_);
lean_dec_ref(v_a_2239_);
lean_dec(v_a_2238_);
lean_dec_ref(v_a_2237_);
lean_dec(v_a_2236_);
lean_dec_ref(v_a_2235_);
lean_dec_ref(v_a_2234_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0(lean_object* v_00_u03b1_2243_, lean_object* v_msg_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v___x_2253_; 
v___x_2253_ = l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0___redArg(v_msg_2244_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0___boxed(lean_object* v_00_u03b1_2254_, lean_object* v_msg_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0(v_00_u03b1_2254_, v_msg_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec_ref(v___y_2256_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4(lean_object* v_00_u03b1_2265_, lean_object* v_x_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v___x_2269_; 
v___x_2269_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___redArg(v_x_2266_, v___y_2268_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2270_, lean_object* v_x_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4(v_00_u03b1_2270_, v_x_2271_, v___y_2272_, v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec_ref(v_x_2271_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9(lean_object* v_00_u03b1_2275_, lean_object* v_ref_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg(v_ref_2276_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___boxed(lean_object* v_00_u03b1_2285_, lean_object* v_ref_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9(v_00_u03b1_2285_, v_ref_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10(lean_object* v_00_u03b1_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v___x_2303_; 
v___x_2303_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg();
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___boxed(lean_object* v_00_u03b1_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10(v_00_u03b1_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3(lean_object* v_00_u03b1_2313_, lean_object* v_x_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v___x_2322_; 
v___x_2322_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg(v_x_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___boxed(lean_object* v_00_u03b1_2323_, lean_object* v_x_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3(v_00_u03b1_2323_, v_x_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3(lean_object* v_cls_2333_, lean_object* v_msg_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v___x_2342_; 
v___x_2342_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg(v_cls_2333_, v_msg_2334_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___boxed(lean_object* v_cls_2343_, lean_object* v_msg_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3(v_cls_2343_, v_msg_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6(lean_object* v_as_2353_, lean_object* v_as_x27_2354_, lean_object* v_b_2355_, lean_object* v_a_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
lean_object* v___x_2364_; 
v___x_2364_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6___redArg(v_as_x27_2354_, v_b_2355_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6___boxed(lean_object* v_as_2365_, lean_object* v_as_x27_2366_, lean_object* v_b_2367_, lean_object* v_a_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6(v_as_2365_, v_as_x27_2366_, v_b_2367_, v_a_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v_as_x27_2366_);
lean_dec(v_as_2365_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8(lean_object* v_00_u03b1_2377_, lean_object* v_ref_2378_, lean_object* v_msg_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v___x_2387_; 
v___x_2387_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8___redArg(v_ref_2378_, v_msg_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8___boxed(lean_object* v_00_u03b1_2388_, lean_object* v_ref_2389_, lean_object* v_msg_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
lean_object* v_res_2398_; 
v_res_2398_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8(v_00_u03b1_2388_, v_ref_2389_, v_msg_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v_ref_2389_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_2399_, lean_object* v_m_2400_, lean_object* v_a_2401_){
_start:
{
lean_object* v___x_2402_; 
v___x_2402_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8___redArg(v_m_2400_, v_a_2401_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_2403_, lean_object* v_m_2404_, lean_object* v_a_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8(v_00_u03b2_2403_, v_m_2404_, v_a_2405_);
lean_dec(v_a_2405_);
lean_dec_ref(v_m_2404_);
return v_res_2406_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9(lean_object* v_00_u03b2_2407_, lean_object* v_x_2408_, lean_object* v_x_2409_){
_start:
{
uint8_t v___x_2410_; 
v___x_2410_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9___redArg(v_x_2408_, v_x_2409_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9___boxed(lean_object* v_00_u03b2_2411_, lean_object* v_x_2412_, lean_object* v_x_2413_){
_start:
{
uint8_t v_res_2414_; lean_object* v_r_2415_; 
v_res_2414_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9(v_00_u03b2_2411_, v_x_2412_, v_x_2413_);
lean_dec_ref(v_x_2413_);
lean_dec_ref(v_x_2412_);
v_r_2415_ = lean_box(v_res_2414_);
return v_r_2415_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12(lean_object* v_00_u03b2_2416_, lean_object* v_a_2417_, lean_object* v_x_2418_){
_start:
{
lean_object* v___x_2419_; 
v___x_2419_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12___redArg(v_a_2417_, v_x_2418_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12___boxed(lean_object* v_00_u03b2_2420_, lean_object* v_a_2421_, lean_object* v_x_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12(v_00_u03b2_2420_, v_a_2421_, v_x_2422_);
lean_dec(v_x_2422_);
lean_dec(v_a_2421_);
return v_res_2423_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13(lean_object* v_00_u03b2_2424_, lean_object* v_x_2425_, size_t v_x_2426_, lean_object* v_x_2427_){
_start:
{
uint8_t v___x_2428_; 
v___x_2428_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13___redArg(v_x_2425_, v_x_2426_, v_x_2427_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13___boxed(lean_object* v_00_u03b2_2429_, lean_object* v_x_2430_, lean_object* v_x_2431_, lean_object* v_x_2432_){
_start:
{
size_t v_x_30088__boxed_2433_; uint8_t v_res_2434_; lean_object* v_r_2435_; 
v_x_30088__boxed_2433_ = lean_unbox_usize(v_x_2431_);
lean_dec(v_x_2431_);
v_res_2434_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13(v_00_u03b2_2429_, v_x_2430_, v_x_30088__boxed_2433_, v_x_2432_);
lean_dec_ref(v_x_2432_);
lean_dec_ref(v_x_2430_);
v_r_2435_ = lean_box(v_res_2434_);
return v_r_2435_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16(lean_object* v_00_u03b2_2436_, lean_object* v_keys_2437_, lean_object* v_vals_2438_, lean_object* v_heq_2439_, lean_object* v_i_2440_, lean_object* v_k_2441_){
_start:
{
uint8_t v___x_2442_; 
v___x_2442_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16___redArg(v_keys_2437_, v_i_2440_, v_k_2441_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16___boxed(lean_object* v_00_u03b2_2443_, lean_object* v_keys_2444_, lean_object* v_vals_2445_, lean_object* v_heq_2446_, lean_object* v_i_2447_, lean_object* v_k_2448_){
_start:
{
uint8_t v_res_2449_; lean_object* v_r_2450_; 
v_res_2449_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16(v_00_u03b2_2443_, v_keys_2444_, v_vals_2445_, v_heq_2446_, v_i_2447_, v_k_2448_);
lean_dec_ref(v_k_2448_);
lean_dec_ref(v_vals_2445_);
lean_dec_ref(v_keys_2444_);
v_r_2450_ = lean_box(v_res_2449_);
return v_r_2450_;
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
