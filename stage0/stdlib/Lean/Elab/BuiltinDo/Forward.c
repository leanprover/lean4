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
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_toCold_57_; lean_object* v_options_58_; lean_object* v___x_59_; uint8_t v___x_60_; 
v_toCold_57_ = lean_ctor_get(v___y_55_, 0);
v_options_58_ = lean_ctor_get(v_toCold_57_, 2);
v___x_59_ = l_Lean_Elab_pp_macroStack;
v___x_60_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__2(v_options_58_, v___x_59_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; 
lean_dec(v_macroStack_54_);
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v_msgData_53_);
return v___x_61_;
}
else
{
if (lean_obj_tag(v_macroStack_54_) == 0)
{
lean_object* v___x_62_; 
v___x_62_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_62_, 0, v_msgData_53_);
return v___x_62_;
}
else
{
lean_object* v_head_63_; lean_object* v_after_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_79_; 
v_head_63_ = lean_ctor_get(v_macroStack_54_, 0);
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
lean_ctor_set(v___x_66_, 0, v_msgData_53_);
v___x_70_ = v___x_66_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v_msgData_53_);
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
v___x_76_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1_spec__3(v_msgData_75_, v_macroStack_54_);
v___x_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
return v___x_77_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_81_, lean_object* v_macroStack_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg(v_msgData_81_, v_macroStack_82_, v___y_83_);
lean_dec_ref(v___y_83_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0(lean_object* v_msgData_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v___x_92_; lean_object* v_env_93_; lean_object* v___x_94_; lean_object* v_toCold_95_; lean_object* v_mctx_96_; lean_object* v_lctx_97_; lean_object* v_options_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_92_ = lean_st_ref_get(v___y_90_);
v_env_93_ = lean_ctor_get(v___x_92_, 0);
lean_inc_ref(v_env_93_);
lean_dec(v___x_92_);
v___x_94_ = lean_st_ref_get(v___y_88_);
v_toCold_95_ = lean_ctor_get(v___y_89_, 0);
v_mctx_96_ = lean_ctor_get(v___x_94_, 0);
lean_inc_ref(v_mctx_96_);
lean_dec(v___x_94_);
v_lctx_97_ = lean_ctor_get(v___y_87_, 2);
v_options_98_ = lean_ctor_get(v_toCold_95_, 2);
lean_inc_ref(v_options_98_);
lean_inc_ref(v_lctx_97_);
v___x_99_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_99_, 0, v_env_93_);
lean_ctor_set(v___x_99_, 1, v_mctx_96_);
lean_ctor_set(v___x_99_, 2, v_lctx_97_);
lean_ctor_set(v___x_99_, 3, v_options_98_);
v___x_100_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v_msgData_86_);
v___x_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0___boxed(lean_object* v_msgData_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0(v_msgData_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg(lean_object* v_msg_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v_ref_117_; lean_object* v_macroStack_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v_a_121_; lean_object* v___x_122_; lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_131_; 
v_ref_117_ = lean_ctor_get(v___y_114_, 2);
v_macroStack_118_ = lean_ctor_get(v___y_110_, 1);
v___x_119_ = l_Lean_Elab_getBetterRef(v_ref_117_, v_macroStack_118_);
v___x_120_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0(v_msg_109_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
v_a_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_a_121_);
lean_dec_ref(v___x_120_);
lean_inc(v_macroStack_118_);
v___x_122_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg(v_a_121_, v_macroStack_118_, v___y_114_);
v_a_123_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_131_ == 0)
{
v___x_125_ = v___x_122_;
v_isShared_126_ = v_isSharedCheck_131_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_122_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_131_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_119_);
lean_ctor_set(v___x_127_, 1, v_a_123_);
if (v_isShared_126_ == 0)
{
lean_ctor_set_tag(v___x_125_, 1);
lean_ctor_set(v___x_125_, 0, v___x_127_);
v___x_129_ = v___x_125_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg___boxed(lean_object* v_msg_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg(v_msg_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
return v_res_140_;
}
}
static lean_object* _init_l_Lean_Elab_Do_elabDoForward___redArg___closed__1(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = ((lean_object*)(l_Lean_Elab_Do_elabDoForward___redArg___closed__0));
v___x_143_ = l_Lean_stringToMessageData(v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoForward___redArg(lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = lean_obj_once(&l_Lean_Elab_Do_elabDoForward___redArg___closed__1, &l_Lean_Elab_Do_elabDoForward___redArg___closed__1_once, _init_l_Lean_Elab_Do_elabDoForward___redArg___closed__1);
v___x_152_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg(v___x_151_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoForward___redArg___boxed(lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lean_Elab_Do_elabDoForward___redArg(v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_);
lean_dec(v_a_158_);
lean_dec_ref(v_a_157_);
lean_dec(v_a_156_);
lean_dec_ref(v_a_155_);
lean_dec(v_a_154_);
lean_dec_ref(v_a_153_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoForward(lean_object* v_x_161_, lean_object* v_x_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_Lean_Elab_Do_elabDoForward___redArg(v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoForward___boxed(lean_object* v_x_171_, lean_object* v_x_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_Elab_Do_elabDoForward(v_x_171_, v_x_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_);
lean_dec(v_a_178_);
lean_dec_ref(v_a_177_);
lean_dec(v_a_176_);
lean_dec_ref(v_a_175_);
lean_dec(v_a_174_);
lean_dec_ref(v_a_173_);
lean_dec(v_x_172_);
lean_dec(v_x_171_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0(lean_object* v_00_u03b1_181_, lean_object* v_msg_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg(v_msg_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___boxed(lean_object* v_00_u03b1_191_, lean_object* v_msg_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0(v_00_u03b1_191_, v_msg_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1(lean_object* v_msgData_201_, lean_object* v_macroStack_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___redArg(v_msgData_201_, v_macroStack_202_, v___y_207_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1___boxed(lean_object* v_msgData_211_, lean_object* v_macroStack_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__1(v_msgData_211_, v_macroStack_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1(){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_239_ = l_Lean_Elab_Term_termElabAttribute;
v___x_240_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__4));
v___x_241_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___closed__8));
v___x_242_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoForward___boxed), 9, 0);
v___x_243_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_239_, v___x_240_, v___x_241_, v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1___boxed(lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_elabDoForward___regBuiltin_Lean_Elab_Do_elabDoForward__1();
return v_res_245_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__0));
v___x_248_ = l_Lean_stringToMessageData(v___x_247_);
return v___x_248_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__3(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__2));
v___x_251_ = l_Lean_stringToMessageData(v___x_250_);
return v___x_251_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__5(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__4));
v___x_254_ = l_Lean_stringToMessageData(v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint(lean_object* v_headApp_255_, lean_object* v_reason_256_){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_257_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1);
v___x_258_ = l_Lean_MessageData_ofSyntax(v_headApp_255_);
v___x_259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_257_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
v___x_260_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__3, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__3);
v___x_261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_259_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
v___x_262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v_reason_256_);
v___x_263_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__5, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__5_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__5);
v___x_264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_262_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(lean_object* v_e_265_, lean_object* v___y_266_){
_start:
{
uint8_t v___x_268_; 
v___x_268_ = l_Lean_Expr_hasMVar(v_e_265_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; 
v___x_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_269_, 0, v_e_265_);
return v___x_269_;
}
else
{
lean_object* v___x_270_; lean_object* v_mctx_271_; lean_object* v___x_272_; lean_object* v_fst_273_; lean_object* v_snd_274_; lean_object* v___x_275_; lean_object* v_cache_276_; lean_object* v_zetaDeltaFVarIds_277_; lean_object* v_postponed_278_; lean_object* v_diag_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_288_; 
v___x_270_ = lean_st_ref_get(v___y_266_);
v_mctx_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc_ref(v_mctx_271_);
lean_dec(v___x_270_);
v___x_272_ = l_Lean_instantiateMVarsCore(v_mctx_271_, v_e_265_);
v_fst_273_ = lean_ctor_get(v___x_272_, 0);
lean_inc(v_fst_273_);
v_snd_274_ = lean_ctor_get(v___x_272_, 1);
lean_inc(v_snd_274_);
lean_dec_ref(v___x_272_);
v___x_275_ = lean_st_ref_take(v___y_266_);
v_cache_276_ = lean_ctor_get(v___x_275_, 1);
v_zetaDeltaFVarIds_277_ = lean_ctor_get(v___x_275_, 2);
v_postponed_278_ = lean_ctor_get(v___x_275_, 3);
v_diag_279_ = lean_ctor_get(v___x_275_, 4);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_288_ == 0)
{
lean_object* v_unused_289_; 
v_unused_289_ = lean_ctor_get(v___x_275_, 0);
lean_dec(v_unused_289_);
v___x_281_ = v___x_275_;
v_isShared_282_ = v_isSharedCheck_288_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_diag_279_);
lean_inc(v_postponed_278_);
lean_inc(v_zetaDeltaFVarIds_277_);
lean_inc(v_cache_276_);
lean_dec(v___x_275_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_288_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 0, v_snd_274_);
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_snd_274_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_cache_276_);
lean_ctor_set(v_reuseFailAlloc_287_, 2, v_zetaDeltaFVarIds_277_);
lean_ctor_set(v_reuseFailAlloc_287_, 3, v_postponed_278_);
lean_ctor_set(v_reuseFailAlloc_287_, 4, v_diag_279_);
v___x_284_ = v_reuseFailAlloc_287_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = lean_st_ref_put(v___y_266_, v___x_284_);
v___x_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_286_, 0, v_fst_273_);
return v___x_286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg___boxed(lean_object* v_e_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_e_290_, v___y_291_);
lean_dec(v___y_291_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1(lean_object* v_e_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_e_294_, v___y_296_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___boxed(lean_object* v_e_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1(v_e_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___lam__0(lean_object* v_k_308_, lean_object* v_b_309_, lean_object* v_c_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v___x_316_; 
lean_inc(v___y_314_);
lean_inc_ref(v___y_313_);
lean_inc(v___y_312_);
lean_inc_ref(v___y_311_);
v___x_316_ = lean_apply_7(v_k_308_, v_b_309_, v_c_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, lean_box(0));
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___lam__0___boxed(lean_object* v_k_317_, lean_object* v_b_318_, lean_object* v_c_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___lam__0(v_k_317_, v_b_318_, v_c_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg(lean_object* v_type_326_, lean_object* v_k_327_, uint8_t v_cleanupAnnotations_328_, uint8_t v_whnfType_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v___f_335_; lean_object* v___x_336_; 
v___f_335_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_335_, 0, v_k_327_);
v___x_336_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_326_, v___f_335_, v_cleanupAnnotations_328_, v_whnfType_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
v_a_337_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_344_ == 0)
{
v___x_339_ = v___x_336_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_336_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_a_337_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
else
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
v_a_345_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_336_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_336_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg___boxed(lean_object* v_type_353_, lean_object* v_k_354_, lean_object* v_cleanupAnnotations_355_, lean_object* v_whnfType_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_362_; uint8_t v_whnfType_boxed_363_; lean_object* v_res_364_; 
v_cleanupAnnotations_boxed_362_ = lean_unbox(v_cleanupAnnotations_355_);
v_whnfType_boxed_363_ = lean_unbox(v_whnfType_356_);
v_res_364_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg(v_type_353_, v_k_354_, v_cleanupAnnotations_boxed_362_, v_whnfType_boxed_363_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4(lean_object* v_00_u03b1_365_, lean_object* v_type_366_, lean_object* v_k_367_, uint8_t v_cleanupAnnotations_368_, uint8_t v_whnfType_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg(v_type_366_, v_k_367_, v_cleanupAnnotations_368_, v_whnfType_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___boxed(lean_object* v_00_u03b1_376_, lean_object* v_type_377_, lean_object* v_k_378_, lean_object* v_cleanupAnnotations_379_, lean_object* v_whnfType_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_386_; uint8_t v_whnfType_boxed_387_; lean_object* v_res_388_; 
v_cleanupAnnotations_boxed_386_ = lean_unbox(v_cleanupAnnotations_379_);
v_whnfType_boxed_387_ = lean_unbox(v_whnfType_380_);
v_res_388_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4(v_00_u03b1_376_, v_type_377_, v_k_378_, v_cleanupAnnotations_boxed_386_, v_whnfType_boxed_387_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(lean_object* v_msg_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_ref_395_; lean_object* v___x_396_; lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_405_; 
v_ref_395_ = lean_ctor_get(v___y_392_, 2);
v___x_396_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0(v_msg_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
v_a_397_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_405_ == 0)
{
v___x_399_ = v___x_396_;
v_isShared_400_ = v_isSharedCheck_405_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_396_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_405_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_401_; lean_object* v___x_403_; 
lean_inc(v_ref_395_);
v___x_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_401_, 0, v_ref_395_);
lean_ctor_set(v___x_401_, 1, v_a_397_);
if (v_isShared_400_ == 0)
{
lean_ctor_set_tag(v___x_399_, 1);
lean_ctor_set(v___x_399_, 0, v___x_401_);
v___x_403_ = v___x_399_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_401_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg___boxed(lean_object* v_msg_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v_msg_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0(lean_object* v_headApp_413_, lean_object* v_00_u03b1_414_, lean_object* v_reason_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint(v_headApp_413_, v_reason_415_);
v___x_422_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v___x_421_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0___boxed(lean_object* v_headApp_423_, lean_object* v_00_u03b1_424_, lean_object* v_reason_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0(v_headApp_423_, v_00_u03b1_424_, v_reason_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
return v_res_431_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0(lean_object* v_arg_432_, lean_object* v_x_433_){
_start:
{
lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_434_ = l_Lean_Expr_mvarId_x21(v_arg_432_);
v___x_435_ = l_Lean_instBEqMVarId_beq(v_x_433_, v___x_434_);
lean_dec(v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0___boxed(lean_object* v_arg_436_, lean_object* v_x_437_){
_start:
{
uint8_t v_res_438_; lean_object* v_r_439_; 
v_res_438_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0(v_arg_436_, v_x_437_);
lean_dec(v_x_437_);
lean_dec_ref(v_arg_436_);
v_r_439_ = lean_box(v_res_438_);
return v_r_439_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__0));
v___x_442_ = l_Lean_stringToMessageData(v___x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4(lean_object* v_arg_443_, lean_object* v_headApp_444_, lean_object* v_as_445_, size_t v_sz_446_, size_t v_i_447_, lean_object* v_b_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v_a_455_; uint8_t v___x_459_; 
v___x_459_ = lean_usize_dec_lt(v_i_447_, v_sz_446_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; 
lean_dec(v_headApp_444_);
lean_dec_ref(v_arg_443_);
v___x_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_460_, 0, v_b_448_);
return v___x_460_;
}
else
{
lean_object* v___f_461_; lean_object* v___x_462_; lean_object* v_a_463_; lean_object* v___x_464_; 
lean_inc_ref(v_arg_443_);
v___f_461_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_461_, 0, v_arg_443_);
v___x_462_ = lean_box(0);
v_a_463_ = lean_array_uget_borrowed(v_as_445_, v_i_447_);
lean_inc(v___y_452_);
lean_inc_ref(v___y_451_);
lean_inc(v___y_450_);
lean_inc_ref(v___y_449_);
lean_inc(v_a_463_);
v___x_464_ = lean_infer_type(v_a_463_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v___x_466_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc_n(v_a_465_, 2);
lean_dec_ref_known(v___x_464_, 1);
v___x_466_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_a_465_, v___y_450_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v_a_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_a_467_);
lean_dec_ref_known(v___x_466_, 1);
v___x_468_ = lean_box(0);
v___x_469_ = l_Lean_FindMVar_main(v___f_461_, v_a_467_, v___x_468_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_dec(v_a_465_);
v_a_455_ = v___x_462_;
goto v___jp_454_;
}
else
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
lean_dec_ref_known(v___x_469_, 1);
v___x_470_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1);
v___x_471_ = l_Lean_MessageData_ofExpr(v_a_465_);
v___x_472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_470_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
v___x_473_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1);
v___x_474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_472_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
lean_inc(v_headApp_444_);
v___x_475_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint(v_headApp_444_, v___x_474_);
v___x_476_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v___x_475_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_dec_ref_known(v___x_476_, 1);
v_a_455_ = v___x_462_;
goto v___jp_454_;
}
else
{
lean_dec(v_headApp_444_);
lean_dec_ref(v_arg_443_);
return v___x_476_;
}
}
}
else
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_484_; 
lean_dec(v_a_465_);
lean_dec_ref(v___f_461_);
lean_dec(v_headApp_444_);
lean_dec_ref(v_arg_443_);
v_a_477_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_484_ == 0)
{
v___x_479_ = v___x_466_;
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_466_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_a_477_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
else
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
lean_dec_ref(v___f_461_);
lean_dec(v_headApp_444_);
lean_dec_ref(v_arg_443_);
v_a_485_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_464_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_464_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
v___jp_454_:
{
size_t v___x_456_; size_t v___x_457_; 
v___x_456_ = ((size_t)1ULL);
v___x_457_ = lean_usize_add(v_i_447_, v___x_456_);
v_i_447_ = v___x_457_;
v_b_448_ = v_a_455_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___boxed(lean_object* v_arg_493_, lean_object* v_headApp_494_, lean_object* v_as_495_, lean_object* v_sz_496_, lean_object* v_i_497_, lean_object* v_b_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
size_t v_sz_boxed_504_; size_t v_i_boxed_505_; lean_object* v_res_506_; 
v_sz_boxed_504_ = lean_unbox_usize(v_sz_496_);
lean_dec(v_sz_496_);
v_i_boxed_505_ = lean_unbox_usize(v_i_497_);
lean_dec(v_i_497_);
v_res_506_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4(v_arg_493_, v_headApp_494_, v_as_495_, v_sz_boxed_504_, v_i_boxed_505_, v_b_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
lean_dec_ref(v_as_495_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3(lean_object* v_arg_507_, lean_object* v_headApp_508_, lean_object* v_as_509_, size_t v_sz_510_, size_t v_i_511_, lean_object* v_b_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v_a_519_; uint8_t v___x_523_; 
v___x_523_ = lean_usize_dec_lt(v_i_511_, v_sz_510_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; 
lean_dec(v_headApp_508_);
lean_dec_ref(v_arg_507_);
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v_b_512_);
return v___x_524_;
}
else
{
lean_object* v___f_525_; lean_object* v___x_526_; lean_object* v_a_527_; lean_object* v___x_528_; 
lean_inc_ref(v_arg_507_);
v___f_525_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_525_, 0, v_arg_507_);
v___x_526_ = lean_box(0);
v_a_527_ = lean_array_uget_borrowed(v_as_509_, v_i_511_);
lean_inc(v___y_516_);
lean_inc_ref(v___y_515_);
lean_inc(v___y_514_);
lean_inc_ref(v___y_513_);
lean_inc(v_a_527_);
v___x_528_ = lean_infer_type(v_a_527_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; lean_object* v___x_530_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc_n(v_a_529_, 2);
lean_dec_ref_known(v___x_528_, 1);
v___x_530_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_a_529_, v___y_514_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_a_531_);
lean_dec_ref_known(v___x_530_, 1);
v___x_532_ = lean_box(0);
v___x_533_ = l_Lean_FindMVar_main(v___f_525_, v_a_531_, v___x_532_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_dec(v_a_529_);
v_a_519_ = v___x_526_;
goto v___jp_518_;
}
else
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
lean_dec_ref_known(v___x_533_, 1);
v___x_534_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4___closed__1);
v___x_535_ = l_Lean_MessageData_ofExpr(v_a_529_);
v___x_536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_534_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1);
v___x_538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_536_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
lean_inc(v_headApp_508_);
v___x_539_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint(v_headApp_508_, v___x_538_);
v___x_540_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v___x_539_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_dec_ref_known(v___x_540_, 1);
v_a_519_ = v___x_526_;
goto v___jp_518_;
}
else
{
lean_dec(v_headApp_508_);
lean_dec_ref(v_arg_507_);
return v___x_540_;
}
}
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_dec(v_a_529_);
lean_dec_ref(v___f_525_);
lean_dec(v_headApp_508_);
lean_dec_ref(v_arg_507_);
v_a_541_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_530_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_530_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
else
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
lean_dec_ref(v___f_525_);
lean_dec(v_headApp_508_);
lean_dec_ref(v_arg_507_);
v_a_549_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_528_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_528_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
v___jp_518_:
{
size_t v___x_520_; size_t v___x_521_; lean_object* v___x_522_; 
v___x_520_ = ((size_t)1ULL);
v___x_521_ = lean_usize_add(v_i_511_, v___x_520_);
v___x_522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3_spec__4(v_arg_507_, v_headApp_508_, v_as_509_, v_sz_510_, v___x_521_, v_a_519_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
return v___x_522_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3___boxed(lean_object* v_arg_557_, lean_object* v_headApp_558_, lean_object* v_as_559_, lean_object* v_sz_560_, lean_object* v_i_561_, lean_object* v_b_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
size_t v_sz_boxed_568_; size_t v_i_boxed_569_; lean_object* v_res_570_; 
v_sz_boxed_568_ = lean_unbox_usize(v_sz_560_);
lean_dec(v_sz_560_);
v_i_boxed_569_ = lean_unbox_usize(v_i_561_);
lean_dec(v_i_561_);
v_res_570_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3(v_arg_557_, v_headApp_558_, v_as_559_, v_sz_boxed_568_, v_i_boxed_569_, v_b_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec_ref(v_as_559_);
return v_res_570_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__1(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__0));
v___x_573_ = l_Lean_stringToMessageData(v___x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1(lean_object* v_arg_574_, lean_object* v_headApp_575_, lean_object* v_a_576_, lean_object* v_reject_577_, lean_object* v_args_578_, lean_object* v_body_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v___x_598_; lean_object* v_a_599_; lean_object* v___x_600_; 
v___x_598_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_body_579_, v___y_581_);
v_a_599_ = lean_ctor_get(v___x_598_, 0);
lean_inc(v_a_599_);
lean_dec_ref(v___x_598_);
v___x_600_ = l_Lean_Meta_whnfD(v_a_599_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; lean_object* v___x_602_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_a_601_);
lean_dec_ref_known(v___x_600_, 1);
v___x_602_ = l_Lean_Meta_isExprDefEq(v_a_576_, v_a_601_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; uint8_t v___x_604_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_a_603_);
lean_dec_ref_known(v___x_602_, 1);
v___x_604_ = lean_unbox(v_a_603_);
lean_dec(v_a_603_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___closed__1);
lean_inc(v___y_583_);
lean_inc_ref(v___y_582_);
lean_inc(v___y_581_);
lean_inc_ref(v___y_580_);
v___x_606_ = lean_apply_7(v_reject_577_, lean_box(0), v___x_605_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, lean_box(0));
if (lean_obj_tag(v___x_606_) == 0)
{
lean_dec_ref_known(v___x_606_, 1);
goto v___jp_585_;
}
else
{
lean_dec(v_headApp_575_);
lean_dec_ref(v_arg_574_);
return v___x_606_;
}
}
else
{
lean_dec_ref(v_reject_577_);
goto v___jp_585_;
}
}
else
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
lean_dec_ref(v_reject_577_);
lean_dec(v_headApp_575_);
lean_dec_ref(v_arg_574_);
v_a_607_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v___x_602_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_602_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_607_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
else
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
lean_dec_ref(v_reject_577_);
lean_dec_ref(v_a_576_);
lean_dec(v_headApp_575_);
lean_dec_ref(v_arg_574_);
v_a_615_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___x_600_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_600_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
v___jp_585_:
{
lean_object* v___x_586_; size_t v_sz_587_; size_t v___x_588_; lean_object* v___x_589_; 
v___x_586_ = lean_box(0);
v_sz_587_ = lean_array_size(v_args_578_);
v___x_588_ = ((size_t)0ULL);
v___x_589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__3(v_arg_574_, v_headApp_575_, v_args_578_, v_sz_587_, v___x_588_, v___x_586_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_596_ == 0)
{
lean_object* v_unused_597_; 
v_unused_597_ = lean_ctor_get(v___x_589_, 0);
lean_dec(v_unused_597_);
v___x_591_ = v___x_589_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_dec(v___x_589_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 0, v___x_586_);
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_586_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
else
{
return v___x_589_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___boxed(lean_object* v_arg_623_, lean_object* v_headApp_624_, lean_object* v_a_625_, lean_object* v_reject_626_, lean_object* v_args_627_, lean_object* v_body_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1(v_arg_623_, v_headApp_624_, v_a_625_, v_reject_626_, v_args_627_, v_body_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec_ref(v_args_627_);
return v_res_634_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__0));
v___x_637_ = l_Lean_stringToMessageData(v___x_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2(lean_object* v_forwarded_638_, lean_object* v_arg_639_, lean_object* v_headApp_640_, lean_object* v_as_641_, size_t v_sz_642_, size_t v_i_643_, lean_object* v_b_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
lean_object* v_a_651_; uint8_t v___x_655_; 
v___x_655_ = lean_usize_dec_lt(v_i_643_, v_sz_642_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; 
lean_dec(v_headApp_640_);
lean_dec_ref(v_arg_639_);
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v_b_644_);
return v___x_656_;
}
else
{
lean_object* v_a_657_; lean_object* v_fst_658_; lean_object* v_snd_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_719_; 
v_a_657_ = lean_array_uget(v_as_641_, v_i_643_);
v_fst_658_ = lean_ctor_get(v_a_657_, 0);
v_snd_659_ = lean_ctor_get(v_a_657_, 1);
v_isSharedCheck_719_ = !lean_is_exclusive(v_a_657_);
if (v_isSharedCheck_719_ == 0)
{
v___x_661_ = v_a_657_;
v_isShared_662_ = v_isSharedCheck_719_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_snd_659_);
lean_inc(v_fst_658_);
lean_dec(v_a_657_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_719_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___f_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
lean_inc_ref(v_arg_639_);
v___f_663_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_663_, 0, v_arg_639_);
v___x_664_ = lean_box(0);
v___x_665_ = l_Lean_Expr_fvarId_x21(v_fst_658_);
lean_dec(v_fst_658_);
v___x_666_ = l_Lean_FVarId_getDecl___redArg(v___x_665_, v___y_645_, v___y_647_, v___y_648_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; uint8_t v___x_668_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
lean_dec_ref_known(v___x_666_, 1);
v___x_668_ = l_Lean_LocalDecl_binderInfo(v_a_667_);
lean_dec(v_a_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; 
v___x_669_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_snd_659_, v___y_646_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; uint8_t v___x_671_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_a_670_);
lean_dec_ref_known(v___x_669_, 1);
v___x_671_ = lean_expr_eqv(v_a_670_, v_forwarded_638_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; 
lean_inc(v___y_648_);
lean_inc_ref(v___y_647_);
lean_inc(v___y_646_);
lean_inc_ref(v___y_645_);
v___x_672_ = lean_infer_type(v_a_670_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v___x_674_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc_n(v_a_673_, 2);
lean_dec_ref_known(v___x_672_, 1);
v___x_674_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_a_673_, v___y_646_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_a_675_);
lean_dec_ref_known(v___x_674_, 1);
v___x_676_ = lean_box(0);
v___x_677_ = l_Lean_FindMVar_main(v___f_663_, v_a_675_, v___x_676_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_dec(v_a_673_);
lean_del_object(v___x_661_);
v_a_651_ = v___x_664_;
goto v___jp_650_;
}
else
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_681_; 
lean_dec_ref_known(v___x_677_, 1);
v___x_678_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1);
v___x_679_ = l_Lean_MessageData_ofExpr(v_a_673_);
if (v_isShared_662_ == 0)
{
lean_ctor_set_tag(v___x_661_, 7);
lean_ctor_set(v___x_661_, 1, v___x_679_);
lean_ctor_set(v___x_661_, 0, v___x_678_);
v___x_681_ = v___x_661_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v___x_678_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v___x_679_);
v___x_681_ = v_reuseFailAlloc_686_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_682_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1);
v___x_683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_681_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
lean_inc(v_headApp_640_);
v___x_684_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint(v_headApp_640_, v___x_683_);
v___x_685_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v___x_684_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_dec_ref_known(v___x_685_, 1);
v_a_651_ = v___x_664_;
goto v___jp_650_;
}
else
{
lean_dec(v_headApp_640_);
lean_dec_ref(v_arg_639_);
return v___x_685_;
}
}
}
}
else
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_694_; 
lean_dec(v_a_673_);
lean_dec_ref(v___f_663_);
lean_del_object(v___x_661_);
lean_dec(v_headApp_640_);
lean_dec_ref(v_arg_639_);
v_a_687_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_694_ == 0)
{
v___x_689_ = v___x_674_;
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_674_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_690_ == 0)
{
v___x_692_ = v___x_689_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_a_687_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
else
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_702_; 
lean_dec_ref(v___f_663_);
lean_del_object(v___x_661_);
lean_dec(v_headApp_640_);
lean_dec_ref(v_arg_639_);
v_a_695_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_702_ == 0)
{
v___x_697_ = v___x_672_;
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_672_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_698_ == 0)
{
v___x_700_ = v___x_697_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_a_695_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
else
{
lean_dec(v_a_670_);
lean_dec_ref(v___f_663_);
lean_del_object(v___x_661_);
v_a_651_ = v___x_664_;
goto v___jp_650_;
}
}
else
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
lean_dec_ref(v___f_663_);
lean_del_object(v___x_661_);
lean_dec(v_headApp_640_);
lean_dec_ref(v_arg_639_);
v_a_703_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_669_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_669_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
else
{
lean_dec_ref(v___f_663_);
lean_del_object(v___x_661_);
lean_dec(v_snd_659_);
v_a_651_ = v___x_664_;
goto v___jp_650_;
}
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
lean_dec_ref(v___f_663_);
lean_del_object(v___x_661_);
lean_dec(v_snd_659_);
lean_dec(v_headApp_640_);
lean_dec_ref(v_arg_639_);
v_a_711_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_666_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_666_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
}
v___jp_650_:
{
size_t v___x_652_; size_t v___x_653_; 
v___x_652_ = ((size_t)1ULL);
v___x_653_ = lean_usize_add(v_i_643_, v___x_652_);
v_i_643_ = v___x_653_;
v_b_644_ = v_a_651_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___boxed(lean_object* v_forwarded_720_, lean_object* v_arg_721_, lean_object* v_headApp_722_, lean_object* v_as_723_, lean_object* v_sz_724_, lean_object* v_i_725_, lean_object* v_b_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
size_t v_sz_boxed_732_; size_t v_i_boxed_733_; lean_object* v_res_734_; 
v_sz_boxed_732_ = lean_unbox_usize(v_sz_724_);
lean_dec(v_sz_724_);
v_i_boxed_733_ = lean_unbox_usize(v_i_725_);
lean_dec(v_i_725_);
v_res_734_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2(v_forwarded_720_, v_arg_721_, v_headApp_722_, v_as_723_, v_sz_boxed_732_, v_i_boxed_733_, v_b_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec_ref(v_as_723_);
lean_dec_ref(v_forwarded_720_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2(lean_object* v_forwarded_735_, lean_object* v_arg_736_, lean_object* v_headApp_737_, lean_object* v_as_738_, size_t v_sz_739_, size_t v_i_740_, lean_object* v_b_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v_a_748_; uint8_t v___x_752_; 
v___x_752_ = lean_usize_dec_lt(v_i_740_, v_sz_739_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; 
lean_dec(v_headApp_737_);
lean_dec_ref(v_arg_736_);
v___x_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_753_, 0, v_b_741_);
return v___x_753_;
}
else
{
lean_object* v_a_754_; lean_object* v_fst_755_; lean_object* v_snd_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_816_; 
v_a_754_ = lean_array_uget(v_as_738_, v_i_740_);
v_fst_755_ = lean_ctor_get(v_a_754_, 0);
v_snd_756_ = lean_ctor_get(v_a_754_, 1);
v_isSharedCheck_816_ = !lean_is_exclusive(v_a_754_);
if (v_isSharedCheck_816_ == 0)
{
v___x_758_ = v_a_754_;
v_isShared_759_ = v_isSharedCheck_816_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_snd_756_);
lean_inc(v_fst_755_);
lean_dec(v_a_754_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_816_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___f_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
lean_inc_ref(v_arg_736_);
v___f_760_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_760_, 0, v_arg_736_);
v___x_761_ = lean_box(0);
v___x_762_ = l_Lean_Expr_fvarId_x21(v_fst_755_);
lean_dec(v_fst_755_);
v___x_763_ = l_Lean_FVarId_getDecl___redArg(v___x_762_, v___y_742_, v___y_744_, v___y_745_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; uint8_t v___x_765_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_763_, 1);
v___x_765_ = l_Lean_LocalDecl_binderInfo(v_a_764_);
lean_dec(v_a_764_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_snd_756_, v___y_743_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; uint8_t v___x_768_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
lean_dec_ref_known(v___x_766_, 1);
v___x_768_ = lean_expr_eqv(v_a_767_, v_forwarded_735_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; 
lean_inc(v___y_745_);
lean_inc_ref(v___y_744_);
lean_inc(v___y_743_);
lean_inc_ref(v___y_742_);
v___x_769_ = lean_infer_type(v_a_767_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___x_771_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc_n(v_a_770_, 2);
lean_dec_ref_known(v___x_769_, 1);
v___x_771_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_a_770_, v___y_743_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_a_772_);
lean_dec_ref_known(v___x_771_, 1);
v___x_773_ = lean_box(0);
v___x_774_ = l_Lean_FindMVar_main(v___f_760_, v_a_772_, v___x_773_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_dec(v_a_770_);
lean_del_object(v___x_758_);
v_a_748_ = v___x_761_;
goto v___jp_747_;
}
else
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_778_; 
lean_dec_ref_known(v___x_774_, 1);
v___x_775_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2___closed__1);
v___x_776_ = l_Lean_MessageData_ofExpr(v_a_770_);
if (v_isShared_759_ == 0)
{
lean_ctor_set_tag(v___x_758_, 7);
lean_ctor_set(v___x_758_, 1, v___x_776_);
lean_ctor_set(v___x_758_, 0, v___x_775_);
v___x_778_ = v___x_758_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_775_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v___x_776_);
v___x_778_ = v_reuseFailAlloc_783_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_779_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint___closed__1);
v___x_780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_778_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
lean_inc(v_headApp_737_);
v___x_781_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_forwardHint(v_headApp_737_, v___x_780_);
v___x_782_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v___x_781_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_dec_ref_known(v___x_782_, 1);
v_a_748_ = v___x_761_;
goto v___jp_747_;
}
else
{
lean_dec(v_headApp_737_);
lean_dec_ref(v_arg_736_);
return v___x_782_;
}
}
}
}
else
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
lean_dec(v_a_770_);
lean_dec_ref(v___f_760_);
lean_del_object(v___x_758_);
lean_dec(v_headApp_737_);
lean_dec_ref(v_arg_736_);
v_a_784_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_771_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_771_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
else
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
lean_dec_ref(v___f_760_);
lean_del_object(v___x_758_);
lean_dec(v_headApp_737_);
lean_dec_ref(v_arg_736_);
v_a_792_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_769_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_769_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
else
{
lean_dec(v_a_767_);
lean_dec_ref(v___f_760_);
lean_del_object(v___x_758_);
v_a_748_ = v___x_761_;
goto v___jp_747_;
}
}
else
{
lean_object* v_a_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_dec_ref(v___f_760_);
lean_del_object(v___x_758_);
lean_dec(v_headApp_737_);
lean_dec_ref(v_arg_736_);
v_a_800_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_766_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_a_800_);
lean_dec(v___x_766_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_a_800_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
else
{
lean_dec_ref(v___f_760_);
lean_del_object(v___x_758_);
lean_dec(v_snd_756_);
v_a_748_ = v___x_761_;
goto v___jp_747_;
}
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec_ref(v___f_760_);
lean_del_object(v___x_758_);
lean_dec(v_snd_756_);
lean_dec(v_headApp_737_);
lean_dec_ref(v_arg_736_);
v_a_808_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_763_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_763_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
}
v___jp_747_:
{
size_t v___x_749_; size_t v___x_750_; lean_object* v___x_751_; 
v___x_749_ = ((size_t)1ULL);
v___x_750_ = lean_usize_add(v_i_740_, v___x_749_);
v___x_751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2_spec__2(v_forwarded_735_, v_arg_736_, v_headApp_737_, v_as_738_, v_sz_739_, v___x_750_, v_a_748_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
return v___x_751_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2___boxed(lean_object* v_forwarded_817_, lean_object* v_arg_818_, lean_object* v_headApp_819_, lean_object* v_as_820_, lean_object* v_sz_821_, lean_object* v_i_822_, lean_object* v_b_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
size_t v_sz_boxed_829_; size_t v_i_boxed_830_; lean_object* v_res_831_; 
v_sz_boxed_829_ = lean_unbox_usize(v_sz_821_);
lean_dec(v_sz_821_);
v_i_boxed_830_ = lean_unbox_usize(v_i_822_);
lean_dec(v_i_822_);
v_res_831_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2(v_forwarded_817_, v_arg_818_, v_headApp_819_, v_as_820_, v_sz_boxed_829_, v_i_boxed_830_, v_b_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec_ref(v_as_820_);
lean_dec_ref(v_forwarded_817_);
return v_res_831_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___closed__0(void){
_start:
{
lean_object* v___x_832_; lean_object* v_dummy_833_; 
v___x_832_ = lean_box(0);
v_dummy_833_ = l_Lean_Expr_sort___override(v___x_832_);
return v_dummy_833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2(lean_object* v_probeExpr_834_, lean_object* v_forwarded_835_, lean_object* v_arg_836_, lean_object* v_headApp_837_, lean_object* v_fvars_838_, lean_object* v_x_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v_dummy_845_; lean_object* v_nargs_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; size_t v_sz_853_; size_t v___x_854_; lean_object* v___x_855_; 
v_dummy_845_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___closed__0, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___closed__0_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___closed__0);
v_nargs_846_ = l_Lean_Expr_getAppNumArgs(v_probeExpr_834_);
lean_inc(v_nargs_846_);
v___x_847_ = lean_mk_array(v_nargs_846_, v_dummy_845_);
v___x_848_ = lean_unsigned_to_nat(1u);
v___x_849_ = lean_nat_sub(v_nargs_846_, v___x_848_);
lean_dec(v_nargs_846_);
v___x_850_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_probeExpr_834_, v___x_847_, v___x_849_);
v___x_851_ = l_Array_zip___redArg(v_fvars_838_, v___x_850_);
lean_dec_ref(v___x_850_);
v___x_852_ = lean_box(0);
v_sz_853_ = lean_array_size(v___x_851_);
v___x_854_ = ((size_t)0ULL);
v___x_855_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__2(v_forwarded_835_, v_arg_836_, v_headApp_837_, v___x_851_, v_sz_853_, v___x_854_, v___x_852_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
lean_dec_ref(v___x_851_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_862_ == 0)
{
lean_object* v_unused_863_; 
v_unused_863_ = lean_ctor_get(v___x_855_, 0);
lean_dec(v_unused_863_);
v___x_857_ = v___x_855_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_dec(v___x_855_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_852_);
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_852_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
else
{
return v___x_855_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___boxed(lean_object* v_probeExpr_864_, lean_object* v_forwarded_865_, lean_object* v_arg_866_, lean_object* v_headApp_867_, lean_object* v_fvars_868_, lean_object* v_x_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2(v_probeExpr_864_, v_forwarded_865_, v_arg_866_, v_headApp_867_, v_fvars_868_, v_x_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec_ref(v_x_869_);
lean_dec_ref(v_fvars_868_);
lean_dec_ref(v_forwarded_865_);
return v_res_875_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__1(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__0));
v___x_878_ = l_Lean_stringToMessageData(v___x_877_);
return v___x_878_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__3(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__2));
v___x_881_ = l_Lean_stringToMessageData(v___x_880_);
return v___x_881_;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__5(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = ((lean_object*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__4));
v___x_884_ = l_Lean_stringToMessageData(v___x_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder(lean_object* v_headApp_885_, lean_object* v_forwarded_886_, lean_object* v_probeExpr_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_reject_893_; lean_object* v___x_894_; 
lean_inc(v_headApp_885_);
v_reject_893_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0___boxed), 8, 1);
lean_closure_set(v_reject_893_, 0, v_headApp_885_);
lean_inc(v_a_891_);
lean_inc_ref(v_a_890_);
lean_inc(v_a_889_);
lean_inc_ref(v_a_888_);
lean_inc_ref(v_probeExpr_887_);
v___x_894_ = lean_infer_type(v_probeExpr_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_896_; lean_object* v_a_897_; lean_object* v___x_898_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_a_895_);
lean_dec_ref_known(v___x_894_, 1);
v___x_896_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__1___redArg(v_a_895_, v_a_889_);
v_a_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_a_897_);
lean_dec_ref(v___x_896_);
v___x_898_ = l_Lean_Meta_whnfD(v_a_897_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_a_899_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_a_899_);
lean_dec_ref_known(v___x_898_, 1);
if (lean_obj_tag(v_a_899_) == 5)
{
lean_object* v_arg_900_; lean_object* v___f_901_; lean_object* v___f_902_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; uint8_t v___x_932_; 
v_arg_900_ = lean_ctor_get(v_a_899_, 1);
lean_inc_ref_n(v_arg_900_, 3);
lean_inc_n(v_headApp_885_, 2);
v___f_901_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__1___boxed), 11, 4);
lean_closure_set(v___f_901_, 0, v_arg_900_);
lean_closure_set(v___f_901_, 1, v_headApp_885_);
lean_closure_set(v___f_901_, 2, v_a_899_);
lean_closure_set(v___f_901_, 3, v_reject_893_);
lean_inc_ref(v_forwarded_886_);
lean_inc_ref(v_probeExpr_887_);
v___f_902_ = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__2___boxed), 11, 4);
lean_closure_set(v___f_902_, 0, v_probeExpr_887_);
lean_closure_set(v___f_902_, 1, v_forwarded_886_);
lean_closure_set(v___f_902_, 2, v_arg_900_);
lean_closure_set(v___f_902_, 3, v_headApp_885_);
v___x_932_ = l_Lean_Expr_isMVar(v_arg_900_);
lean_dec_ref(v_arg_900_);
if (v___x_932_ == 0)
{
lean_object* v___x_933_; lean_object* v___x_934_; 
lean_dec_ref(v___f_902_);
lean_dec_ref(v___f_901_);
lean_dec_ref(v_probeExpr_887_);
lean_dec_ref(v_forwarded_886_);
v___x_933_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__1, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__1_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__1);
v___x_934_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0(v_headApp_885_, lean_box(0), v___x_933_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
return v___x_934_;
}
else
{
lean_dec(v_headApp_885_);
v___y_904_ = v_a_888_;
v___y_905_ = v_a_889_;
v___y_906_ = v_a_890_;
v___y_907_ = v_a_891_;
goto v___jp_903_;
}
v___jp_903_:
{
lean_object* v___x_908_; 
lean_inc(v___y_907_);
lean_inc_ref(v___y_906_);
lean_inc(v___y_905_);
lean_inc_ref(v___y_904_);
v___x_908_ = lean_infer_type(v_forwarded_886_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; uint8_t v___x_910_; lean_object* v___x_911_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc(v_a_909_);
lean_dec_ref_known(v___x_908_, 1);
v___x_910_ = 0;
v___x_911_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg(v_a_909_, v___f_901_, v___x_910_, v___x_910_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v___x_912_; lean_object* v___x_913_; 
lean_dec_ref_known(v___x_911_, 1);
v___x_912_ = l_Lean_Expr_getAppFn(v_probeExpr_887_);
lean_dec_ref(v_probeExpr_887_);
lean_inc(v___y_907_);
lean_inc_ref(v___y_906_);
lean_inc(v___y_905_);
lean_inc_ref(v___y_904_);
v___x_913_ = lean_infer_type(v___x_912_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_915_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_914_);
lean_dec_ref_known(v___x_913_, 1);
v___x_915_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__4___redArg(v_a_914_, v___f_902_, v___x_910_, v___x_910_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
return v___x_915_;
}
else
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_dec_ref(v___f_902_);
v_a_916_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_913_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_913_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
else
{
lean_dec_ref(v___f_902_);
lean_dec_ref(v_probeExpr_887_);
return v___x_911_;
}
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec_ref(v___f_902_);
lean_dec_ref(v___f_901_);
lean_dec_ref(v_probeExpr_887_);
v_a_924_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_908_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_908_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
}
else
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
lean_dec_ref(v_reject_893_);
lean_dec_ref(v_probeExpr_887_);
lean_dec_ref(v_forwarded_886_);
v___x_935_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__3, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__3_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__3);
v___x_936_ = l_Lean_MessageData_ofExpr(v_a_899_);
v___x_937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_935_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = lean_obj_once(&l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__5, &l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__5_once, _init_l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___closed__5);
v___x_939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_937_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___lam__0(v_headApp_885_, lean_box(0), v___x_939_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
return v___x_940_;
}
}
else
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
lean_dec_ref(v_reject_893_);
lean_dec_ref(v_probeExpr_887_);
lean_dec_ref(v_forwarded_886_);
lean_dec(v_headApp_885_);
v_a_941_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_898_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_898_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
lean_dec_ref(v_reject_893_);
lean_dec_ref(v_probeExpr_887_);
lean_dec_ref(v_forwarded_886_);
lean_dec(v_headApp_885_);
v_a_949_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_894_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_894_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder___boxed(lean_object* v_headApp_957_, lean_object* v_forwarded_958_, lean_object* v_probeExpr_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder(v_headApp_957_, v_forwarded_958_, v_probeExpr_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_);
lean_dec(v_a_963_);
lean_dec_ref(v_a_962_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0(lean_object* v_00_u03b1_966_, lean_object* v_msg_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___redArg(v_msg_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0___boxed(lean_object* v_00_u03b1_974_, lean_object* v_msg_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Lean_throwError___at___00__private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder_spec__0(v_00_u03b1_974_, v_msg_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___redArg(lean_object* v_e_982_, lean_object* v___y_983_){
_start:
{
uint8_t v___x_985_; 
v___x_985_ = l_Lean_Expr_hasMVar(v_e_982_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; 
v___x_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_986_, 0, v_e_982_);
return v___x_986_;
}
else
{
lean_object* v___x_987_; lean_object* v_mctx_988_; lean_object* v___x_989_; lean_object* v_fst_990_; lean_object* v_snd_991_; lean_object* v___x_992_; lean_object* v_cache_993_; lean_object* v_zetaDeltaFVarIds_994_; lean_object* v_postponed_995_; lean_object* v_diag_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1005_; 
v___x_987_ = lean_st_ref_get(v___y_983_);
v_mctx_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc_ref(v_mctx_988_);
lean_dec(v___x_987_);
v___x_989_ = l_Lean_instantiateMVarsCore(v_mctx_988_, v_e_982_);
v_fst_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_fst_990_);
v_snd_991_ = lean_ctor_get(v___x_989_, 1);
lean_inc(v_snd_991_);
lean_dec_ref(v___x_989_);
v___x_992_ = lean_st_ref_take(v___y_983_);
v_cache_993_ = lean_ctor_get(v___x_992_, 1);
v_zetaDeltaFVarIds_994_ = lean_ctor_get(v___x_992_, 2);
v_postponed_995_ = lean_ctor_get(v___x_992_, 3);
v_diag_996_ = lean_ctor_get(v___x_992_, 4);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1005_ == 0)
{
lean_object* v_unused_1006_; 
v_unused_1006_ = lean_ctor_get(v___x_992_, 0);
lean_dec(v_unused_1006_);
v___x_998_ = v___x_992_;
v_isShared_999_ = v_isSharedCheck_1005_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_diag_996_);
lean_inc(v_postponed_995_);
lean_inc(v_zetaDeltaFVarIds_994_);
lean_inc(v_cache_993_);
lean_dec(v___x_992_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1005_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 0, v_snd_991_);
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_snd_991_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v_cache_993_);
lean_ctor_set(v_reuseFailAlloc_1004_, 2, v_zetaDeltaFVarIds_994_);
lean_ctor_set(v_reuseFailAlloc_1004_, 3, v_postponed_995_);
lean_ctor_set(v_reuseFailAlloc_1004_, 4, v_diag_996_);
v___x_1001_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = lean_st_ref_put(v___y_983_, v___x_1001_);
v___x_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1003_, 0, v_fst_990_);
return v___x_1003_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___redArg___boxed(lean_object* v_e_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___redArg(v_e_1007_, v___y_1008_);
lean_dec(v___y_1008_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1(lean_object* v_e_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___redArg(v_e_1011_, v___y_1015_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___boxed(lean_object* v_e_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1(v_e_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
return v_res_1028_;
}
}
static lean_object* _init_l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__3));
v___x_1038_ = l_String_toRawSubstring_x27(v___x_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0(lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_fst_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v_toCold_1058_; lean_object* v_ref_1059_; lean_object* v_quotContext_1060_; lean_object* v_currMacroScope_1061_; uint8_t v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; lean_object* v___x_1075_; 
v_toCold_1058_ = lean_ctor_get(v___y_1055_, 0);
v_ref_1059_ = lean_ctor_get(v___y_1055_, 2);
v_quotContext_1060_ = lean_ctor_get(v_toCold_1058_, 8);
v_currMacroScope_1061_ = lean_ctor_get(v_toCold_1058_, 9);
v___x_1062_ = 0;
v___x_1063_ = l_Lean_SourceInfo_fromRef(v_ref_1059_, v___x_1062_);
v___x_1064_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__1));
v___x_1065_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__2));
lean_inc_n(v___x_1063_, 3);
v___x_1066_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1063_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = lean_obj_once(&l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__4, &l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__4_once, _init_l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__4);
v___x_1068_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__5));
lean_inc(v_currMacroScope_1061_);
lean_inc(v_quotContext_1060_);
v___x_1069_ = l_Lean_addMacroScope(v_quotContext_1060_, v___x_1068_, v_currMacroScope_1061_);
v___x_1070_ = lean_box(0);
v___x_1071_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1063_);
lean_ctor_set(v___x_1071_, 1, v___x_1067_);
lean_ctor_set(v___x_1071_, 2, v___x_1069_);
lean_ctor_set(v___x_1071_, 3, v___x_1070_);
v___x_1072_ = l_Lean_Syntax_node2(v___x_1063_, v___x_1064_, v___x_1066_, v___x_1071_);
v___x_1073_ = lean_box(0);
v___x_1074_ = 1;
lean_inc(v___x_1072_);
v___x_1075_ = l_Lean_Elab_Term_elabTerm(v___x_1072_, v___x_1073_, v___x_1074_, v___x_1074_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v___y_1055_, v___y_1056_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1076_);
lean_dec_ref_known(v___x_1075_, 1);
v___x_1077_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__7));
v___x_1078_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___closed__9));
lean_inc(v___x_1063_);
v___x_1079_ = l_Lean_Syntax_node1(v___x_1063_, v___x_1078_, v___x_1072_);
v___x_1080_ = l_Lean_Syntax_node2(v___x_1063_, v___x_1077_, v_fst_1054_, v___x_1079_);
v___x_1081_ = l_Lean_Elab_Term_elabTerm(v___x_1080_, v___x_1073_, v___x_1074_, v___x_1074_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v___y_1055_, v___y_1056_);
lean_dec_ref(v___y_1055_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1090_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1084_ = v___x_1081_;
v_isShared_1085_ = v_isSharedCheck_1090_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1081_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1090_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1086_; lean_object* v___x_1088_; 
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v_a_1076_);
lean_ctor_set(v___x_1086_, 1, v_a_1082_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___x_1086_);
v___x_1088_ = v___x_1084_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
lean_dec(v_a_1076_);
v_a_1091_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1081_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1081_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_dec(v___x_1072_);
lean_dec(v___x_1063_);
lean_dec_ref(v___y_1055_);
lean_dec(v_fst_1054_);
v_a_1099_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1075_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1075_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___boxed(lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_fst_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0(v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_fst_1111_, v___y_1112_, v___y_1113_);
lean_dec(v___y_1113_);
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__1(lean_object* v_body_1116_, lean_object* v_cont_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
uint8_t v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = 1;
v___x_1127_ = l_Lean_Elab_Do_elabDoSeq(v_body_1116_, v_cont_1117_, v___x_1126_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__1___boxed(lean_object* v_body_1128_, lean_object* v_cont_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__1(v_body_1128_, v_cont_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec_ref(v___y_1130_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__2(lean_object* v_a_1139_, lean_object* v___f_1140_, lean_object* v_a_1141_, lean_object* v_bsExpr_1142_, lean_object* v_x_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Lean_Elab_Do_EffectForwarder_lift(v_a_1139_, v___f_1140_, v_a_1141_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_a_1152_; uint8_t v___x_1153_; uint8_t v___x_1154_; uint8_t v___x_1155_; lean_object* v___x_1156_; 
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_a_1152_);
lean_dec_ref_known(v___x_1151_, 1);
v___x_1153_ = 0;
v___x_1154_ = 1;
v___x_1155_ = 1;
v___x_1156_ = l_Lean_Meta_mkLambdaFVars(v_bsExpr_1142_, v_a_1152_, v___x_1153_, v___x_1154_, v___x_1153_, v___x_1154_, v___x_1155_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
return v___x_1156_;
}
else
{
return v___x_1151_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__2___boxed(lean_object* v_a_1157_, lean_object* v___f_1158_, lean_object* v_a_1159_, lean_object* v_bsExpr_1160_, lean_object* v_x_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__2(v_a_1157_, v___f_1158_, v_a_1159_, v_bsExpr_1160_, v_x_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v_x_1161_);
lean_dec_ref(v_bsExpr_1160_);
lean_dec_ref(v_a_1159_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__3(lean_object* v_a_1170_, lean_object* v_fst_1171_, lean_object* v___f_1172_, lean_object* v_____r_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1181_, 0, v_a_1170_);
v___x_1182_ = l_Lean_Elab_Term_elabFunBinders___redArg(v_fst_1171_, v___x_1181_, v___f_1172_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__3___boxed(lean_object* v_a_1183_, lean_object* v_fst_1184_, lean_object* v___f_1185_, lean_object* v_____r_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__3(v_a_1183_, v_fst_1184_, v___f_1185_, v_____r_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec_ref(v_fst_1184_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0___redArg(lean_object* v_msg_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v_ref_1201_; lean_object* v___x_1202_; lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1211_; 
v_ref_1201_ = lean_ctor_get(v___y_1198_, 2);
v___x_1202_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0(v_msg_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1205_ = v___x_1202_;
v_isShared_1206_ = v_isSharedCheck_1211_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1202_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1211_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1207_; lean_object* v___x_1209_; 
lean_inc(v_ref_1201_);
v___x_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1207_, 0, v_ref_1201_);
lean_ctor_set(v___x_1207_, 1, v_a_1203_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set_tag(v___x_1205_, 1);
lean_ctor_set(v___x_1205_, 0, v___x_1207_);
v___x_1209_ = v___x_1205_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1207_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0___redArg___boxed(lean_object* v_msg_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0___redArg(v_msg_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__2(size_t v_sz_1219_, size_t v_i_1220_, lean_object* v_bs_1221_){
_start:
{
uint8_t v___x_1222_; 
v___x_1222_ = lean_usize_dec_lt(v_i_1220_, v_sz_1219_);
if (v___x_1222_ == 0)
{
return v_bs_1221_;
}
else
{
lean_object* v_v_1223_; lean_object* v___x_1224_; lean_object* v_bs_x27_1225_; size_t v___x_1226_; size_t v___x_1227_; lean_object* v___x_1228_; 
v_v_1223_ = lean_array_uget(v_bs_1221_, v_i_1220_);
v___x_1224_ = lean_unsigned_to_nat(0u);
v_bs_x27_1225_ = lean_array_uset(v_bs_1221_, v_i_1220_, v___x_1224_);
v___x_1226_ = ((size_t)1ULL);
v___x_1227_ = lean_usize_add(v_i_1220_, v___x_1226_);
v___x_1228_ = lean_array_uset(v_bs_x27_1225_, v_i_1220_, v_v_1223_);
v_i_1220_ = v___x_1227_;
v_bs_1221_ = v___x_1228_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__2___boxed(lean_object* v_sz_1230_, lean_object* v_i_1231_, lean_object* v_bs_1232_){
_start:
{
size_t v_sz_boxed_1233_; size_t v_i_boxed_1234_; lean_object* v_res_1235_; 
v_sz_boxed_1233_ = lean_unbox_usize(v_sz_1230_);
lean_dec(v_sz_1230_);
v_i_boxed_1234_ = lean_unbox_usize(v_i_1231_);
lean_dec(v_i_1231_);
v_res_1235_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__2(v_sz_boxed_1233_, v_i_boxed_1234_, v_bs_1232_);
return v_res_1235_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16___redArg(lean_object* v_keys_1236_, lean_object* v_i_1237_, lean_object* v_k_1238_){
_start:
{
lean_object* v___x_1239_; uint8_t v___x_1240_; 
v___x_1239_ = lean_array_get_size(v_keys_1236_);
v___x_1240_ = lean_nat_dec_lt(v_i_1237_, v___x_1239_);
if (v___x_1240_ == 0)
{
lean_dec(v_i_1237_);
return v___x_1240_;
}
else
{
lean_object* v_k_x27_1241_; uint8_t v___x_1242_; 
v_k_x27_1241_ = lean_array_fget_borrowed(v_keys_1236_, v_i_1237_);
v___x_1242_ = l_Lean_instBEqExtraModUse_beq(v_k_1238_, v_k_x27_1241_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = lean_unsigned_to_nat(1u);
v___x_1244_ = lean_nat_add(v_i_1237_, v___x_1243_);
lean_dec(v_i_1237_);
v_i_1237_ = v___x_1244_;
goto _start;
}
else
{
lean_dec(v_i_1237_);
return v___x_1240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16___redArg___boxed(lean_object* v_keys_1246_, lean_object* v_i_1247_, lean_object* v_k_1248_){
_start:
{
uint8_t v_res_1249_; lean_object* v_r_1250_; 
v_res_1249_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16___redArg(v_keys_1246_, v_i_1247_, v_k_1248_);
lean_dec_ref(v_k_1248_);
lean_dec_ref(v_keys_1246_);
v_r_1250_ = lean_box(v_res_1249_);
return v_r_1250_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13___redArg(lean_object* v_x_1251_, size_t v_x_1252_, lean_object* v_x_1253_){
_start:
{
if (lean_obj_tag(v_x_1251_) == 0)
{
lean_object* v_es_1254_; lean_object* v___x_1255_; size_t v___x_1256_; size_t v___x_1257_; lean_object* v_j_1258_; lean_object* v___x_1259_; 
v_es_1254_ = lean_ctor_get(v_x_1251_, 0);
v___x_1255_ = lean_box(2);
v___x_1256_ = ((size_t)31ULL);
v___x_1257_ = lean_usize_land(v_x_1252_, v___x_1256_);
v_j_1258_ = lean_usize_to_nat(v___x_1257_);
v___x_1259_ = lean_array_get_borrowed(v___x_1255_, v_es_1254_, v_j_1258_);
lean_dec(v_j_1258_);
switch(lean_obj_tag(v___x_1259_))
{
case 0:
{
lean_object* v_key_1260_; uint8_t v___x_1261_; 
v_key_1260_ = lean_ctor_get(v___x_1259_, 0);
v___x_1261_ = l_Lean_instBEqExtraModUse_beq(v_x_1253_, v_key_1260_);
return v___x_1261_;
}
case 1:
{
lean_object* v_node_1262_; size_t v___x_1263_; size_t v___x_1264_; 
v_node_1262_ = lean_ctor_get(v___x_1259_, 0);
v___x_1263_ = ((size_t)5ULL);
v___x_1264_ = lean_usize_shift_right(v_x_1252_, v___x_1263_);
v_x_1251_ = v_node_1262_;
v_x_1252_ = v___x_1264_;
goto _start;
}
default: 
{
uint8_t v___x_1266_; 
v___x_1266_ = 0;
return v___x_1266_;
}
}
}
else
{
lean_object* v_ks_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; 
v_ks_1267_ = lean_ctor_get(v_x_1251_, 0);
v___x_1268_ = lean_unsigned_to_nat(0u);
v___x_1269_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16___redArg(v_ks_1267_, v___x_1268_, v_x_1253_);
return v___x_1269_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13___redArg___boxed(lean_object* v_x_1270_, lean_object* v_x_1271_, lean_object* v_x_1272_){
_start:
{
size_t v_x_28157__boxed_1273_; uint8_t v_res_1274_; lean_object* v_r_1275_; 
v_x_28157__boxed_1273_ = lean_unbox_usize(v_x_1271_);
lean_dec(v_x_1271_);
v_res_1274_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13___redArg(v_x_1270_, v_x_28157__boxed_1273_, v_x_1272_);
lean_dec_ref(v_x_1272_);
lean_dec_ref(v_x_1270_);
v_r_1275_ = lean_box(v_res_1274_);
return v_r_1275_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9___redArg(lean_object* v_x_1276_, lean_object* v_x_1277_){
_start:
{
uint64_t v___x_1278_; size_t v___x_1279_; uint8_t v___x_1280_; 
v___x_1278_ = l_Lean_instHashableExtraModUse_hash(v_x_1277_);
v___x_1279_ = lean_uint64_to_usize(v___x_1278_);
v___x_1280_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13___redArg(v_x_1276_, v___x_1279_, v_x_1277_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9___redArg___boxed(lean_object* v_x_1281_, lean_object* v_x_1282_){
_start:
{
uint8_t v_res_1283_; lean_object* v_r_1284_; 
v_res_1283_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9___redArg(v_x_1281_, v_x_1282_);
lean_dec_ref(v_x_1282_);
lean_dec_ref(v_x_1281_);
v_r_1284_ = lean_box(v_res_1283_);
return v_r_1284_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1285_; double v___x_1286_; 
v___x_1285_ = lean_unsigned_to_nat(0u);
v___x_1286_ = lean_float_of_nat(v___x_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg(lean_object* v_cls_1290_, lean_object* v_msg_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_ref_1297_; lean_object* v___x_1298_; lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1343_; 
v_ref_1297_ = lean_ctor_get(v___y_1294_, 2);
v___x_1298_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0_spec__0(v_msg_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1301_ = v___x_1298_;
v_isShared_1302_ = v_isSharedCheck_1343_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1298_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1343_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1303_; lean_object* v_traceState_1304_; lean_object* v_env_1305_; lean_object* v_nextMacroScope_1306_; lean_object* v_ngen_1307_; lean_object* v_auxDeclNGen_1308_; lean_object* v_cache_1309_; lean_object* v_messages_1310_; lean_object* v_infoState_1311_; lean_object* v_snapshotTasks_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1342_; 
v___x_1303_ = lean_st_ref_take(v___y_1295_);
v_traceState_1304_ = lean_ctor_get(v___x_1303_, 4);
v_env_1305_ = lean_ctor_get(v___x_1303_, 0);
v_nextMacroScope_1306_ = lean_ctor_get(v___x_1303_, 1);
v_ngen_1307_ = lean_ctor_get(v___x_1303_, 2);
v_auxDeclNGen_1308_ = lean_ctor_get(v___x_1303_, 3);
v_cache_1309_ = lean_ctor_get(v___x_1303_, 5);
v_messages_1310_ = lean_ctor_get(v___x_1303_, 6);
v_infoState_1311_ = lean_ctor_get(v___x_1303_, 7);
v_snapshotTasks_1312_ = lean_ctor_get(v___x_1303_, 8);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1314_ = v___x_1303_;
v_isShared_1315_ = v_isSharedCheck_1342_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_snapshotTasks_1312_);
lean_inc(v_infoState_1311_);
lean_inc(v_messages_1310_);
lean_inc(v_cache_1309_);
lean_inc(v_traceState_1304_);
lean_inc(v_auxDeclNGen_1308_);
lean_inc(v_ngen_1307_);
lean_inc(v_nextMacroScope_1306_);
lean_inc(v_env_1305_);
lean_dec(v___x_1303_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1342_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
uint64_t v_tid_1316_; lean_object* v_traces_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1341_; 
v_tid_1316_ = lean_ctor_get_uint64(v_traceState_1304_, sizeof(void*)*1);
v_traces_1317_ = lean_ctor_get(v_traceState_1304_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v_traceState_1304_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1319_ = v_traceState_1304_;
v_isShared_1320_ = v_isSharedCheck_1341_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_traces_1317_);
lean_dec(v_traceState_1304_);
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
lean_ctor_set(v___x_1326_, 0, v_cls_1290_);
lean_ctor_set(v___x_1326_, 1, v___x_1322_);
lean_ctor_set(v___x_1326_, 2, v___x_1325_);
lean_ctor_set_float(v___x_1326_, sizeof(void*)*3, v___x_1323_);
lean_ctor_set_float(v___x_1326_, sizeof(void*)*3 + 8, v___x_1323_);
lean_ctor_set_uint8(v___x_1326_, sizeof(void*)*3 + 16, v___x_1324_);
v___x_1327_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg___closed__2));
v___x_1328_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1326_);
lean_ctor_set(v___x_1328_, 1, v_a_1299_);
lean_ctor_set(v___x_1328_, 2, v___x_1327_);
lean_inc(v_ref_1297_);
v___x_1329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1329_, 0, v_ref_1297_);
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
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_env_1305_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_nextMacroScope_1306_);
lean_ctor_set(v_reuseFailAlloc_1339_, 2, v_ngen_1307_);
lean_ctor_set(v_reuseFailAlloc_1339_, 3, v_auxDeclNGen_1308_);
lean_ctor_set(v_reuseFailAlloc_1339_, 4, v___x_1332_);
lean_ctor_set(v_reuseFailAlloc_1339_, 5, v_cache_1309_);
lean_ctor_set(v_reuseFailAlloc_1339_, 6, v_messages_1310_);
lean_ctor_set(v_reuseFailAlloc_1339_, 7, v_infoState_1311_);
lean_ctor_set(v_reuseFailAlloc_1339_, 8, v_snapshotTasks_1312_);
v___x_1334_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1335_ = lean_st_ref_put(v___y_1295_, v___x_1334_);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v___x_1321_);
v___x_1337_ = v___x_1301_;
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
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v_env_1399_; uint8_t v_isExporting_1400_; lean_object* v_entry_1401_; lean_object* v___x_1402_; lean_object* v_env_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___x_1449_; uint8_t v___x_1450_; 
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
v___x_1449_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1397_, v___x_1404_, v_env_1403_, v___x_1405_, v___x_1406_);
v___x_1450_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9___redArg(v___x_1449_, v_entry_1401_);
lean_dec(v___x_1449_);
if (v___x_1450_ == 0)
{
lean_object* v_toCold_1451_; lean_object* v_options_1452_; uint8_t v_hasTrace_1453_; 
v_toCold_1451_ = lean_ctor_get(v___y_1394_, 0);
v_options_1452_ = lean_ctor_get(v_toCold_1451_, 2);
v_hasTrace_1453_ = lean_ctor_get_uint8(v_options_1452_, sizeof(void*)*1);
if (v_hasTrace_1453_ == 0)
{
lean_dec(v_hint_1389_);
lean_dec(v_mod_1387_);
v___y_1408_ = v___y_1393_;
v___y_1409_ = v___y_1395_;
goto v___jp_1407_;
}
else
{
lean_object* v_inheritedTraceOptions_1454_; lean_object* v_cls_1455_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___x_1475_; uint8_t v___x_1476_; 
v_inheritedTraceOptions_1454_ = lean_ctor_get(v_toCold_1451_, 11);
v_cls_1455_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__6));
v___x_1475_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__14);
v___x_1476_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1454_, v_options_1452_, v___x_1475_);
if (v___x_1476_ == 0)
{
lean_dec(v_hint_1389_);
lean_dec(v_mod_1387_);
v___y_1408_ = v___y_1393_;
v___y_1409_ = v___y_1395_;
goto v___jp_1407_;
}
else
{
lean_object* v___x_1477_; lean_object* v___y_1479_; 
v___x_1477_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__16);
if (v_isExporting_1400_ == 0)
{
lean_object* v___x_1486_; 
v___x_1486_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__21));
v___y_1479_ = v___x_1486_;
goto v___jp_1478_;
}
else
{
lean_object* v___x_1487_; 
v___x_1487_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__22));
v___y_1479_ = v___x_1487_;
goto v___jp_1478_;
}
v___jp_1478_:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
lean_inc_ref(v___y_1479_);
v___x_1480_ = l_Lean_stringToMessageData(v___y_1479_);
v___x_1481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1477_);
lean_ctor_set(v___x_1481_, 1, v___x_1480_);
v___x_1482_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__18);
v___x_1483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1481_);
lean_ctor_set(v___x_1483_, 1, v___x_1482_);
if (v_isMeta_1388_ == 0)
{
lean_object* v___x_1484_; 
v___x_1484_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__19));
v___y_1462_ = v___x_1483_;
v___y_1463_ = v___x_1484_;
goto v___jp_1461_;
}
else
{
lean_object* v___x_1485_; 
v___x_1485_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__20));
v___y_1462_ = v___x_1483_;
v___y_1463_ = v___x_1485_;
goto v___jp_1461_;
}
}
}
v___jp_1456_:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1459_, 0, v___y_1457_);
lean_ctor_set(v___x_1459_, 1, v___y_1458_);
v___x_1460_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg(v_cls_1455_, v___x_1459_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_dec_ref_known(v___x_1460_, 1);
v___y_1408_ = v___y_1393_;
v___y_1409_ = v___y_1395_;
goto v___jp_1407_;
}
else
{
lean_dec_ref_known(v_entry_1401_, 1);
return v___x_1460_;
}
}
v___jp_1461_:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; uint8_t v___x_1470_; 
lean_inc_ref(v___y_1463_);
v___x_1464_ = l_Lean_stringToMessageData(v___y_1463_);
v___x_1465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1465_, 0, v___y_1462_);
lean_ctor_set(v___x_1465_, 1, v___x_1464_);
v___x_1466_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__8);
v___x_1467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1465_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
v___x_1468_ = l_Lean_MessageData_ofName(v_mod_1387_);
v___x_1469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1467_);
lean_ctor_set(v___x_1469_, 1, v___x_1468_);
v___x_1470_ = l_Lean_Name_isAnonymous(v_hint_1389_);
if (v___x_1470_ == 0)
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1471_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__10);
v___x_1472_ = l_Lean_MessageData_ofName(v_hint_1389_);
v___x_1473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1471_);
lean_ctor_set(v___x_1473_, 1, v___x_1472_);
v___y_1457_ = v___x_1469_;
v___y_1458_ = v___x_1473_;
goto v___jp_1456_;
}
else
{
lean_object* v___x_1474_; 
lean_dec(v_hint_1389_);
v___x_1474_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__11);
v___y_1457_ = v___x_1469_;
v___y_1458_ = v___x_1474_;
goto v___jp_1456_;
}
}
}
}
else
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
lean_dec_ref_known(v_entry_1401_, 1);
lean_dec(v_hint_1389_);
lean_dec(v_mod_1387_);
v___x_1488_ = lean_box(0);
v___x_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
return v___x_1489_;
}
v___jp_1407_:
{
lean_object* v___x_1410_; lean_object* v_toEnvExtension_1411_; lean_object* v_env_1412_; lean_object* v_nextMacroScope_1413_; lean_object* v_ngen_1414_; lean_object* v_auxDeclNGen_1415_; lean_object* v_traceState_1416_; lean_object* v_messages_1417_; lean_object* v_infoState_1418_; lean_object* v_snapshotTasks_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1447_; 
v___x_1410_ = lean_st_ref_take(v___y_1409_);
v_toEnvExtension_1411_ = lean_ctor_get(v___x_1404_, 0);
v_env_1412_ = lean_ctor_get(v___x_1410_, 0);
v_nextMacroScope_1413_ = lean_ctor_get(v___x_1410_, 1);
v_ngen_1414_ = lean_ctor_get(v___x_1410_, 2);
v_auxDeclNGen_1415_ = lean_ctor_get(v___x_1410_, 3);
v_traceState_1416_ = lean_ctor_get(v___x_1410_, 4);
v_messages_1417_ = lean_ctor_get(v___x_1410_, 6);
v_infoState_1418_ = lean_ctor_get(v___x_1410_, 7);
v_snapshotTasks_1419_ = lean_ctor_get(v___x_1410_, 8);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1410_);
if (v_isSharedCheck_1447_ == 0)
{
lean_object* v_unused_1448_; 
v_unused_1448_ = lean_ctor_get(v___x_1410_, 5);
lean_dec(v_unused_1448_);
v___x_1421_ = v___x_1410_;
v_isShared_1422_ = v_isSharedCheck_1447_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_snapshotTasks_1419_);
lean_inc(v_infoState_1418_);
lean_inc(v_messages_1417_);
lean_inc(v_traceState_1416_);
lean_inc(v_auxDeclNGen_1415_);
lean_inc(v_ngen_1414_);
lean_inc(v_nextMacroScope_1413_);
lean_inc(v_env_1412_);
lean_dec(v___x_1410_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1447_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v_asyncMode_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1427_; 
v_asyncMode_1423_ = lean_ctor_get(v_toEnvExtension_1411_, 2);
v___x_1424_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1404_, v_env_1412_, v_entry_1401_, v_asyncMode_1423_, v___x_1406_);
v___x_1425_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__3);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 5, v___x_1425_);
lean_ctor_set(v___x_1421_, 0, v___x_1424_);
v___x_1427_ = v___x_1421_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1424_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v_nextMacroScope_1413_);
lean_ctor_set(v_reuseFailAlloc_1446_, 2, v_ngen_1414_);
lean_ctor_set(v_reuseFailAlloc_1446_, 3, v_auxDeclNGen_1415_);
lean_ctor_set(v_reuseFailAlloc_1446_, 4, v_traceState_1416_);
lean_ctor_set(v_reuseFailAlloc_1446_, 5, v___x_1425_);
lean_ctor_set(v_reuseFailAlloc_1446_, 6, v_messages_1417_);
lean_ctor_set(v_reuseFailAlloc_1446_, 7, v_infoState_1418_);
lean_ctor_set(v_reuseFailAlloc_1446_, 8, v_snapshotTasks_1419_);
v___x_1427_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v_mctx_1430_; lean_object* v_zetaDeltaFVarIds_1431_; lean_object* v_postponed_1432_; lean_object* v_diag_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1444_; 
v___x_1428_ = lean_st_ref_put(v___y_1409_, v___x_1427_);
v___x_1429_ = lean_st_ref_take(v___y_1408_);
v_mctx_1430_ = lean_ctor_get(v___x_1429_, 0);
v_zetaDeltaFVarIds_1431_ = lean_ctor_get(v___x_1429_, 2);
v_postponed_1432_ = lean_ctor_get(v___x_1429_, 3);
v_diag_1433_ = lean_ctor_get(v___x_1429_, 4);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1444_ == 0)
{
lean_object* v_unused_1445_; 
v_unused_1445_ = lean_ctor_get(v___x_1429_, 1);
lean_dec(v_unused_1445_);
v___x_1435_ = v___x_1429_;
v_isShared_1436_ = v_isSharedCheck_1444_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_diag_1433_);
lean_inc(v_postponed_1432_);
lean_inc(v_zetaDeltaFVarIds_1431_);
lean_inc(v_mctx_1430_);
lean_dec(v___x_1429_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1444_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1440_; 
v___x_1437_ = lean_box(0);
v___x_1438_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__4);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 1, v___x_1438_);
v___x_1440_ = v___x_1435_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_mctx_1430_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1443_, 2, v_zetaDeltaFVarIds_1431_);
lean_ctor_set(v_reuseFailAlloc_1443_, 3, v_postponed_1432_);
lean_ctor_set(v_reuseFailAlloc_1443_, 4, v_diag_1433_);
v___x_1440_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1441_ = lean_st_ref_put(v___y_1408_, v___x_1440_);
v___x_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1437_);
return v___x_1442_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___boxed(lean_object* v_mod_1490_, lean_object* v_isMeta_1491_, lean_object* v_hint_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
uint8_t v_isMeta_boxed_1500_; lean_object* v_res_1501_; 
v_isMeta_boxed_1500_ = lean_unbox(v_isMeta_1491_);
v_res_1501_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6(v_mod_1490_, v_isMeta_boxed_1500_, v_hint_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__7(lean_object* v___x_1502_, lean_object* v_declName_1503_, lean_object* v_as_1504_, size_t v_sz_1505_, size_t v_i_1506_, lean_object* v_b_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
uint8_t v___x_1515_; 
v___x_1515_ = lean_usize_dec_lt(v_i_1506_, v_sz_1505_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; 
lean_dec(v_declName_1503_);
v___x_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1516_, 0, v_b_1507_);
return v___x_1516_;
}
else
{
lean_object* v___x_1517_; lean_object* v_modules_1518_; lean_object* v___x_1519_; lean_object* v_a_1520_; lean_object* v___x_1521_; lean_object* v_toImport_1522_; lean_object* v_module_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; lean_object* v___x_1526_; 
v___x_1517_ = l_Lean_Environment_header(v___x_1502_);
v_modules_1518_ = lean_ctor_get(v___x_1517_, 3);
lean_inc_ref(v_modules_1518_);
lean_dec_ref(v___x_1517_);
v___x_1519_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1520_ = lean_array_uget_borrowed(v_as_1504_, v_i_1506_);
v___x_1521_ = lean_array_get(v___x_1519_, v_modules_1518_, v_a_1520_);
lean_dec_ref(v_modules_1518_);
v_toImport_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc_ref(v_toImport_1522_);
lean_dec(v___x_1521_);
v_module_1523_ = lean_ctor_get(v_toImport_1522_, 0);
lean_inc(v_module_1523_);
lean_dec_ref(v_toImport_1522_);
v___x_1524_ = lean_box(0);
v___x_1525_ = 0;
lean_inc(v_declName_1503_);
v___x_1526_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6(v_module_1523_, v___x_1525_, v_declName_1503_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
if (lean_obj_tag(v___x_1526_) == 0)
{
size_t v___x_1527_; size_t v___x_1528_; 
lean_dec_ref_known(v___x_1526_, 1);
v___x_1527_ = ((size_t)1ULL);
v___x_1528_ = lean_usize_add(v_i_1506_, v___x_1527_);
v_i_1506_ = v___x_1528_;
v_b_1507_ = v___x_1524_;
goto _start;
}
else
{
lean_dec(v_declName_1503_);
return v___x_1526_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__7___boxed(lean_object* v___x_1530_, lean_object* v_declName_1531_, lean_object* v_as_1532_, lean_object* v_sz_1533_, lean_object* v_i_1534_, lean_object* v_b_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
size_t v_sz_boxed_1543_; size_t v_i_boxed_1544_; lean_object* v_res_1545_; 
v_sz_boxed_1543_ = lean_unbox_usize(v_sz_1533_);
lean_dec(v_sz_1533_);
v_i_boxed_1544_ = lean_unbox_usize(v_i_1534_);
lean_dec(v_i_1534_);
v_res_1545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__7(v___x_1530_, v_declName_1531_, v_as_1532_, v_sz_boxed_1543_, v_i_boxed_1544_, v_b_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec_ref(v_as_1532_);
lean_dec_ref(v___x_1530_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12___redArg(lean_object* v_a_1546_, lean_object* v_x_1547_){
_start:
{
if (lean_obj_tag(v_x_1547_) == 0)
{
lean_object* v___x_1548_; 
v___x_1548_ = lean_box(0);
return v___x_1548_;
}
else
{
lean_object* v_key_1549_; lean_object* v_value_1550_; lean_object* v_tail_1551_; uint8_t v___x_1552_; 
v_key_1549_ = lean_ctor_get(v_x_1547_, 0);
v_value_1550_ = lean_ctor_get(v_x_1547_, 1);
v_tail_1551_ = lean_ctor_get(v_x_1547_, 2);
v___x_1552_ = lean_name_eq(v_key_1549_, v_a_1546_);
if (v___x_1552_ == 0)
{
v_x_1547_ = v_tail_1551_;
goto _start;
}
else
{
lean_object* v___x_1554_; 
lean_inc(v_value_1550_);
v___x_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1554_, 0, v_value_1550_);
return v___x_1554_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12___redArg___boxed(lean_object* v_a_1555_, lean_object* v_x_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12___redArg(v_a_1555_, v_x_1556_);
lean_dec(v_x_1556_);
lean_dec(v_a_1555_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8___redArg(lean_object* v_m_1558_, lean_object* v_a_1559_){
_start:
{
lean_object* v_buckets_1560_; lean_object* v___x_1561_; uint64_t v___y_1563_; 
v_buckets_1560_ = lean_ctor_get(v_m_1558_, 1);
v___x_1561_ = lean_array_get_size(v_buckets_1560_);
if (lean_obj_tag(v_a_1559_) == 0)
{
uint64_t v___x_1577_; 
v___x_1577_ = 1723ULL;
v___y_1563_ = v___x_1577_;
goto v___jp_1562_;
}
else
{
uint64_t v_hash_1578_; 
v_hash_1578_ = lean_ctor_get_uint64(v_a_1559_, sizeof(void*)*2);
v___y_1563_ = v_hash_1578_;
goto v___jp_1562_;
}
v___jp_1562_:
{
uint64_t v___x_1564_; uint64_t v___x_1565_; uint64_t v_fold_1566_; uint64_t v___x_1567_; uint64_t v___x_1568_; uint64_t v___x_1569_; size_t v___x_1570_; size_t v___x_1571_; size_t v___x_1572_; size_t v___x_1573_; size_t v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1564_ = 32ULL;
v___x_1565_ = lean_uint64_shift_right(v___y_1563_, v___x_1564_);
v_fold_1566_ = lean_uint64_xor(v___y_1563_, v___x_1565_);
v___x_1567_ = 16ULL;
v___x_1568_ = lean_uint64_shift_right(v_fold_1566_, v___x_1567_);
v___x_1569_ = lean_uint64_xor(v_fold_1566_, v___x_1568_);
v___x_1570_ = lean_uint64_to_usize(v___x_1569_);
v___x_1571_ = lean_usize_of_nat(v___x_1561_);
v___x_1572_ = ((size_t)1ULL);
v___x_1573_ = lean_usize_sub(v___x_1571_, v___x_1572_);
v___x_1574_ = lean_usize_land(v___x_1570_, v___x_1573_);
v___x_1575_ = lean_array_uget_borrowed(v_buckets_1560_, v___x_1574_);
v___x_1576_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12___redArg(v_a_1559_, v___x_1575_);
return v___x_1576_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_m_1579_, lean_object* v_a_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8___redArg(v_m_1579_, v_a_1580_);
lean_dec(v_a_1580_);
lean_dec_ref(v_m_1579_);
return v_res_1581_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5(lean_object* v_declName_1585_, uint8_t v_isMeta_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v_env_1599_; lean_object* v___y_1601_; lean_object* v___x_1614_; 
v___x_1594_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5___closed__0);
v___x_1595_ = lean_st_ref_get(v___y_1592_);
v_env_1599_ = lean_ctor_get(v___x_1595_, 0);
lean_inc_ref(v_env_1599_);
lean_dec(v___x_1595_);
v___x_1614_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1599_, v_declName_1585_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_dec_ref(v_env_1599_);
lean_dec(v_declName_1585_);
goto v___jp_1596_;
}
else
{
lean_object* v_val_1615_; lean_object* v___x_1616_; lean_object* v_modules_1617_; lean_object* v___x_1618_; uint8_t v___x_1619_; 
v_val_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_val_1615_);
lean_dec_ref_known(v___x_1614_, 1);
v___x_1616_ = l_Lean_Environment_header(v_env_1599_);
v_modules_1617_ = lean_ctor_get(v___x_1616_, 3);
lean_inc_ref(v_modules_1617_);
lean_dec_ref(v___x_1616_);
v___x_1618_ = lean_array_get_size(v_modules_1617_);
v___x_1619_ = lean_nat_dec_lt(v_val_1615_, v___x_1618_);
if (v___x_1619_ == 0)
{
lean_dec_ref(v_modules_1617_);
lean_dec(v_val_1615_);
lean_dec_ref(v_env_1599_);
lean_dec(v_declName_1585_);
goto v___jp_1596_;
}
else
{
lean_object* v___x_1620_; lean_object* v___x_1621_; uint8_t v___y_1623_; 
v___x_1620_ = lean_array_fget(v_modules_1617_, v_val_1615_);
lean_dec(v_val_1615_);
lean_dec_ref(v_modules_1617_);
v___x_1621_ = lean_st_ref_get(v___y_1592_);
if (v_isMeta_1586_ == 0)
{
lean_dec(v___x_1621_);
v___y_1623_ = v_isMeta_1586_;
goto v___jp_1622_;
}
else
{
lean_object* v_env_1634_; uint8_t v___x_1635_; 
v_env_1634_ = lean_ctor_get(v___x_1621_, 0);
lean_inc_ref(v_env_1634_);
lean_dec(v___x_1621_);
lean_inc(v_declName_1585_);
v___x_1635_ = l_Lean_isMarkedMeta(v_env_1634_, v_declName_1585_);
if (v___x_1635_ == 0)
{
v___y_1623_ = v_isMeta_1586_;
goto v___jp_1622_;
}
else
{
uint8_t v___x_1636_; 
v___x_1636_ = 0;
v___y_1623_ = v___x_1636_;
goto v___jp_1622_;
}
}
v___jp_1622_:
{
lean_object* v_toImport_1624_; lean_object* v_module_1625_; lean_object* v___x_1626_; 
v_toImport_1624_ = lean_ctor_get(v___x_1620_, 0);
lean_inc_ref(v_toImport_1624_);
lean_dec(v___x_1620_);
v_module_1625_ = lean_ctor_get(v_toImport_1624_, 0);
lean_inc(v_module_1625_);
lean_dec_ref(v_toImport_1624_);
lean_inc(v_declName_1585_);
v___x_1626_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6(v_module_1625_, v___y_1623_, v_declName_1585_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
lean_dec_ref_known(v___x_1626_, 1);
v___x_1627_ = l_Lean_indirectModUseExt;
v___x_1628_ = lean_box(1);
v___x_1629_ = lean_box(0);
lean_inc_ref(v_env_1599_);
v___x_1630_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1594_, v___x_1627_, v_env_1599_, v___x_1628_, v___x_1629_);
v___x_1631_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8___redArg(v___x_1630_, v_declName_1585_);
lean_dec(v___x_1630_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v___x_1632_; 
v___x_1632_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5___closed__1));
v___y_1601_ = v___x_1632_;
goto v___jp_1600_;
}
else
{
lean_object* v_val_1633_; 
v_val_1633_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_val_1633_);
lean_dec_ref_known(v___x_1631_, 1);
v___y_1601_ = v_val_1633_;
goto v___jp_1600_;
}
}
else
{
lean_dec_ref(v_env_1599_);
lean_dec(v_declName_1585_);
return v___x_1626_;
}
}
}
}
v___jp_1596_:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1597_ = lean_box(0);
v___x_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1597_);
return v___x_1598_;
}
v___jp_1600_:
{
lean_object* v___x_1602_; size_t v_sz_1603_; size_t v___x_1604_; lean_object* v___x_1605_; 
v___x_1602_ = lean_box(0);
v_sz_1603_ = lean_array_size(v___y_1601_);
v___x_1604_ = ((size_t)0ULL);
v___x_1605_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__7(v_env_1599_, v_declName_1585_, v___y_1601_, v_sz_1603_, v___x_1604_, v___x_1602_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
lean_dec_ref(v___y_1601_);
lean_dec_ref(v_env_1599_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1612_ == 0)
{
lean_object* v_unused_1613_; 
v_unused_1613_ = lean_ctor_get(v___x_1605_, 0);
lean_dec(v_unused_1613_);
v___x_1607_ = v___x_1605_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_dec(v___x_1605_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 0, v___x_1602_);
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1602_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
else
{
return v___x_1605_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5___boxed(lean_object* v_declName_1637_, lean_object* v_isMeta_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
uint8_t v_isMeta_boxed_1646_; lean_object* v_res_1647_; 
v_isMeta_boxed_1646_ = lean_unbox(v_isMeta_1638_);
v_res_1647_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5(v_declName_1637_, v_isMeta_boxed_1646_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6___redArg(lean_object* v_as_x27_1648_, lean_object* v_b_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
if (lean_obj_tag(v_as_x27_1648_) == 0)
{
lean_object* v___x_1657_; 
v___x_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1657_, 0, v_b_1649_);
return v___x_1657_;
}
else
{
lean_object* v_head_1658_; lean_object* v_tail_1659_; lean_object* v___x_1660_; uint8_t v___x_1661_; lean_object* v___x_1662_; 
v_head_1658_ = lean_ctor_get(v_as_x27_1648_, 0);
v_tail_1659_ = lean_ctor_get(v_as_x27_1648_, 1);
v___x_1660_ = lean_box(0);
v___x_1661_ = 1;
lean_inc(v_head_1658_);
v___x_1662_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5(v_head_1658_, v___x_1661_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_dec_ref_known(v___x_1662_, 1);
v_as_x27_1648_ = v_tail_1659_;
v_b_1649_ = v___x_1660_;
goto _start;
}
else
{
return v___x_1662_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6___redArg___boxed(lean_object* v_as_x27_1664_, lean_object* v_b_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6___redArg(v_as_x27_1664_, v_b_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v_as_x27_1664_);
return v_res_1673_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = l_Lean_maxRecDepthErrorMessage;
v___x_1680_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
return v___x_1680_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__4(void){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__3);
v___x_1682_ = l_Lean_MessageData_ofFormat(v___x_1681_);
return v___x_1682_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__5(void){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1683_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__4);
v___x_1684_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__2));
v___x_1685_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1684_);
lean_ctor_set(v___x_1685_, 1, v___x_1683_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg(lean_object* v_ref_1686_){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1688_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___closed__5);
v___x_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1689_, 0, v_ref_1686_);
lean_ctor_set(v___x_1689_, 1, v___x_1688_);
v___x_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg___boxed(lean_object* v_ref_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg(v_ref_1691_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__2(lean_object* v_env_1694_, lean_object* v_currNamespace_1695_, lean_object* v_openDecls_1696_, lean_object* v_n_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1700_ = l_Lean_ResolveName_resolveNamespace(v_env_1694_, v_currNamespace_1695_, v_openDecls_1696_, v_n_1697_);
v___x_1701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1700_);
lean_ctor_set(v___x_1701_, 1, v___y_1699_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__2___boxed(lean_object* v_env_1702_, lean_object* v_currNamespace_1703_, lean_object* v_openDecls_1704_, lean_object* v_n_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__2(v_env_1702_, v_currNamespace_1703_, v_openDecls_1704_, v_n_1705_, v___y_1706_, v___y_1707_);
lean_dec_ref(v___y_1706_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___redArg(lean_object* v_x_1709_, lean_object* v___y_1710_){
_start:
{
if (lean_obj_tag(v_x_1709_) == 0)
{
lean_object* v_a_1711_; lean_object* v___x_1712_; 
v_a_1711_ = lean_ctor_get(v_x_1709_, 0);
lean_inc(v_a_1711_);
v___x_1712_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1712_, 0, v_a_1711_);
lean_ctor_set(v___x_1712_, 1, v___y_1710_);
return v___x_1712_;
}
else
{
lean_object* v_a_1713_; lean_object* v___x_1714_; 
v_a_1713_ = lean_ctor_get(v_x_1709_, 0);
lean_inc(v_a_1713_);
v___x_1714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1714_, 0, v_a_1713_);
lean_ctor_set(v___x_1714_, 1, v___y_1710_);
return v___x_1714_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___redArg___boxed(lean_object* v_x_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___redArg(v_x_1715_, v___y_1716_);
lean_dec_ref(v_x_1715_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__0(lean_object* v_env_1718_, lean_object* v_stx_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v___x_1722_; 
v___x_1722_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_1718_, v_stx_1719_, v___y_1720_, v___y_1721_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1723_);
if (lean_obj_tag(v_a_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1732_; 
v_a_1724_ = lean_ctor_get(v___x_1722_, 1);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1732_ == 0)
{
lean_object* v_unused_1733_; 
v_unused_1733_ = lean_ctor_get(v___x_1722_, 0);
lean_dec(v_unused_1733_);
v___x_1726_ = v___x_1722_;
v_isShared_1727_ = v_isSharedCheck_1732_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1722_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1732_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1728_; lean_object* v___x_1730_; 
v___x_1728_ = lean_box(0);
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 0, v___x_1728_);
v___x_1730_ = v___x_1726_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1728_);
lean_ctor_set(v_reuseFailAlloc_1731_, 1, v_a_1724_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
else
{
lean_object* v_val_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1762_; 
v_val_1734_ = lean_ctor_get(v_a_1723_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v_a_1723_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1736_ = v_a_1723_;
v_isShared_1737_ = v_isSharedCheck_1762_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_val_1734_);
lean_dec(v_a_1723_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1762_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v_snd_1738_; 
v_snd_1738_ = lean_ctor_get(v_val_1734_, 1);
lean_inc(v_snd_1738_);
lean_dec(v_val_1734_);
if (lean_obj_tag(v_snd_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1748_; 
lean_del_object(v___x_1736_);
v_a_1739_ = lean_ctor_get(v___x_1722_, 1);
lean_inc(v_a_1739_);
lean_dec_ref_known(v___x_1722_, 2);
v_a_1740_ = lean_ctor_get(v_snd_1738_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v_snd_1738_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1742_ = v_snd_1738_;
v_isShared_1743_ = v_isSharedCheck_1748_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v_snd_1738_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1748_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1740_);
v___x_1745_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___redArg(v___x_1745_, v_a_1739_);
lean_dec_ref(v___x_1745_);
return v___x_1746_;
}
}
}
else
{
lean_object* v_a_1749_; lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1761_; 
v_a_1749_ = lean_ctor_get(v___x_1722_, 1);
lean_inc(v_a_1749_);
lean_dec_ref_known(v___x_1722_, 2);
v_a_1750_ = lean_ctor_get(v_snd_1738_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v_snd_1738_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1752_ = v_snd_1738_;
v_isShared_1753_ = v_isSharedCheck_1761_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v_snd_1738_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1761_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 0, v_a_1750_);
v___x_1755_ = v___x_1736_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1750_);
v___x_1755_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
lean_object* v___x_1757_; 
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 0, v___x_1755_);
v___x_1757_ = v___x_1752_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1755_);
v___x_1757_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___redArg(v___x_1757_, v_a_1749_);
lean_dec_ref(v___x_1757_);
return v___x_1758_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1763_; lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
v_a_1763_ = lean_ctor_get(v___x_1722_, 0);
v_a_1764_ = lean_ctor_get(v___x_1722_, 1);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v___x_1722_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_inc(v_a_1763_);
lean_dec(v___x_1722_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1763_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_a_1764_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__0___boxed(lean_object* v_env_1772_, lean_object* v_stx_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__0(v_env_1772_, v_stx_1773_, v___y_1774_, v___y_1775_);
lean_dec_ref(v___y_1774_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__4(lean_object* v_env_1777_, lean_object* v_options_1778_, lean_object* v_currNamespace_1779_, lean_object* v_openDecls_1780_, lean_object* v_n_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_){
_start:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1784_ = l_Lean_ResolveName_resolveGlobalName(v_env_1777_, v_options_1778_, v_currNamespace_1779_, v_openDecls_1780_, v_n_1781_);
v___x_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1784_);
lean_ctor_set(v___x_1785_, 1, v___y_1783_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__4___boxed(lean_object* v_env_1786_, lean_object* v_options_1787_, lean_object* v_currNamespace_1788_, lean_object* v_openDecls_1789_, lean_object* v_n_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__4(v_env_1786_, v_options_1787_, v_currNamespace_1788_, v_openDecls_1789_, v_n_1790_, v___y_1791_, v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec_ref(v_options_1787_);
return v_res_1793_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1794_ = lean_box(0);
v___x_1795_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_1796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
lean_ctor_set(v___x_1796_, 1, v___x_1794_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg(){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1798_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg___closed__0);
v___x_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg___boxed(lean_object* v___y_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg();
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__7(lean_object* v_as_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
if (lean_obj_tag(v_as_1802_) == 0)
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = lean_box(0);
v___x_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1810_);
return v___x_1811_;
}
else
{
lean_object* v_toCold_1812_; lean_object* v_options_1813_; uint8_t v_hasTrace_1814_; 
v_toCold_1812_ = lean_ctor_get(v___y_1807_, 0);
v_options_1813_ = lean_ctor_get(v_toCold_1812_, 2);
v_hasTrace_1814_ = lean_ctor_get_uint8(v_options_1813_, sizeof(void*)*1);
if (v_hasTrace_1814_ == 0)
{
lean_object* v_tail_1815_; 
v_tail_1815_ = lean_ctor_get(v_as_1802_, 1);
lean_inc(v_tail_1815_);
lean_dec_ref_known(v_as_1802_, 2);
v_as_1802_ = v_tail_1815_;
goto _start;
}
else
{
lean_object* v_head_1817_; lean_object* v_tail_1818_; lean_object* v_fst_1819_; lean_object* v_snd_1820_; lean_object* v_inheritedTraceOptions_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; uint8_t v___x_1824_; 
v_head_1817_ = lean_ctor_get(v_as_1802_, 0);
lean_inc(v_head_1817_);
v_tail_1818_ = lean_ctor_get(v_as_1802_, 1);
lean_inc(v_tail_1818_);
lean_dec_ref_known(v_as_1802_, 2);
v_fst_1819_ = lean_ctor_get(v_head_1817_, 0);
lean_inc_n(v_fst_1819_, 2);
v_snd_1820_ = lean_ctor_get(v_head_1817_, 1);
lean_inc(v_snd_1820_);
lean_dec(v_head_1817_);
v_inheritedTraceOptions_1821_ = lean_ctor_get(v_toCold_1812_, 11);
v___x_1822_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6___closed__13));
v___x_1823_ = l_Lean_Name_append(v___x_1822_, v_fst_1819_);
v___x_1824_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1821_, v_options_1813_, v___x_1823_);
lean_dec(v___x_1823_);
if (v___x_1824_ == 0)
{
lean_dec(v_snd_1820_);
lean_dec(v_fst_1819_);
v_as_1802_ = v_tail_1818_;
goto _start;
}
else
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1826_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1826_, 0, v_snd_1820_);
v___x_1827_ = l_Lean_MessageData_ofFormat(v___x_1826_);
v___x_1828_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg(v_fst_1819_, v___x_1827_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_dec_ref_known(v___x_1828_, 1);
v_as_1802_ = v_tail_1818_;
goto _start;
}
else
{
lean_dec(v_tail_1818_);
return v___x_1828_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__7___boxed(lean_object* v_as_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__7(v_as_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__3(lean_object* v_currNamespace_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v___x_1842_; 
v___x_1842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1842_, 0, v_currNamespace_1839_);
lean_ctor_set(v___x_1842_, 1, v___y_1841_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__3___boxed(lean_object* v_currNamespace_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__3(v_currNamespace_1843_, v___y_1844_, v___y_1845_);
lean_dec_ref(v___y_1844_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8___redArg(lean_object* v_ref_1847_, lean_object* v_msg_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v_toCold_1856_; lean_object* v_currRecDepth_1857_; lean_object* v_ref_1858_; uint8_t v_diag_1859_; uint8_t v_suppressElabErrors_1860_; lean_object* v_ref_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v_toCold_1856_ = lean_ctor_get(v___y_1853_, 0);
v_currRecDepth_1857_ = lean_ctor_get(v___y_1853_, 1);
v_ref_1858_ = lean_ctor_get(v___y_1853_, 2);
v_diag_1859_ = lean_ctor_get_uint8(v___y_1853_, sizeof(void*)*3);
v_suppressElabErrors_1860_ = lean_ctor_get_uint8(v___y_1853_, sizeof(void*)*3 + 1);
v_ref_1861_ = l_Lean_replaceRef(v_ref_1847_, v_ref_1858_);
lean_inc(v_currRecDepth_1857_);
lean_inc_ref(v_toCold_1856_);
v___x_1862_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1862_, 0, v_toCold_1856_);
lean_ctor_set(v___x_1862_, 1, v_currRecDepth_1857_);
lean_ctor_set(v___x_1862_, 2, v_ref_1861_);
lean_ctor_set_uint8(v___x_1862_, sizeof(void*)*3, v_diag_1859_);
lean_ctor_set_uint8(v___x_1862_, sizeof(void*)*3 + 1, v_suppressElabErrors_1860_);
v___x_1863_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg(v_msg_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___x_1862_, v___y_1854_);
lean_dec_ref_known(v___x_1862_, 3);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8___redArg___boxed(lean_object* v_ref_1864_, lean_object* v_msg_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8___redArg(v_ref_1864_, v_msg_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v_ref_1864_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__1(lean_object* v_env_1874_, lean_object* v_declName_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
uint8_t v___x_1878_; lean_object* v_env_1879_; lean_object* v___x_1880_; uint8_t v___x_1881_; uint8_t v___x_1882_; 
v___x_1878_ = 0;
v_env_1879_ = l_Lean_Environment_setExporting(v_env_1874_, v___x_1878_);
lean_inc(v_declName_1875_);
v___x_1880_ = l_Lean_mkPrivateName(v_env_1879_, v_declName_1875_);
v___x_1881_ = 1;
lean_inc_ref(v_env_1879_);
v___x_1882_ = l_Lean_Environment_contains(v_env_1879_, v___x_1880_, v___x_1881_);
if (v___x_1882_ == 0)
{
lean_object* v___x_1883_; uint8_t v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1883_ = l_Lean_privateToUserName(v_declName_1875_);
v___x_1884_ = l_Lean_Environment_contains(v_env_1879_, v___x_1883_, v___x_1881_);
v___x_1885_ = lean_box(v___x_1884_);
v___x_1886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1885_);
lean_ctor_set(v___x_1886_, 1, v___y_1877_);
return v___x_1886_;
}
else
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
lean_dec_ref(v_env_1879_);
lean_dec(v_declName_1875_);
v___x_1887_ = lean_box(v___x_1882_);
v___x_1888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
lean_ctor_set(v___x_1888_, 1, v___y_1877_);
return v___x_1888_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__1___boxed(lean_object* v_env_1889_, lean_object* v_declName_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__1(v_env_1889_, v_declName_1890_, v___y_1891_, v___y_1892_);
lean_dec_ref(v___y_1891_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg(lean_object* v_x_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v___x_1903_; lean_object* v_toCold_1904_; lean_object* v_env_1905_; lean_object* v_currRecDepth_1906_; lean_object* v_ref_1907_; lean_object* v_options_1908_; lean_object* v_maxRecDepth_1909_; lean_object* v_currNamespace_1910_; lean_object* v_openDecls_1911_; lean_object* v_quotContext_1912_; lean_object* v_currMacroScope_1913_; lean_object* v___f_1914_; lean_object* v___f_1915_; lean_object* v___f_1916_; lean_object* v___f_1917_; lean_object* v___f_1918_; lean_object* v_methods_1919_; lean_object* v___x_1920_; lean_object* v_nextMacroScope_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1903_ = lean_st_ref_get(v___y_1901_);
v_toCold_1904_ = lean_ctor_get(v___y_1900_, 0);
v_env_1905_ = lean_ctor_get(v___x_1903_, 0);
lean_inc_ref_n(v_env_1905_, 4);
lean_dec(v___x_1903_);
v_currRecDepth_1906_ = lean_ctor_get(v___y_1900_, 1);
v_ref_1907_ = lean_ctor_get(v___y_1900_, 2);
v_options_1908_ = lean_ctor_get(v_toCold_1904_, 2);
v_maxRecDepth_1909_ = lean_ctor_get(v_toCold_1904_, 3);
v_currNamespace_1910_ = lean_ctor_get(v_toCold_1904_, 4);
v_openDecls_1911_ = lean_ctor_get(v_toCold_1904_, 5);
v_quotContext_1912_ = lean_ctor_get(v_toCold_1904_, 8);
v_currMacroScope_1913_ = lean_ctor_get(v_toCold_1904_, 9);
v___f_1914_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1914_, 0, v_env_1905_);
v___f_1915_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_1915_, 0, v_env_1905_);
lean_inc_n(v_openDecls_1911_, 2);
lean_inc_n(v_currNamespace_1910_, 3);
v___f_1916_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1916_, 0, v_env_1905_);
lean_closure_set(v___f_1916_, 1, v_currNamespace_1910_);
lean_closure_set(v___f_1916_, 2, v_openDecls_1911_);
v___f_1917_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_1917_, 0, v_currNamespace_1910_);
lean_inc_ref(v_options_1908_);
v___f_1918_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_1918_, 0, v_env_1905_);
lean_closure_set(v___f_1918_, 1, v_options_1908_);
lean_closure_set(v___f_1918_, 2, v_currNamespace_1910_);
lean_closure_set(v___f_1918_, 3, v_openDecls_1911_);
v_methods_1919_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_1919_, 0, v___f_1914_);
lean_ctor_set(v_methods_1919_, 1, v___f_1917_);
lean_ctor_set(v_methods_1919_, 2, v___f_1915_);
lean_ctor_set(v_methods_1919_, 3, v___f_1916_);
lean_ctor_set(v_methods_1919_, 4, v___f_1918_);
v___x_1920_ = lean_st_ref_get(v___y_1901_);
v_nextMacroScope_1921_ = lean_ctor_get(v___x_1920_, 1);
lean_inc(v_nextMacroScope_1921_);
lean_dec(v___x_1920_);
lean_inc(v_ref_1907_);
lean_inc(v_maxRecDepth_1909_);
lean_inc(v_currRecDepth_1906_);
lean_inc(v_currMacroScope_1913_);
lean_inc(v_quotContext_1912_);
v___x_1922_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1922_, 0, v_methods_1919_);
lean_ctor_set(v___x_1922_, 1, v_quotContext_1912_);
lean_ctor_set(v___x_1922_, 2, v_currMacroScope_1913_);
lean_ctor_set(v___x_1922_, 3, v_currRecDepth_1906_);
lean_ctor_set(v___x_1922_, 4, v_maxRecDepth_1909_);
lean_ctor_set(v___x_1922_, 5, v_ref_1907_);
v___x_1923_ = lean_box(0);
v___x_1924_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1924_, 0, v_nextMacroScope_1921_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
lean_ctor_set(v___x_1924_, 2, v___x_1923_);
v___x_1925_ = lean_apply_2(v_x_1895_, v___x_1922_, v___x_1924_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v_a_1927_; lean_object* v_macroScope_1928_; lean_object* v_traceMsgs_1929_; lean_object* v_expandedMacroDecls_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 1);
lean_inc(v_a_1926_);
v_a_1927_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1927_);
lean_dec_ref_known(v___x_1925_, 2);
v_macroScope_1928_ = lean_ctor_get(v_a_1926_, 0);
lean_inc(v_macroScope_1928_);
v_traceMsgs_1929_ = lean_ctor_get(v_a_1926_, 1);
lean_inc(v_traceMsgs_1929_);
v_expandedMacroDecls_1930_ = lean_ctor_get(v_a_1926_, 2);
lean_inc(v_expandedMacroDecls_1930_);
lean_dec(v_a_1926_);
v___x_1931_ = lean_box(0);
v___x_1932_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6___redArg(v_expandedMacroDecls_1930_, v___x_1931_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
lean_dec(v_expandedMacroDecls_1930_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v___x_1933_; lean_object* v_env_1934_; lean_object* v_ngen_1935_; lean_object* v_auxDeclNGen_1936_; lean_object* v_traceState_1937_; lean_object* v_cache_1938_; lean_object* v_messages_1939_; lean_object* v_infoState_1940_; lean_object* v_snapshotTasks_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1967_; 
lean_dec_ref_known(v___x_1932_, 1);
v___x_1933_ = lean_st_ref_take(v___y_1901_);
v_env_1934_ = lean_ctor_get(v___x_1933_, 0);
v_ngen_1935_ = lean_ctor_get(v___x_1933_, 2);
v_auxDeclNGen_1936_ = lean_ctor_get(v___x_1933_, 3);
v_traceState_1937_ = lean_ctor_get(v___x_1933_, 4);
v_cache_1938_ = lean_ctor_get(v___x_1933_, 5);
v_messages_1939_ = lean_ctor_get(v___x_1933_, 6);
v_infoState_1940_ = lean_ctor_get(v___x_1933_, 7);
v_snapshotTasks_1941_ = lean_ctor_get(v___x_1933_, 8);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1967_ == 0)
{
lean_object* v_unused_1968_; 
v_unused_1968_ = lean_ctor_get(v___x_1933_, 1);
lean_dec(v_unused_1968_);
v___x_1943_ = v___x_1933_;
v_isShared_1944_ = v_isSharedCheck_1967_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_snapshotTasks_1941_);
lean_inc(v_infoState_1940_);
lean_inc(v_messages_1939_);
lean_inc(v_cache_1938_);
lean_inc(v_traceState_1937_);
lean_inc(v_auxDeclNGen_1936_);
lean_inc(v_ngen_1935_);
lean_inc(v_env_1934_);
lean_dec(v___x_1933_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1967_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 1, v_macroScope_1928_);
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_env_1934_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v_macroScope_1928_);
lean_ctor_set(v_reuseFailAlloc_1966_, 2, v_ngen_1935_);
lean_ctor_set(v_reuseFailAlloc_1966_, 3, v_auxDeclNGen_1936_);
lean_ctor_set(v_reuseFailAlloc_1966_, 4, v_traceState_1937_);
lean_ctor_set(v_reuseFailAlloc_1966_, 5, v_cache_1938_);
lean_ctor_set(v_reuseFailAlloc_1966_, 6, v_messages_1939_);
lean_ctor_set(v_reuseFailAlloc_1966_, 7, v_infoState_1940_);
lean_ctor_set(v_reuseFailAlloc_1966_, 8, v_snapshotTasks_1941_);
v___x_1946_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1947_ = lean_st_ref_put(v___y_1901_, v___x_1946_);
v___x_1948_ = l_List_reverse___redArg(v_traceMsgs_1929_);
v___x_1949_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__7(v___x_1948_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1956_ == 0)
{
lean_object* v_unused_1957_; 
v_unused_1957_ = lean_ctor_get(v___x_1949_, 0);
lean_dec(v_unused_1957_);
v___x_1951_ = v___x_1949_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_dec(v___x_1949_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v_a_1927_);
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1927_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
else
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
lean_dec(v_a_1927_);
v_a_1958_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___x_1949_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1949_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
}
}
else
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1976_; 
lean_dec(v_traceMsgs_1929_);
lean_dec(v_macroScope_1928_);
lean_dec(v_a_1927_);
v_a_1969_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___x_1932_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1932_);
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
lean_object* v_a_1977_; 
v_a_1977_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1977_);
lean_dec_ref_known(v___x_1925_, 2);
if (lean_obj_tag(v_a_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v_a_1979_; lean_object* v___x_1980_; uint8_t v___x_1981_; 
v_a_1978_ = lean_ctor_get(v_a_1977_, 0);
lean_inc(v_a_1978_);
v_a_1979_ = lean_ctor_get(v_a_1977_, 1);
lean_inc_ref(v_a_1979_);
lean_dec_ref_known(v_a_1977_, 2);
v___x_1980_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___closed__0));
v___x_1981_ = lean_string_dec_eq(v_a_1979_, v___x_1980_);
if (v___x_1981_ == 0)
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1982_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1982_, 0, v_a_1979_);
v___x_1983_ = l_Lean_MessageData_ofFormat(v___x_1982_);
v___x_1984_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8___redArg(v_a_1978_, v___x_1983_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
lean_dec(v_a_1978_);
return v___x_1984_;
}
else
{
lean_object* v___x_1985_; 
lean_dec_ref(v_a_1979_);
v___x_1985_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg(v_a_1978_);
return v___x_1985_;
}
}
else
{
lean_object* v___x_1986_; 
v___x_1986_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg();
return v___x_1986_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg___boxed(lean_object* v_x_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg(v_x_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
return v_res_1995_;
}
}
static lean_object* _init_l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__1(void){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__0));
v___x_1998_ = l_Lean_stringToMessageData(v___x_1997_);
return v___x_1998_;
}
}
static lean_object* _init_l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__6(void){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2007_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__5));
v___x_2008_ = l_Lean_stringToMessageData(v___x_2007_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f(lean_object* v_e_2009_, lean_object* v_dec_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_){
_start:
{
lean_object* v___x_2019_; 
v___x_2019_ = l_Lean_Elab_Do_Forward_matchApp_x3f(v_e_2009_);
if (lean_obj_tag(v___x_2019_) == 1)
{
lean_object* v_val_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2190_; 
v_val_2020_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2022_ = v___x_2019_;
v_isShared_2023_ = v_isSharedCheck_2190_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_val_2020_);
lean_dec(v___x_2019_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2190_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v_fst_2024_; lean_object* v_snd_2025_; lean_object* v___f_2026_; lean_object* v___x_2027_; 
v_fst_2024_ = lean_ctor_get(v_val_2020_, 0);
lean_inc_n(v_fst_2024_, 2);
v_snd_2025_ = lean_ctor_get(v_val_2020_, 1);
lean_inc(v_snd_2025_);
lean_dec(v_val_2020_);
lean_inc(v_a_2015_);
lean_inc_ref(v_a_2014_);
lean_inc(v_a_2013_);
lean_inc_ref(v_a_2012_);
v___f_2026_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__0___boxed), 8, 5);
lean_closure_set(v___f_2026_, 0, v_a_2012_);
lean_closure_set(v___f_2026_, 1, v_a_2013_);
lean_closure_set(v___f_2026_, 2, v_a_2014_);
lean_closure_set(v___f_2026_, 3, v_a_2015_);
lean_closure_set(v___f_2026_, 4, v_fst_2024_);
v___x_2027_ = l_Lean_Core_withFreshMacroScope___redArg(v___f_2026_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v_fst_2029_; lean_object* v_snd_2030_; lean_object* v___x_2031_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2028_);
lean_dec_ref_known(v___x_2027_, 1);
v_fst_2029_ = lean_ctor_get(v_a_2028_, 0);
lean_inc_n(v_fst_2029_, 2);
v_snd_2030_ = lean_ctor_get(v_a_2028_, 1);
lean_inc_n(v_snd_2030_, 2);
lean_dec(v_a_2028_);
v___x_2031_ = l___private_Lean_Elab_BuiltinDo_Forward_0__Lean_Elab_Do_validateForwarder(v_fst_2024_, v_fst_2029_, v_snd_2030_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_binders_2032_; lean_object* v_body_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2173_; 
lean_dec_ref_known(v___x_2031_, 1);
v_binders_2032_ = lean_ctor_get(v_snd_2025_, 0);
v_body_2033_ = lean_ctor_get(v_snd_2025_, 1);
v_isSharedCheck_2173_ = !lean_is_exclusive(v_snd_2025_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2035_ = v_snd_2025_;
v_isShared_2036_ = v_isSharedCheck_2173_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_body_2033_);
lean_inc(v_binders_2032_);
lean_dec(v_snd_2025_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2173_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___f_2037_; lean_object* v___x_2038_; 
lean_inc(v_body_2033_);
v___f_2037_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__1___boxed), 10, 1);
lean_closure_set(v___f_2037_, 0, v_body_2033_);
v___x_2038_ = l_Lean_Elab_Do_InferControlInfo_ofSeq(v_body_2033_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_a_2039_; lean_object* v___x_2040_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_a_2039_);
lean_dec_ref_known(v___x_2038_, 1);
v___x_2040_ = l_Lean_Elab_Do_EffectForwarder_ofCont(v_a_2039_, v_dec_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
lean_dec(v_a_2039_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2081_; lean_object* v___f_2113_; lean_object* v___x_2114_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc_n(v_a_2041_, 2);
lean_dec_ref_known(v___x_2040_, 1);
lean_inc_ref(v_a_2011_);
v___f_2113_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__2___boxed), 12, 3);
lean_closure_set(v___f_2113_, 0, v_a_2041_);
lean_closure_set(v___f_2113_, 1, v___f_2037_);
lean_closure_set(v___f_2113_, 2, v_a_2011_);
lean_inc(v_a_2017_);
lean_inc_ref(v_a_2016_);
lean_inc(v_a_2015_);
lean_inc_ref(v_a_2014_);
lean_inc(v_fst_2029_);
v___x_2114_ = lean_infer_type(v_fst_2029_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v___x_2116_; lean_object* v_a_2117_; lean_object* v_ref_2118_; uint8_t v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2124_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2115_);
lean_dec_ref_known(v___x_2114_, 1);
v___x_2116_ = l_Lean_instantiateMVars___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__1___redArg(v_a_2115_, v_a_2015_);
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2117_);
lean_dec_ref(v___x_2116_);
v_ref_2118_ = lean_ctor_get(v_a_2016_, 2);
v___x_2119_ = 0;
v___x_2120_ = l_Lean_SourceInfo_fromRef(v_ref_2118_, v___x_2119_);
v___x_2121_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__3));
v___x_2122_ = ((lean_object*)(l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__4));
lean_inc(v___x_2120_);
if (v_isShared_2036_ == 0)
{
lean_ctor_set_tag(v___x_2035_, 2);
lean_ctor_set(v___x_2035_, 1, v___x_2122_);
lean_ctor_set(v___x_2035_, 0, v___x_2120_);
v___x_2124_ = v___x_2035_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2120_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v___x_2122_);
v___x_2124_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
lean_object* v___x_2125_; size_t v_sz_2126_; size_t v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2125_ = l_Lean_Syntax_node1(v___x_2120_, v___x_2121_, v___x_2124_);
v_sz_2126_ = lean_array_size(v_binders_2032_);
v___x_2127_ = ((size_t)0ULL);
v___x_2128_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__2(v_sz_2126_, v___x_2127_, v_binders_2032_);
v___x_2129_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandFunBinders___boxed), 4, 2);
lean_closure_set(v___x_2129_, 0, v___x_2128_);
lean_closure_set(v___x_2129_, 1, v___x_2125_);
v___x_2130_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg(v___x_2129_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v_snd_2132_; lean_object* v_snd_2133_; uint8_t v___x_2134_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2130_, 1);
v_snd_2132_ = lean_ctor_get(v_a_2131_, 1);
v_snd_2133_ = lean_ctor_get(v_snd_2132_, 1);
v___x_2134_ = lean_unbox(v_snd_2133_);
if (v___x_2134_ == 0)
{
lean_object* v_fst_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v_fst_2135_ = lean_ctor_get(v_a_2131_, 0);
lean_inc(v_fst_2135_);
lean_dec(v_a_2131_);
v___x_2136_ = lean_box(0);
v___x_2137_ = l_Lean_Elab_Do_tryElabForwardApp_x3f___lam__3(v_a_2117_, v_fst_2135_, v___f_2113_, v___x_2136_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
lean_dec(v_fst_2135_);
v___y_2081_ = v___x_2137_;
goto v___jp_2080_;
}
else
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
lean_dec(v_a_2131_);
lean_dec(v_a_2117_);
lean_dec_ref(v___f_2113_);
lean_dec(v_a_2041_);
lean_dec(v_snd_2030_);
lean_dec(v_fst_2029_);
lean_del_object(v___x_2022_);
v___x_2138_ = lean_obj_once(&l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__6, &l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__6_once, _init_l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__6);
v___x_2139_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoForward_spec__0___redArg(v___x_2138_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2139_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2139_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
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
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_dec(v_a_2117_);
lean_dec_ref(v___f_2113_);
lean_dec(v_a_2041_);
lean_dec(v_snd_2030_);
lean_dec(v_fst_2029_);
lean_del_object(v___x_2022_);
v_a_2148_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2130_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2130_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
}
else
{
lean_dec_ref(v___f_2113_);
lean_del_object(v___x_2035_);
lean_dec_ref(v_binders_2032_);
v___y_2081_ = v___x_2114_;
goto v___jp_2080_;
}
v___jp_2042_:
{
lean_object* v___x_2050_; 
v___x_2050_ = l_Lean_Elab_Do_EffectForwarder_restoreCont(v_a_2041_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; lean_object* v___x_2052_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2051_);
lean_dec_ref_known(v___x_2050_, 1);
v___x_2052_ = l_Lean_Elab_Do_DoElemCont_mkBindUnlessPure(v_a_2051_, v_snd_2030_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2063_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2055_ = v___x_2052_;
v_isShared_2056_ = v_isSharedCheck_2063_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2052_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2063_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 0, v_a_2053_);
v___x_2058_ = v___x_2022_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
lean_object* v___x_2060_; 
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 0, v___x_2058_);
v___x_2060_ = v___x_2055_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2058_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
else
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
lean_del_object(v___x_2022_);
v_a_2064_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___x_2052_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2052_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_dec(v_snd_2030_);
lean_del_object(v___x_2022_);
v_a_2072_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2050_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2050_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
v___jp_2080_:
{
if (lean_obj_tag(v___y_2081_) == 0)
{
lean_object* v_a_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v_a_2082_ = lean_ctor_get(v___y_2081_, 0);
lean_inc(v_a_2082_);
lean_dec_ref_known(v___y_2081_, 1);
v___x_2083_ = l_Lean_Expr_mvarId_x21(v_fst_2029_);
lean_dec(v_fst_2029_);
lean_inc(v_a_2017_);
lean_inc_ref(v_a_2016_);
lean_inc(v_a_2015_);
lean_inc_ref(v_a_2014_);
v___x_2084_ = lean_checked_assign(v___x_2083_, v_a_2082_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; uint8_t v___x_2086_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_a_2085_);
lean_dec_ref_known(v___x_2084_, 1);
v___x_2086_ = lean_unbox(v_a_2085_);
lean_dec(v_a_2085_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec(v_a_2041_);
lean_dec(v_snd_2030_);
lean_del_object(v___x_2022_);
v___x_2087_ = lean_obj_once(&l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__1, &l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__1_once, _init_l_Lean_Elab_Do_tryElabForwardApp_x3f___closed__1);
v___x_2088_ = l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0___redArg(v___x_2087_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2088_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2088_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
else
{
v___y_2043_ = v_a_2011_;
v___y_2044_ = v_a_2012_;
v___y_2045_ = v_a_2013_;
v___y_2046_ = v_a_2014_;
v___y_2047_ = v_a_2015_;
v___y_2048_ = v_a_2016_;
v___y_2049_ = v_a_2017_;
goto v___jp_2042_;
}
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_dec(v_a_2041_);
lean_dec(v_snd_2030_);
lean_del_object(v___x_2022_);
v_a_2097_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2084_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2084_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
lean_dec(v_a_2041_);
lean_dec(v_snd_2030_);
lean_dec(v_fst_2029_);
lean_del_object(v___x_2022_);
v_a_2105_ = lean_ctor_get(v___y_2081_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___y_2081_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___y_2081_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___y_2081_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
}
else
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
lean_dec_ref(v___f_2037_);
lean_del_object(v___x_2035_);
lean_dec_ref(v_binders_2032_);
lean_dec(v_snd_2030_);
lean_dec(v_fst_2029_);
lean_del_object(v___x_2022_);
v_a_2157_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___x_2040_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2040_);
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
else
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
lean_dec_ref(v___f_2037_);
lean_del_object(v___x_2035_);
lean_dec_ref(v_binders_2032_);
lean_dec(v_snd_2030_);
lean_dec(v_fst_2029_);
lean_del_object(v___x_2022_);
lean_dec_ref(v_dec_2010_);
v_a_2165_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2038_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2038_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
lean_dec(v_snd_2030_);
lean_dec(v_fst_2029_);
lean_dec(v_snd_2025_);
lean_del_object(v___x_2022_);
lean_dec_ref(v_dec_2010_);
v_a_2174_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2031_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2031_);
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
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_dec(v_snd_2025_);
lean_dec(v_fst_2024_);
lean_del_object(v___x_2022_);
lean_dec_ref(v_dec_2010_);
v_a_2182_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2027_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2027_);
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
}
else
{
lean_object* v___x_2191_; lean_object* v___x_2192_; 
lean_dec(v___x_2019_);
lean_dec_ref(v_dec_2010_);
v___x_2191_ = lean_box(0);
v___x_2192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2191_);
return v___x_2192_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_tryElabForwardApp_x3f___boxed(lean_object* v_e_2193_, lean_object* v_dec_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l_Lean_Elab_Do_tryElabForwardApp_x3f(v_e_2193_, v_dec_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_);
lean_dec(v_a_2201_);
lean_dec_ref(v_a_2200_);
lean_dec(v_a_2199_);
lean_dec_ref(v_a_2198_);
lean_dec(v_a_2197_);
lean_dec_ref(v_a_2196_);
lean_dec_ref(v_a_2195_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0(lean_object* v_00_u03b1_2204_, lean_object* v_msg_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_){
_start:
{
lean_object* v___x_2214_; 
v___x_2214_ = l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0___redArg(v_msg_2205_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0___boxed(lean_object* v_00_u03b1_2215_, lean_object* v_msg_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_Lean_throwError___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__0(v_00_u03b1_2215_, v_msg_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec_ref(v___y_2217_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4(lean_object* v_00_u03b1_2226_, lean_object* v_x_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
lean_object* v___x_2230_; 
v___x_2230_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___redArg(v_x_2227_, v___y_2229_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2231_, lean_object* v_x_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__4(v_00_u03b1_2231_, v_x_2232_, v___y_2233_, v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec_ref(v_x_2232_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9(lean_object* v_00_u03b1_2236_, lean_object* v_ref_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_){
_start:
{
lean_object* v___x_2245_; 
v___x_2245_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___redArg(v_ref_2237_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9___boxed(lean_object* v_00_u03b1_2246_, lean_object* v_ref_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__9(v_00_u03b1_2246_, v_ref_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10(lean_object* v_00_u03b1_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v___x_2264_; 
v___x_2264_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___redArg();
return v___x_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10___boxed(lean_object* v_00_u03b1_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__10(v_00_u03b1_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3(lean_object* v_00_u03b1_2274_, lean_object* v_x_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___redArg(v_x_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3___boxed(lean_object* v_00_u03b1_2284_, lean_object* v_x_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3(v_00_u03b1_2284_, v_x_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3(lean_object* v_cls_2294_, lean_object* v_msg_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v___x_2303_; 
v___x_2303_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___redArg(v_cls_2294_, v_msg_2295_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3___boxed(lean_object* v_cls_2304_, lean_object* v_msg_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__3(v_cls_2304_, v_msg_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6(lean_object* v_as_2314_, lean_object* v_as_x27_2315_, lean_object* v_b_2316_, lean_object* v_a_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v___x_2325_; 
v___x_2325_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6___redArg(v_as_x27_2315_, v_b_2316_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6___boxed(lean_object* v_as_2326_, lean_object* v_as_x27_2327_, lean_object* v_b_2328_, lean_object* v_a_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__6(v_as_2326_, v_as_x27_2327_, v_b_2328_, v_a_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v_as_x27_2327_);
lean_dec(v_as_2326_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8(lean_object* v_00_u03b1_2338_, lean_object* v_ref_2339_, lean_object* v_msg_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v___x_2348_; 
v___x_2348_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8___redArg(v_ref_2339_, v_msg_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8___boxed(lean_object* v_00_u03b1_2349_, lean_object* v_ref_2350_, lean_object* v_msg_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__8(v_00_u03b1_2349_, v_ref_2350_, v_msg_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v_ref_2350_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_2360_, lean_object* v_m_2361_, lean_object* v_a_2362_){
_start:
{
lean_object* v___x_2363_; 
v___x_2363_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8___redArg(v_m_2361_, v_a_2362_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_2364_, lean_object* v_m_2365_, lean_object* v_a_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8(v_00_u03b2_2364_, v_m_2365_, v_a_2366_);
lean_dec(v_a_2366_);
lean_dec_ref(v_m_2365_);
return v_res_2367_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9(lean_object* v_00_u03b2_2368_, lean_object* v_x_2369_, lean_object* v_x_2370_){
_start:
{
uint8_t v___x_2371_; 
v___x_2371_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9___redArg(v_x_2369_, v_x_2370_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9___boxed(lean_object* v_00_u03b2_2372_, lean_object* v_x_2373_, lean_object* v_x_2374_){
_start:
{
uint8_t v_res_2375_; lean_object* v_r_2376_; 
v_res_2375_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9(v_00_u03b2_2372_, v_x_2373_, v_x_2374_);
lean_dec_ref(v_x_2374_);
lean_dec_ref(v_x_2373_);
v_r_2376_ = lean_box(v_res_2375_);
return v_r_2376_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12(lean_object* v_00_u03b2_2377_, lean_object* v_a_2378_, lean_object* v_x_2379_){
_start:
{
lean_object* v___x_2380_; 
v___x_2380_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12___redArg(v_a_2378_, v_x_2379_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12___boxed(lean_object* v_00_u03b2_2381_, lean_object* v_a_2382_, lean_object* v_x_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__8_spec__12(v_00_u03b2_2381_, v_a_2382_, v_x_2383_);
lean_dec(v_x_2383_);
lean_dec(v_a_2382_);
return v_res_2384_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13(lean_object* v_00_u03b2_2385_, lean_object* v_x_2386_, size_t v_x_2387_, lean_object* v_x_2388_){
_start:
{
uint8_t v___x_2389_; 
v___x_2389_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13___redArg(v_x_2386_, v_x_2387_, v_x_2388_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13___boxed(lean_object* v_00_u03b2_2390_, lean_object* v_x_2391_, lean_object* v_x_2392_, lean_object* v_x_2393_){
_start:
{
size_t v_x_29888__boxed_2394_; uint8_t v_res_2395_; lean_object* v_r_2396_; 
v_x_29888__boxed_2394_ = lean_unbox_usize(v_x_2392_);
lean_dec(v_x_2392_);
v_res_2395_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13(v_00_u03b2_2390_, v_x_2391_, v_x_29888__boxed_2394_, v_x_2393_);
lean_dec_ref(v_x_2393_);
lean_dec_ref(v_x_2391_);
v_r_2396_ = lean_box(v_res_2395_);
return v_r_2396_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16(lean_object* v_00_u03b2_2397_, lean_object* v_keys_2398_, lean_object* v_vals_2399_, lean_object* v_heq_2400_, lean_object* v_i_2401_, lean_object* v_k_2402_){
_start:
{
uint8_t v___x_2403_; 
v___x_2403_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16___redArg(v_keys_2398_, v_i_2401_, v_k_2402_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16___boxed(lean_object* v_00_u03b2_2404_, lean_object* v_keys_2405_, lean_object* v_vals_2406_, lean_object* v_heq_2407_, lean_object* v_i_2408_, lean_object* v_k_2409_){
_start:
{
uint8_t v_res_2410_; lean_object* v_r_2411_; 
v_res_2410_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_tryElabForwardApp_x3f_spec__3_spec__5_spec__6_spec__9_spec__13_spec__16(v_00_u03b2_2404_, v_keys_2405_, v_vals_2406_, v_heq_2407_, v_i_2408_, v_k_2409_);
lean_dec_ref(v_k_2409_);
lean_dec_ref(v_vals_2406_);
lean_dec_ref(v_keys_2405_);
v_r_2411_ = lean_box(v_res_2410_);
return v_r_2411_;
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
