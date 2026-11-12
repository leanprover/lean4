// Lean compiler output
// Module: Lean.Elab.Idbg
// Imports: public import Lean.Elab.Do.Basic meta import Lean.Parser.Do public import Lean.Idbg
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Do_doElemElabAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_mkMonadApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_realpath(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_exprToSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_inServer;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSorry(lean_object*);
lean_object* l_Lean_Idbg_exprToJson(lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Idbg_idbgServer(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_IO_CancelToken_new();
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Core_wrapAsyncAsSnapshot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_defaultReportingRange(lean_object*);
lean_object* l_Lean_Core_logSnapshotTask___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint64_t lean_string_hash(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_setNondep(lean_object*, uint8_t);
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_ensureUnitAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_doElabToSyntax___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Do_controlInfoElemAttribute;
extern lean_object* l_Lean_Elab_Do_instInhabitedControlInfo_default;
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___redArg();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doIdbg"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(61, 152, 121, 224, 0, 70, 155, 32)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__6_value),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__7_value),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Idbg"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__10 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__9_value),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(222, 127, 37, 145, 246, 253, 221, 130)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(167, 188, 96, 25, 36, 32, 177, 172)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__12 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__12_value),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(154, 85, 246, 154, 57, 30, 227, 186)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__13 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__13_value),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 120, 240, 118, 26, 169, 87, 68)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__14 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__14_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__15 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__14_value),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(72, 181, 66, 123, 98, 246, 242, 167)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__16 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__16_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "controlInfoIdbg"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__17 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__16_value),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(38, 98, 163, 235, 228, 39, 161, 40)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__18 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__18_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__8___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "idbg: "};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Import"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__2_value),LEAN_SCALAR_PTR_LITERAL(29, 47, 116, 218, 39, 28, 172, 37)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__1_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__5_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__7;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__2_value),LEAN_SCALAR_PTR_LITERAL(29, 47, 116, 218, 39, 28, 172, 37)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(233, 207, 36, 16, 41, 121, 79, 89)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__8_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__11(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__0 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "f"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__1 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(29, 68, 183, 24, 128, 148, 178, 23)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__2 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toArray"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__3 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__1_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__3_value),LEAN_SCALAR_PTR_LITERAL(225, 54, 189, 64, 249, 49, 198, 116)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__4 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__5;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__6 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__1_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__6_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__7 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__8;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__9;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term_>>=_"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__10 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__10_value),LEAN_SCALAR_PTR_LITERAL(143, 92, 54, 199, 40, 32, 117, 253)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__11 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__12 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__12_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__13 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.Idbg.idbgClientLoop"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__14 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__14_value;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__15;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "idbgClientLoop"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__16 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(216, 3, 140, 103, 23, 193, 97, 10)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__17_value_aux_1),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__16_value),LEAN_SCALAR_PTR_LITERAL(114, 35, 176, 243, 23, 158, 209, 172)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__17 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__18 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__19 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__19_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__20 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__20_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__20_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__21 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__21_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = ">>="};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__22 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__22_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__23 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__23_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__24_value_aux_0),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__24_value_aux_1),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__24_value_aux_2),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__23_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__24 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__24_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__25 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__25_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__26_value_aux_0),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__26_value_aux_1),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__26_value_aux_2),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__25_value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__26 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__26_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__27 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__27_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__28_value_aux_0),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__28_value_aux_1),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__28_value_aux_2),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__27_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__28 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__28_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__29 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__29_value;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__30;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__31 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__31_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "type"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__32 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__32_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "value"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__33 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__33_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "elabIdbgCore"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__34 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__34_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "idbg: abstracted type still has metavariables"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__35 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__35_value;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__36;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "idbg: abstracted value still has metavariables"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__37 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__37_value;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__38;
static const lean_array_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__39 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__39_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "repr"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__40 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__40_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__40_value),LEAN_SCALAR_PTR_LITERAL(248, 109, 138, 163, 21, 170, 71, 243)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__41 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__41_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ToString"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__42 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__42_value;
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toString"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__43 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__43_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__42_value),LEAN_SCALAR_PTR_LITERAL(30, 202, 174, 203, 16, 186, 159, 168)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__44_value_aux_0),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__43_value),LEAN_SCALAR_PTR_LITERAL(206, 210, 39, 124, 69, 192, 37, 107)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__44 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__44_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "idbg"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__0 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(158, 127, 98, 129, 230, 27, 154, 50)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__1 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "elabIdbgTerm"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__16_value),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(174, 12, 184, 32, 84, 90, 234, 209)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "idbg body"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elabDoIdbg"};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__16_value),((lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 80, 1, 78, 180, 59, 65, 71)}};
static const lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___redArg(){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = l_Lean_Elab_Do_instInhabitedControlInfo_default;
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___redArg___boxed(lean_object* v_a_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___redArg();
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg(lean_object* v_x_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___redArg();
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___boxed(lean_object* v_x_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg(v_x_15_, v_a_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_);
lean_dec(v_a_21_);
lean_dec_ref(v_a_20_);
lean_dec(v_a_19_);
lean_dec_ref(v_a_18_);
lean_dec(v_a_17_);
lean_dec_ref(v_a_16_);
lean_dec(v_x_15_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1(){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_66_ = l_Lean_Elab_Do_controlInfoElemAttribute;
v___x_67_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__4));
v___x_68_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__18));
v___x_69_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___boxed), 8, 0);
v___x_70_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_66_, v___x_67_, v___x_68_, v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___boxed(lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1();
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg(lean_object* v_e_73_, lean_object* v___y_74_){
_start:
{
uint8_t v___x_76_; 
v___x_76_ = l_Lean_Expr_hasMVar(v_e_73_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; 
v___x_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_77_, 0, v_e_73_);
return v___x_77_;
}
else
{
lean_object* v___x_78_; lean_object* v_mctx_79_; lean_object* v___x_80_; lean_object* v_fst_81_; lean_object* v_snd_82_; lean_object* v___x_83_; lean_object* v_cache_84_; lean_object* v_zetaDeltaFVarIds_85_; lean_object* v_postponed_86_; lean_object* v_diag_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_96_; 
v___x_78_ = lean_st_ref_get(v___y_74_);
v_mctx_79_ = lean_ctor_get(v___x_78_, 0);
lean_inc_ref(v_mctx_79_);
lean_dec(v___x_78_);
v___x_80_ = l_Lean_instantiateMVarsCore(v_mctx_79_, v_e_73_);
v_fst_81_ = lean_ctor_get(v___x_80_, 0);
lean_inc(v_fst_81_);
v_snd_82_ = lean_ctor_get(v___x_80_, 1);
lean_inc(v_snd_82_);
lean_dec_ref(v___x_80_);
v___x_83_ = lean_st_ref_take(v___y_74_);
v_cache_84_ = lean_ctor_get(v___x_83_, 1);
v_zetaDeltaFVarIds_85_ = lean_ctor_get(v___x_83_, 2);
v_postponed_86_ = lean_ctor_get(v___x_83_, 3);
v_diag_87_ = lean_ctor_get(v___x_83_, 4);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_96_ == 0)
{
lean_object* v_unused_97_; 
v_unused_97_ = lean_ctor_get(v___x_83_, 0);
lean_dec(v_unused_97_);
v___x_89_ = v___x_83_;
v_isShared_90_ = v_isSharedCheck_96_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_diag_87_);
lean_inc(v_postponed_86_);
lean_inc(v_zetaDeltaFVarIds_85_);
lean_inc(v_cache_84_);
lean_dec(v___x_83_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_96_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_92_; 
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v_snd_82_);
v___x_92_ = v___x_89_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_snd_82_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v_cache_84_);
lean_ctor_set(v_reuseFailAlloc_95_, 2, v_zetaDeltaFVarIds_85_);
lean_ctor_set(v_reuseFailAlloc_95_, 3, v_postponed_86_);
lean_ctor_set(v_reuseFailAlloc_95_, 4, v_diag_87_);
v___x_92_ = v_reuseFailAlloc_95_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_st_ref_put(v___y_74_, v___x_92_);
v___x_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_94_, 0, v_fst_81_);
return v___x_94_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg___boxed(lean_object* v_e_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg(v_e_98_, v___y_99_);
lean_dec(v___y_99_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3(lean_object* v_e_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg(v_e_102_, v___y_106_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___boxed(lean_object* v_e_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3(v_e_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4___redArg(lean_object* v_lctx_120_, lean_object* v_x_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_keyedConfig_129_; uint8_t v_trackZetaDelta_130_; lean_object* v_zetaDeltaSet_131_; lean_object* v_localInstances_132_; lean_object* v_defEqCtx_x3f_133_; lean_object* v_synthPendingDepth_134_; lean_object* v_customCanUnfoldPredicate_x3f_135_; uint8_t v_univApprox_136_; uint8_t v_inTypeClassResolution_137_; uint8_t v_cacheInferType_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v_keyedConfig_129_ = lean_ctor_get(v___y_124_, 0);
v_trackZetaDelta_130_ = lean_ctor_get_uint8(v___y_124_, sizeof(void*)*7);
v_zetaDeltaSet_131_ = lean_ctor_get(v___y_124_, 1);
v_localInstances_132_ = lean_ctor_get(v___y_124_, 3);
v_defEqCtx_x3f_133_ = lean_ctor_get(v___y_124_, 4);
v_synthPendingDepth_134_ = lean_ctor_get(v___y_124_, 5);
v_customCanUnfoldPredicate_x3f_135_ = lean_ctor_get(v___y_124_, 6);
v_univApprox_136_ = lean_ctor_get_uint8(v___y_124_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_137_ = lean_ctor_get_uint8(v___y_124_, sizeof(void*)*7 + 2);
v_cacheInferType_138_ = lean_ctor_get_uint8(v___y_124_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_135_);
lean_inc(v_synthPendingDepth_134_);
lean_inc(v_defEqCtx_x3f_133_);
lean_inc_ref(v_localInstances_132_);
lean_inc(v_zetaDeltaSet_131_);
lean_inc_ref(v_keyedConfig_129_);
v___x_139_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_139_, 0, v_keyedConfig_129_);
lean_ctor_set(v___x_139_, 1, v_zetaDeltaSet_131_);
lean_ctor_set(v___x_139_, 2, v_lctx_120_);
lean_ctor_set(v___x_139_, 3, v_localInstances_132_);
lean_ctor_set(v___x_139_, 4, v_defEqCtx_x3f_133_);
lean_ctor_set(v___x_139_, 5, v_synthPendingDepth_134_);
lean_ctor_set(v___x_139_, 6, v_customCanUnfoldPredicate_x3f_135_);
lean_ctor_set_uint8(v___x_139_, sizeof(void*)*7, v_trackZetaDelta_130_);
lean_ctor_set_uint8(v___x_139_, sizeof(void*)*7 + 1, v_univApprox_136_);
lean_ctor_set_uint8(v___x_139_, sizeof(void*)*7 + 2, v_inTypeClassResolution_137_);
lean_ctor_set_uint8(v___x_139_, sizeof(void*)*7 + 3, v_cacheInferType_138_);
lean_inc(v___y_127_);
lean_inc_ref(v___y_126_);
lean_inc(v___y_125_);
lean_inc(v___y_123_);
lean_inc_ref(v___y_122_);
v___x_140_ = lean_apply_7(v_x_121_, v___y_122_, v___y_123_, v___x_139_, v___y_125_, v___y_126_, v___y_127_, lean_box(0));
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_148_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_148_ == 0)
{
v___x_143_ = v___x_140_;
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_140_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_144_ == 0)
{
v___x_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_a_141_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
else
{
return v___x_140_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4___redArg___boxed(lean_object* v_lctx_149_, lean_object* v_x_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4___redArg(v_lctx_149_, v_x_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4(lean_object* v_00_u03b1_159_, lean_object* v_lctx_160_, lean_object* v_x_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4___redArg(v_lctx_160_, v_x_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4___boxed(lean_object* v_00_u03b1_170_, lean_object* v_lctx_171_, lean_object* v_x_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4(v_00_u03b1_170_, v_lctx_171_, v_x_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg___lam__0(lean_object* v_k_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v_b_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v___x_190_; 
lean_inc(v___y_188_);
lean_inc_ref(v___y_187_);
lean_inc(v___y_186_);
lean_inc_ref(v___y_185_);
lean_inc(v___y_183_);
lean_inc_ref(v___y_182_);
v___x_190_ = lean_apply_8(v_k_181_, v_b_184_, v___y_182_, v___y_183_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, lean_box(0));
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg___lam__0___boxed(lean_object* v_k_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v_b_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg___lam__0(v_k_191_, v___y_192_, v___y_193_, v_b_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg(lean_object* v_name_201_, uint8_t v_bi_202_, lean_object* v_type_203_, lean_object* v_k_204_, uint8_t v_kind_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v___f_213_; lean_object* v___x_214_; 
lean_inc(v___y_207_);
lean_inc_ref(v___y_206_);
v___f_213_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_213_, 0, v_k_204_);
lean_closure_set(v___f_213_, 1, v___y_206_);
lean_closure_set(v___f_213_, 2, v___y_207_);
v___x_214_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_201_, v_bi_202_, v_type_203_, v___f_213_, v_kind_205_, v___y_208_, v___y_209_, v___y_210_, v___y_211_);
if (lean_obj_tag(v___x_214_) == 0)
{
return v___x_214_;
}
else
{
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_222_; 
v_a_215_ = lean_ctor_get(v___x_214_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_222_ == 0)
{
v___x_217_ = v___x_214_;
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_214_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_220_; 
if (v_isShared_218_ == 0)
{
v___x_220_ = v___x_217_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_a_215_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg___boxed(lean_object* v_name_223_, lean_object* v_bi_224_, lean_object* v_type_225_, lean_object* v_k_226_, lean_object* v_kind_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
uint8_t v_bi_boxed_235_; uint8_t v_kind_boxed_236_; lean_object* v_res_237_; 
v_bi_boxed_235_ = lean_unbox(v_bi_224_);
v_kind_boxed_236_ = lean_unbox(v_kind_227_);
v_res_237_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg(v_name_223_, v_bi_boxed_235_, v_type_225_, v_k_226_, v_kind_boxed_236_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5(lean_object* v_00_u03b1_238_, lean_object* v_name_239_, uint8_t v_bi_240_, lean_object* v_type_241_, lean_object* v_k_242_, uint8_t v_kind_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg(v_name_239_, v_bi_240_, v_type_241_, v_k_242_, v_kind_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___boxed(lean_object* v_00_u03b1_252_, lean_object* v_name_253_, lean_object* v_bi_254_, lean_object* v_type_255_, lean_object* v_k_256_, lean_object* v_kind_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
uint8_t v_bi_boxed_265_; uint8_t v_kind_boxed_266_; lean_object* v_res_267_; 
v_bi_boxed_265_ = lean_unbox(v_bi_254_);
v_kind_boxed_266_ = lean_unbox(v_kind_257_);
v_res_267_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5(v_00_u03b1_252_, v_name_253_, v_bi_boxed_265_, v_type_255_, v_k_256_, v_kind_boxed_266_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
return v_res_267_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__8(lean_object* v_opts_268_, lean_object* v_opt_269_){
_start:
{
lean_object* v_name_270_; lean_object* v_defValue_271_; lean_object* v_map_272_; lean_object* v___x_273_; 
v_name_270_ = lean_ctor_get(v_opt_269_, 0);
v_defValue_271_ = lean_ctor_get(v_opt_269_, 1);
v_map_272_ = lean_ctor_get(v_opts_268_, 0);
v___x_273_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_272_, v_name_270_);
if (lean_obj_tag(v___x_273_) == 0)
{
uint8_t v___x_274_; 
v___x_274_ = lean_unbox(v_defValue_271_);
return v___x_274_;
}
else
{
lean_object* v_val_275_; 
v_val_275_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_val_275_);
lean_dec_ref_known(v___x_273_, 1);
if (lean_obj_tag(v_val_275_) == 1)
{
uint8_t v_v_276_; 
v_v_276_ = lean_ctor_get_uint8(v_val_275_, 0);
lean_dec_ref_known(v_val_275_, 0);
return v_v_276_;
}
else
{
uint8_t v___x_277_; 
lean_dec(v_val_275_);
v___x_277_ = lean_unbox(v_defValue_271_);
return v___x_277_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__8___boxed(lean_object* v_opts_278_, lean_object* v_opt_279_){
_start:
{
uint8_t v_res_280_; lean_object* v_r_281_; 
v_res_280_ = l_Lean_Option_get___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__8(v_opts_278_, v_opt_279_);
lean_dec_ref(v_opt_279_);
lean_dec_ref(v_opts_278_);
v_r_281_ = lean_box(v_res_280_);
return v_r_281_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0(uint8_t v_suppressElabErrors_289_, lean_object* v_x_290_){
_start:
{
if (lean_obj_tag(v_x_290_) == 1)
{
lean_object* v_pre_291_; 
v_pre_291_ = lean_ctor_get(v_x_290_, 0);
switch(lean_obj_tag(v_pre_291_))
{
case 1:
{
lean_object* v_pre_292_; 
v_pre_292_ = lean_ctor_get(v_pre_291_, 0);
switch(lean_obj_tag(v_pre_292_))
{
case 0:
{
lean_object* v_str_293_; lean_object* v_str_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v_str_293_ = lean_ctor_get(v_x_290_, 1);
v_str_294_ = lean_ctor_get(v_pre_291_, 1);
v___x_295_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__8));
v___x_296_ = lean_string_dec_eq(v_str_294_, v___x_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_297_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__0));
v___x_298_ = lean_string_dec_eq(v_str_294_, v___x_297_);
if (v___x_298_ == 0)
{
return v___x_298_;
}
else
{
lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_299_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__1));
v___x_300_ = lean_string_dec_eq(v_str_293_, v___x_299_);
if (v___x_300_ == 0)
{
return v___x_300_;
}
else
{
return v_suppressElabErrors_289_;
}
}
}
else
{
lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_301_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__2));
v___x_302_ = lean_string_dec_eq(v_str_293_, v___x_301_);
if (v___x_302_ == 0)
{
return v___x_302_;
}
else
{
return v_suppressElabErrors_289_;
}
}
}
case 1:
{
lean_object* v_pre_303_; 
v_pre_303_ = lean_ctor_get(v_pre_292_, 0);
if (lean_obj_tag(v_pre_303_) == 0)
{
lean_object* v_str_304_; lean_object* v_str_305_; lean_object* v_str_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v_str_304_ = lean_ctor_get(v_x_290_, 1);
v_str_305_ = lean_ctor_get(v_pre_291_, 1);
v_str_306_ = lean_ctor_get(v_pre_292_, 1);
v___x_307_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__3));
v___x_308_ = lean_string_dec_eq(v_str_306_, v___x_307_);
if (v___x_308_ == 0)
{
return v___x_308_;
}
else
{
lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_309_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__4));
v___x_310_ = lean_string_dec_eq(v_str_305_, v___x_309_);
if (v___x_310_ == 0)
{
return v___x_310_;
}
else
{
lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_311_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__5));
v___x_312_ = lean_string_dec_eq(v_str_304_, v___x_311_);
if (v___x_312_ == 0)
{
return v___x_312_;
}
else
{
return v_suppressElabErrors_289_;
}
}
}
}
else
{
uint8_t v___x_313_; 
v___x_313_ = 0;
return v___x_313_;
}
}
default: 
{
uint8_t v___x_314_; 
v___x_314_ = 0;
return v___x_314_;
}
}
}
case 0:
{
lean_object* v_str_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v_str_315_ = lean_ctor_get(v_x_290_, 1);
v___x_316_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___closed__6));
v___x_317_ = lean_string_dec_eq(v_str_315_, v___x_316_);
if (v___x_317_ == 0)
{
return v___x_317_;
}
else
{
return v_suppressElabErrors_289_;
}
}
default: 
{
uint8_t v___x_318_; 
v___x_318_ = 0;
return v___x_318_;
}
}
}
else
{
uint8_t v___x_319_; 
v___x_319_ = 0;
return v___x_319_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___boxed(lean_object* v_suppressElabErrors_320_, lean_object* v_x_321_){
_start:
{
uint8_t v_suppressElabErrors_boxed_322_; uint8_t v_res_323_; lean_object* v_r_324_; 
v_suppressElabErrors_boxed_322_ = lean_unbox(v_suppressElabErrors_320_);
v_res_323_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0(v_suppressElabErrors_boxed_322_, v_x_321_);
lean_dec(v_x_321_);
v_r_324_ = lean_box(v_res_323_);
return v_r_324_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__0(void){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_325_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__1(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__0);
v___x_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
return v___x_327_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__2(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_328_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__1);
v___x_329_ = lean_unsigned_to_nat(0u);
v___x_330_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
lean_ctor_set(v___x_330_, 2, v___x_329_);
lean_ctor_set(v___x_330_, 3, v___x_329_);
lean_ctor_set(v___x_330_, 4, v___x_328_);
lean_ctor_set(v___x_330_, 5, v___x_328_);
lean_ctor_set(v___x_330_, 6, v___x_328_);
lean_ctor_set(v___x_330_, 7, v___x_328_);
lean_ctor_set(v___x_330_, 8, v___x_328_);
lean_ctor_set(v___x_330_, 9, v___x_328_);
lean_ctor_set(v___x_330_, 10, v___x_328_);
return v___x_330_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__3(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_331_ = lean_unsigned_to_nat(32u);
v___x_332_ = lean_mk_empty_array_with_capacity(v___x_331_);
v___x_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
return v___x_333_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__4(void){
_start:
{
size_t v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_334_ = ((size_t)5ULL);
v___x_335_ = lean_unsigned_to_nat(0u);
v___x_336_ = lean_unsigned_to_nat(32u);
v___x_337_ = lean_mk_empty_array_with_capacity(v___x_336_);
v___x_338_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__3);
v___x_339_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v___x_337_);
lean_ctor_set(v___x_339_, 2, v___x_335_);
lean_ctor_set(v___x_339_, 3, v___x_335_);
lean_ctor_set_usize(v___x_339_, 4, v___x_334_);
return v___x_339_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__5(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_340_ = lean_box(1);
v___x_341_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__4);
v___x_342_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__1);
v___x_343_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v___x_341_);
lean_ctor_set(v___x_343_, 2, v___x_340_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19(lean_object* v_msgData_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v___x_348_; lean_object* v_toCold_349_; lean_object* v_env_350_; lean_object* v_options_351_; uint8_t v___x_352_; lean_object* v_env_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_348_ = lean_st_ref_get(v___y_346_);
v_toCold_349_ = lean_ctor_get(v___y_345_, 0);
v_env_350_ = lean_ctor_get(v___x_348_, 0);
lean_inc_ref(v_env_350_);
lean_dec(v___x_348_);
v_options_351_ = lean_ctor_get(v_toCold_349_, 2);
v___x_352_ = 0;
v_env_353_ = l_Lean_Environment_setRecordingDeps(v_env_350_, v___x_352_);
v___x_354_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__2);
v___x_355_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___closed__5);
lean_inc_ref(v_options_351_);
v___x_356_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_356_, 0, v_env_353_);
lean_ctor_set(v___x_356_, 1, v___x_354_);
lean_ctor_set(v___x_356_, 2, v___x_355_);
lean_ctor_set(v___x_356_, 3, v_options_351_);
v___x_357_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
lean_ctor_set(v___x_357_, 1, v_msgData_344_);
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19___boxed(lean_object* v_msgData_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19(v_msgData_359_, v___y_360_, v___y_361_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13(lean_object* v_ref_365_, lean_object* v_msgData_366_, uint8_t v_severity_367_, uint8_t v_isSilent_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; uint8_t v___y_377_; lean_object* v___y_378_; uint8_t v___y_379_; lean_object* v_toCold_380_; lean_object* v___y_381_; lean_object* v___y_410_; lean_object* v___y_411_; uint8_t v___y_412_; lean_object* v___y_413_; lean_object* v___y_414_; uint8_t v___y_415_; uint8_t v___y_416_; lean_object* v___y_417_; uint8_t v___y_437_; lean_object* v___y_438_; lean_object* v___y_439_; lean_object* v___y_440_; uint8_t v___y_441_; uint8_t v___y_442_; lean_object* v___y_443_; uint8_t v___y_447_; uint8_t v___y_448_; uint8_t v___x_458_; uint8_t v___y_460_; uint8_t v___x_466_; 
v___x_458_ = 2;
v___x_466_ = l_Lean_instBEqMessageSeverity_beq(v_severity_367_, v___x_458_);
if (v___x_466_ == 0)
{
v___y_460_ = v___x_466_;
goto v___jp_459_;
}
else
{
uint8_t v___x_467_; 
lean_inc_ref(v_msgData_366_);
v___x_467_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_366_);
if (v___x_467_ == 0)
{
v___y_460_ = v___x_467_;
goto v___jp_459_;
}
else
{
lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec_ref(v_msgData_366_);
v___x_468_ = lean_box(0);
v___x_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
return v___x_469_;
}
}
v___jp_372_:
{
lean_object* v_currNamespace_382_; lean_object* v_openDecls_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v_env_388_; lean_object* v_nextMacroScope_389_; lean_object* v_ngen_390_; lean_object* v_auxDeclNGen_391_; lean_object* v_traceState_392_; lean_object* v_cache_393_; lean_object* v_recordedDeps_394_; lean_object* v_messages_395_; lean_object* v_infoState_396_; lean_object* v_snapshotTasks_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_408_; 
v_currNamespace_382_ = lean_ctor_get(v_toCold_380_, 4);
v_openDecls_383_ = lean_ctor_get(v_toCold_380_, 5);
lean_inc(v_openDecls_383_);
lean_inc(v_currNamespace_382_);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v_currNamespace_382_);
lean_ctor_set(v___x_384_, 1, v_openDecls_383_);
v___x_385_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
lean_ctor_set(v___x_385_, 1, v___y_378_);
lean_inc_ref(v___y_374_);
lean_inc_ref(v___y_375_);
v___x_386_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_386_, 0, v___y_375_);
lean_ctor_set(v___x_386_, 1, v___y_373_);
lean_ctor_set(v___x_386_, 2, v___y_376_);
lean_ctor_set(v___x_386_, 3, v___y_374_);
lean_ctor_set(v___x_386_, 4, v___x_385_);
lean_ctor_set_uint8(v___x_386_, sizeof(void*)*5, v___y_379_);
lean_ctor_set_uint8(v___x_386_, sizeof(void*)*5 + 1, v___y_377_);
lean_ctor_set_uint8(v___x_386_, sizeof(void*)*5 + 2, v_isSilent_368_);
v___x_387_ = lean_st_ref_take(v___y_381_);
v_env_388_ = lean_ctor_get(v___x_387_, 0);
v_nextMacroScope_389_ = lean_ctor_get(v___x_387_, 1);
v_ngen_390_ = lean_ctor_get(v___x_387_, 2);
v_auxDeclNGen_391_ = lean_ctor_get(v___x_387_, 3);
v_traceState_392_ = lean_ctor_get(v___x_387_, 4);
v_cache_393_ = lean_ctor_get(v___x_387_, 5);
v_recordedDeps_394_ = lean_ctor_get(v___x_387_, 6);
v_messages_395_ = lean_ctor_get(v___x_387_, 7);
v_infoState_396_ = lean_ctor_get(v___x_387_, 8);
v_snapshotTasks_397_ = lean_ctor_get(v___x_387_, 9);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_408_ == 0)
{
v___x_399_ = v___x_387_;
v_isShared_400_ = v_isSharedCheck_408_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_snapshotTasks_397_);
lean_inc(v_infoState_396_);
lean_inc(v_messages_395_);
lean_inc(v_recordedDeps_394_);
lean_inc(v_cache_393_);
lean_inc(v_traceState_392_);
lean_inc(v_auxDeclNGen_391_);
lean_inc(v_ngen_390_);
lean_inc(v_nextMacroScope_389_);
lean_inc(v_env_388_);
lean_dec(v___x_387_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_408_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_401_ = lean_box(0);
v___x_402_ = l_Lean_MessageLog_add(v___x_386_, v_messages_395_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 7, v___x_402_);
v___x_404_ = v___x_399_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_env_388_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_nextMacroScope_389_);
lean_ctor_set(v_reuseFailAlloc_407_, 2, v_ngen_390_);
lean_ctor_set(v_reuseFailAlloc_407_, 3, v_auxDeclNGen_391_);
lean_ctor_set(v_reuseFailAlloc_407_, 4, v_traceState_392_);
lean_ctor_set(v_reuseFailAlloc_407_, 5, v_cache_393_);
lean_ctor_set(v_reuseFailAlloc_407_, 6, v_recordedDeps_394_);
lean_ctor_set(v_reuseFailAlloc_407_, 7, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_407_, 8, v_infoState_396_);
lean_ctor_set(v_reuseFailAlloc_407_, 9, v_snapshotTasks_397_);
v___x_404_ = v_reuseFailAlloc_407_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_st_ref_put(v___y_381_, v___x_404_);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_401_);
return v___x_406_;
}
}
}
v___jp_409_:
{
lean_object* v_fileName_418_; lean_object* v_fileMap_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_435_; 
v_fileName_418_ = lean_ctor_get(v___y_413_, 0);
v_fileMap_419_ = lean_ctor_get(v___y_413_, 1);
v___x_420_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_366_);
v___x_421_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13_spec__19(v___x_420_, v___y_369_, v___y_370_);
v_a_422_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_435_ == 0)
{
v___x_424_ = v___x_421_;
v_isShared_425_ = v_isSharedCheck_435_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_421_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_435_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
lean_inc_ref_n(v_fileMap_419_, 2);
v___x_426_ = l_Lean_FileMap_toPosition(v_fileMap_419_, v___y_414_);
lean_dec(v___y_414_);
v___x_427_ = l_Lean_FileMap_toPosition(v_fileMap_419_, v___y_417_);
lean_dec(v___y_417_);
v___x_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
v___x_429_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___closed__0));
if (v___y_412_ == 0)
{
lean_del_object(v___x_424_);
lean_dec_ref(v___y_411_);
v___y_373_ = v___x_426_;
v___y_374_ = v___x_429_;
v___y_375_ = v_fileName_418_;
v___y_376_ = v___x_428_;
v___y_377_ = v___y_415_;
v___y_378_ = v_a_422_;
v___y_379_ = v___y_416_;
v_toCold_380_ = v___y_410_;
v___y_381_ = v___y_370_;
goto v___jp_372_;
}
else
{
uint8_t v___x_430_; 
lean_inc(v_a_422_);
v___x_430_ = l_Lean_MessageData_hasTag(v___y_411_, v_a_422_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; lean_object* v___x_433_; 
lean_dec_ref_known(v___x_428_, 1);
lean_dec_ref(v___x_426_);
lean_dec(v_a_422_);
v___x_431_ = lean_box(0);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_431_);
v___x_433_ = v___x_424_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_431_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
else
{
lean_del_object(v___x_424_);
v___y_373_ = v___x_426_;
v___y_374_ = v___x_429_;
v___y_375_ = v_fileName_418_;
v___y_376_ = v___x_428_;
v___y_377_ = v___y_415_;
v___y_378_ = v_a_422_;
v___y_379_ = v___y_416_;
v_toCold_380_ = v___y_410_;
v___y_381_ = v___y_370_;
goto v___jp_372_;
}
}
}
}
v___jp_436_:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_Syntax_getTailPos_x3f(v___y_440_, v___y_442_);
lean_dec(v___y_440_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_inc(v___y_443_);
v___y_410_ = v___y_438_;
v___y_411_ = v___y_439_;
v___y_412_ = v___y_437_;
v___y_413_ = v___y_438_;
v___y_414_ = v___y_443_;
v___y_415_ = v___y_441_;
v___y_416_ = v___y_442_;
v___y_417_ = v___y_443_;
goto v___jp_409_;
}
else
{
lean_object* v_val_445_; 
v_val_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_val_445_);
lean_dec_ref_known(v___x_444_, 1);
v___y_410_ = v___y_438_;
v___y_411_ = v___y_439_;
v___y_412_ = v___y_437_;
v___y_413_ = v___y_438_;
v___y_414_ = v___y_443_;
v___y_415_ = v___y_441_;
v___y_416_ = v___y_442_;
v___y_417_ = v_val_445_;
goto v___jp_409_;
}
}
v___jp_446_:
{
lean_object* v_toCold_449_; lean_object* v_ref_450_; uint8_t v_suppressElabErrors_451_; lean_object* v___x_452_; lean_object* v___f_453_; lean_object* v_ref_454_; lean_object* v___x_455_; 
v_toCold_449_ = lean_ctor_get(v___y_369_, 0);
v_ref_450_ = lean_ctor_get(v___y_369_, 2);
v_suppressElabErrors_451_ = lean_ctor_get_uint8(v___y_369_, sizeof(void*)*3 + 2);
v___x_452_ = lean_box(v_suppressElabErrors_451_);
v___f_453_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___lam__0___boxed), 2, 1);
lean_closure_set(v___f_453_, 0, v___x_452_);
v_ref_454_ = l_Lean_replaceRef(v_ref_365_, v_ref_450_);
v___x_455_ = l_Lean_Syntax_getPos_x3f(v_ref_454_, v___y_447_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v___x_456_; 
v___x_456_ = lean_unsigned_to_nat(0u);
v___y_437_ = v_suppressElabErrors_451_;
v___y_438_ = v_toCold_449_;
v___y_439_ = v___f_453_;
v___y_440_ = v_ref_454_;
v___y_441_ = v___y_448_;
v___y_442_ = v___y_447_;
v___y_443_ = v___x_456_;
goto v___jp_436_;
}
else
{
lean_object* v_val_457_; 
v_val_457_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_val_457_);
lean_dec_ref_known(v___x_455_, 1);
v___y_437_ = v_suppressElabErrors_451_;
v___y_438_ = v_toCold_449_;
v___y_439_ = v___f_453_;
v___y_440_ = v_ref_454_;
v___y_441_ = v___y_448_;
v___y_442_ = v___y_447_;
v___y_443_ = v_val_457_;
goto v___jp_436_;
}
}
v___jp_459_:
{
uint8_t v___x_461_; uint8_t v___x_462_; 
v___x_461_ = 1;
v___x_462_ = l_Lean_instBEqMessageSeverity_beq(v_severity_367_, v___x_461_);
if (v___x_462_ == 0)
{
v___y_447_ = v___y_460_;
v___y_448_ = v_severity_367_;
goto v___jp_446_;
}
else
{
lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_463_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_369_);
v___x_464_ = l_Lean_warningAsError;
v___x_465_ = l_Lean_Option_get___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__8(v___x_463_, v___x_464_);
lean_dec_ref(v___x_463_);
if (v___x_465_ == 0)
{
v___y_447_ = v___y_460_;
v___y_448_ = v_severity_367_;
goto v___jp_446_;
}
else
{
v___y_447_ = v___y_460_;
v___y_448_ = v___x_458_;
goto v___jp_446_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13___boxed(lean_object* v_ref_470_, lean_object* v_msgData_471_, lean_object* v_severity_472_, lean_object* v_isSilent_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
uint8_t v_severity_boxed_477_; uint8_t v_isSilent_boxed_478_; lean_object* v_res_479_; 
v_severity_boxed_477_ = lean_unbox(v_severity_472_);
v_isSilent_boxed_478_ = lean_unbox(v_isSilent_473_);
v_res_479_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13(v_ref_470_, v_msgData_471_, v_severity_boxed_477_, v_isSilent_boxed_478_, v___y_474_, v___y_475_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v_ref_470_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9(lean_object* v_ref_480_, lean_object* v_msgData_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
uint8_t v___x_485_; uint8_t v___x_486_; lean_object* v___x_487_; 
v___x_485_ = 0;
v___x_486_ = 0;
v___x_487_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9_spec__13(v_ref_480_, v_msgData_481_, v___x_485_, v___x_486_, v___y_482_, v___y_483_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9___boxed(lean_object* v_ref_488_, lean_object* v_msgData_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9(v_ref_488_, v_msgData_489_, v___y_490_, v___y_491_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v_ref_488_);
return v_res_493_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___closed__0));
v___x_496_ = l_Lean_stringToMessageData(v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0(lean_object* v___x_497_, lean_object* v___x_498_, lean_object* v_ref_499_, lean_object* v_x_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v_ref_504_; lean_object* v___x_505_; 
v_ref_504_ = lean_ctor_get(v___y_501_, 2);
v___x_505_ = l_Lean_Idbg_idbgServer(v___x_497_, v___x_498_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_519_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_519_ == 0)
{
v___x_508_ = v___x_505_;
v_isShared_509_ = v_isSharedCheck_519_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_505_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_519_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
if (lean_obj_tag(v_a_506_) == 1)
{
lean_object* v_val_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
lean_del_object(v___x_508_);
v_val_510_ = lean_ctor_get(v_a_506_, 0);
lean_inc(v_val_510_);
lean_dec_ref_known(v_a_506_, 1);
v___x_511_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___closed__1, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___closed__1_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___closed__1);
v___x_512_ = l_Lean_stringToMessageData(v_val_510_);
v___x_513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_511_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
v___x_514_ = l_Lean_logInfoAt___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__9(v_ref_499_, v___x_513_, v___y_501_, v___y_502_);
return v___x_514_;
}
else
{
lean_object* v___x_515_; lean_object* v___x_517_; 
lean_dec(v_a_506_);
v___x_515_ = lean_box(0);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_515_);
v___x_517_ = v___x_508_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_515_);
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
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_531_; 
v_a_520_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_531_ == 0)
{
v___x_522_ = v___x_505_;
v_isShared_523_ = v_isSharedCheck_531_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_505_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_531_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_524_ = lean_io_error_to_string(v_a_520_);
v___x_525_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
v___x_526_ = l_Lean_MessageData_ofFormat(v___x_525_);
lean_inc(v_ref_504_);
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v_ref_504_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v___x_527_);
v___x_529_ = v___x_522_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___boxed(lean_object* v___x_532_, lean_object* v___x_533_, lean_object* v_ref_534_, lean_object* v_x_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0(v___x_532_, v___x_533_, v_ref_534_, v_x_535_, v___y_536_, v___y_537_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v_ref_534_);
lean_dec_ref(v___x_532_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__1(lean_object* v___x_540_, lean_object* v___x_541_, uint8_t v___x_542_, uint8_t v___x_543_, uint8_t v___x_544_, lean_object* v_fVar_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
lean_inc_ref(v_fVar_545_);
v___x_553_ = l_Lean_mkAppN(v_fVar_545_, v___x_540_);
v___x_554_ = lean_array_push(v___x_541_, v_fVar_545_);
v___x_555_ = l_Lean_Meta_mkLambdaFVars(v___x_554_, v___x_553_, v___x_542_, v___x_543_, v___x_542_, v___x_543_, v___x_544_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
lean_dec_ref(v___x_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__1___boxed(lean_object* v___x_556_, lean_object* v___x_557_, lean_object* v___x_558_, lean_object* v___x_559_, lean_object* v___x_560_, lean_object* v_fVar_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
uint8_t v___x_34248__boxed_569_; uint8_t v___x_34249__boxed_570_; uint8_t v___x_34250__boxed_571_; lean_object* v_res_572_; 
v___x_34248__boxed_569_ = lean_unbox(v___x_558_);
v___x_34249__boxed_570_ = lean_unbox(v___x_559_);
v___x_34250__boxed_571_ = lean_unbox(v___x_560_);
v_res_572_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__1(v___x_556_, v___x_557_, v___x_34248__boxed_569_, v___x_34249__boxed_570_, v___x_34250__boxed_571_, v_fVar_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec_ref(v___x_556_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__2(lean_object* v___x_573_, lean_object* v_a_574_, uint8_t v___x_575_, uint8_t v___x_576_, uint8_t v___x_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_Meta_mkLambdaFVars(v___x_573_, v_a_574_, v___x_575_, v___x_576_, v___x_575_, v___x_576_, v___x_577_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v___x_587_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc_n(v_a_586_, 2);
lean_dec_ref_known(v___x_585_, 1);
lean_inc(v___y_581_);
v___x_587_ = lean_infer_type(v_a_586_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v___x_589_; lean_object* v_a_590_; lean_object* v___x_591_; lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_600_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
lean_dec_ref_known(v___x_587_, 1);
v___x_589_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg(v_a_586_, v___y_581_);
v_a_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc(v_a_590_);
lean_dec_ref(v___x_589_);
v___x_591_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg(v_a_588_, v___y_581_);
lean_dec(v___y_581_);
v_a_592_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_600_ == 0)
{
v___x_594_ = v___x_591_;
v_isShared_595_ = v_isSharedCheck_600_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_591_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_600_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_596_, 0, v_a_590_);
lean_ctor_set(v___x_596_, 1, v_a_592_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_596_);
v___x_598_ = v___x_594_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_596_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
else
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
lean_dec(v_a_586_);
lean_dec(v___y_581_);
v_a_601_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_587_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_587_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_601_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
else
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
v_a_609_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_585_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_585_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__2___boxed(lean_object* v___x_617_, lean_object* v_a_618_, lean_object* v___x_619_, lean_object* v___x_620_, lean_object* v___x_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
uint8_t v___x_34290__boxed_629_; uint8_t v___x_34291__boxed_630_; uint8_t v___x_34292__boxed_631_; lean_object* v_res_632_; 
v___x_34290__boxed_629_ = lean_unbox(v___x_619_);
v___x_34291__boxed_630_ = lean_unbox(v___x_620_);
v___x_34292__boxed_631_ = lean_unbox(v___x_621_);
v_res_632_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__2(v___x_617_, v_a_618_, v___x_34290__boxed_629_, v___x_34291__boxed_630_, v___x_34292__boxed_631_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec_ref(v___x_617_);
return v_res_632_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_641_ = lean_box(0);
v___x_642_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__3));
v___x_643_ = l_Lean_Expr_const___override(v___x_642_, v___x_641_);
return v___x_643_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__7(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_648_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__0));
v___x_649_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__6));
v___x_650_ = l_Lean_Expr_const___override(v___x_649_, v___x_648_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10(lean_object* v_as_651_, size_t v_i_652_, size_t v_stop_653_, lean_object* v_b_654_){
_start:
{
uint8_t v___x_655_; 
v___x_655_ = lean_usize_dec_eq(v_i_652_, v_stop_653_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; size_t v___x_657_; size_t v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_656_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4);
v___x_657_ = ((size_t)1ULL);
v___x_658_ = lean_usize_sub(v_i_652_, v___x_657_);
v___x_659_ = lean_array_uget_borrowed(v_as_651_, v___x_658_);
v___x_660_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__7);
lean_inc(v___x_659_);
v___x_661_ = l_Lean_mkApp3(v___x_660_, v___x_656_, v___x_659_, v_b_654_);
v_i_652_ = v___x_658_;
v_b_654_ = v___x_661_;
goto _start;
}
else
{
return v_b_654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___boxed(lean_object* v_as_663_, lean_object* v_i_664_, lean_object* v_stop_665_, lean_object* v_b_666_){
_start:
{
size_t v_i_boxed_667_; size_t v_stop_boxed_668_; lean_object* v_res_669_; 
v_i_boxed_667_ = lean_unbox_usize(v_i_664_);
lean_dec(v_i_664_);
v_stop_boxed_668_ = lean_unbox_usize(v_stop_665_);
lean_dec(v_stop_665_);
v_res_669_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10(v_as_663_, v_i_boxed_667_, v_stop_boxed_668_, v_b_666_);
lean_dec_ref(v_as_663_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7(lean_object* v_init_670_, lean_object* v_l_671_){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_672_ = lean_array_mk(v_l_671_);
v___x_673_ = lean_array_get_size(v___x_672_);
v___x_674_ = lean_unsigned_to_nat(0u);
v___x_675_ = lean_nat_dec_lt(v___x_674_, v___x_673_);
if (v___x_675_ == 0)
{
lean_dec_ref(v___x_672_);
return v_init_670_;
}
else
{
size_t v___x_676_; size_t v___x_677_; lean_object* v___x_678_; 
v___x_676_ = lean_usize_of_nat(v___x_673_);
v___x_677_ = ((size_t)0ULL);
v___x_678_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10(v___x_672_, v___x_676_, v___x_677_, v_init_670_);
lean_dec_ref(v___x_672_);
return v___x_678_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8___redArg(lean_object* v_as_679_, size_t v_sz_680_, size_t v_i_681_, lean_object* v_b_682_){
_start:
{
uint8_t v___x_684_; 
v___x_684_ = lean_usize_dec_lt(v_i_681_, v_sz_680_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; 
v___x_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_685_, 0, v_b_682_);
return v___x_685_;
}
else
{
lean_object* v_snd_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_703_; 
v_snd_686_ = lean_ctor_get(v_b_682_, 1);
v_isSharedCheck_703_ = !lean_is_exclusive(v_b_682_);
if (v_isSharedCheck_703_ == 0)
{
lean_object* v_unused_704_; 
v_unused_704_ = lean_ctor_get(v_b_682_, 0);
lean_dec(v_unused_704_);
v___x_688_ = v_b_682_;
v_isShared_689_ = v_isSharedCheck_703_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_snd_686_);
lean_dec(v_b_682_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_703_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_690_; lean_object* v_a_692_; lean_object* v_a_699_; 
v___x_690_ = lean_box(0);
v_a_699_ = lean_array_uget_borrowed(v_as_679_, v_i_681_);
if (lean_obj_tag(v_a_699_) == 0)
{
v_a_692_ = v_snd_686_;
goto v___jp_691_;
}
else
{
lean_object* v_val_700_; uint8_t v___x_701_; 
v_val_700_ = lean_ctor_get(v_a_699_, 0);
v___x_701_ = l_Lean_LocalDecl_isAuxDecl(v_val_700_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; 
lean_inc(v_val_700_);
v___x_702_ = lean_array_push(v_snd_686_, v_val_700_);
v_a_692_ = v___x_702_;
goto v___jp_691_;
}
else
{
v_a_692_ = v_snd_686_;
goto v___jp_691_;
}
}
v___jp_691_:
{
lean_object* v___x_694_; 
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 1, v_a_692_);
lean_ctor_set(v___x_688_, 0, v___x_690_);
v___x_694_ = v___x_688_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_a_692_);
v___x_694_ = v_reuseFailAlloc_698_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
size_t v___x_695_; size_t v___x_696_; 
v___x_695_ = ((size_t)1ULL);
v___x_696_ = lean_usize_add(v_i_681_, v___x_695_);
v_i_681_ = v___x_696_;
v_b_682_ = v___x_694_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8___redArg___boxed(lean_object* v_as_705_, lean_object* v_sz_706_, lean_object* v_i_707_, lean_object* v_b_708_, lean_object* v___y_709_){
_start:
{
size_t v_sz_boxed_710_; size_t v_i_boxed_711_; lean_object* v_res_712_; 
v_sz_boxed_710_ = lean_unbox_usize(v_sz_706_);
lean_dec(v_sz_706_);
v_i_boxed_711_ = lean_unbox_usize(v_i_707_);
lean_dec(v_i_707_);
v_res_712_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8___redArg(v_as_705_, v_sz_boxed_710_, v_i_boxed_711_, v_b_708_);
lean_dec_ref(v_as_705_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1(lean_object* v_as_713_, size_t v_sz_714_, size_t v_i_715_, lean_object* v_b_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
uint8_t v___x_724_; 
v___x_724_ = lean_usize_dec_lt(v_i_715_, v_sz_714_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; 
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v_b_716_);
return v___x_725_;
}
else
{
lean_object* v_snd_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_743_; 
v_snd_726_ = lean_ctor_get(v_b_716_, 1);
v_isSharedCheck_743_ = !lean_is_exclusive(v_b_716_);
if (v_isSharedCheck_743_ == 0)
{
lean_object* v_unused_744_; 
v_unused_744_ = lean_ctor_get(v_b_716_, 0);
lean_dec(v_unused_744_);
v___x_728_ = v_b_716_;
v_isShared_729_ = v_isSharedCheck_743_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_snd_726_);
lean_dec(v_b_716_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_743_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_730_; lean_object* v_a_732_; lean_object* v_a_739_; 
v___x_730_ = lean_box(0);
v_a_739_ = lean_array_uget_borrowed(v_as_713_, v_i_715_);
if (lean_obj_tag(v_a_739_) == 0)
{
v_a_732_ = v_snd_726_;
goto v___jp_731_;
}
else
{
lean_object* v_val_740_; uint8_t v___x_741_; 
v_val_740_ = lean_ctor_get(v_a_739_, 0);
v___x_741_ = l_Lean_LocalDecl_isAuxDecl(v_val_740_);
if (v___x_741_ == 0)
{
lean_object* v___x_742_; 
lean_inc(v_val_740_);
v___x_742_ = lean_array_push(v_snd_726_, v_val_740_);
v_a_732_ = v___x_742_;
goto v___jp_731_;
}
else
{
v_a_732_ = v_snd_726_;
goto v___jp_731_;
}
}
v___jp_731_:
{
lean_object* v___x_734_; 
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 1, v_a_732_);
lean_ctor_set(v___x_728_, 0, v___x_730_);
v___x_734_ = v___x_728_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_730_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_a_732_);
v___x_734_ = v_reuseFailAlloc_738_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
size_t v___x_735_; size_t v___x_736_; lean_object* v___x_737_; 
v___x_735_ = ((size_t)1ULL);
v___x_736_ = lean_usize_add(v_i_715_, v___x_735_);
v___x_737_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8___redArg(v_as_713_, v_sz_714_, v___x_736_, v___x_734_);
return v___x_737_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1___boxed(lean_object* v_as_745_, lean_object* v_sz_746_, lean_object* v_i_747_, lean_object* v_b_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
size_t v_sz_boxed_756_; size_t v_i_boxed_757_; lean_object* v_res_758_; 
v_sz_boxed_756_ = lean_unbox_usize(v_sz_746_);
lean_dec(v_sz_746_);
v_i_boxed_757_ = lean_unbox_usize(v_i_747_);
lean_dec(v_i_747_);
v_res_758_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1(v_as_745_, v_sz_boxed_756_, v_i_boxed_757_, v_b_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec_ref(v_as_745_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15___redArg(lean_object* v_as_759_, size_t v_sz_760_, size_t v_i_761_, lean_object* v_b_762_){
_start:
{
uint8_t v___x_764_; 
v___x_764_ = lean_usize_dec_lt(v_i_761_, v_sz_760_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; 
v___x_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_765_, 0, v_b_762_);
return v___x_765_;
}
else
{
lean_object* v_snd_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_783_; 
v_snd_766_ = lean_ctor_get(v_b_762_, 1);
v_isSharedCheck_783_ = !lean_is_exclusive(v_b_762_);
if (v_isSharedCheck_783_ == 0)
{
lean_object* v_unused_784_; 
v_unused_784_ = lean_ctor_get(v_b_762_, 0);
lean_dec(v_unused_784_);
v___x_768_ = v_b_762_;
v_isShared_769_ = v_isSharedCheck_783_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_snd_766_);
lean_dec(v_b_762_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_783_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_770_; lean_object* v_a_772_; lean_object* v_a_779_; 
v___x_770_ = lean_box(0);
v_a_779_ = lean_array_uget_borrowed(v_as_759_, v_i_761_);
if (lean_obj_tag(v_a_779_) == 0)
{
v_a_772_ = v_snd_766_;
goto v___jp_771_;
}
else
{
lean_object* v_val_780_; uint8_t v___x_781_; 
v_val_780_ = lean_ctor_get(v_a_779_, 0);
v___x_781_ = l_Lean_LocalDecl_isAuxDecl(v_val_780_);
if (v___x_781_ == 0)
{
lean_object* v___x_782_; 
lean_inc(v_val_780_);
v___x_782_ = lean_array_push(v_snd_766_, v_val_780_);
v_a_772_ = v___x_782_;
goto v___jp_771_;
}
else
{
v_a_772_ = v_snd_766_;
goto v___jp_771_;
}
}
v___jp_771_:
{
lean_object* v___x_774_; 
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 1, v_a_772_);
lean_ctor_set(v___x_768_, 0, v___x_770_);
v___x_774_ = v___x_768_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_770_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_a_772_);
v___x_774_ = v_reuseFailAlloc_778_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
size_t v___x_775_; size_t v___x_776_; 
v___x_775_ = ((size_t)1ULL);
v___x_776_ = lean_usize_add(v_i_761_, v___x_775_);
v_i_761_ = v___x_776_;
v_b_762_ = v___x_774_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15___redArg___boxed(lean_object* v_as_785_, lean_object* v_sz_786_, lean_object* v_i_787_, lean_object* v_b_788_, lean_object* v___y_789_){
_start:
{
size_t v_sz_boxed_790_; size_t v_i_boxed_791_; lean_object* v_res_792_; 
v_sz_boxed_790_ = lean_unbox_usize(v_sz_786_);
lean_dec(v_sz_786_);
v_i_boxed_791_ = lean_unbox_usize(v_i_787_);
lean_dec(v_i_787_);
v_res_792_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15___redArg(v_as_785_, v_sz_boxed_790_, v_i_boxed_791_, v_b_788_);
lean_dec_ref(v_as_785_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6(lean_object* v_as_793_, size_t v_sz_794_, size_t v_i_795_, lean_object* v_b_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
uint8_t v___x_804_; 
v___x_804_ = lean_usize_dec_lt(v_i_795_, v_sz_794_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; 
v___x_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_805_, 0, v_b_796_);
return v___x_805_;
}
else
{
lean_object* v_snd_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_823_; 
v_snd_806_ = lean_ctor_get(v_b_796_, 1);
v_isSharedCheck_823_ = !lean_is_exclusive(v_b_796_);
if (v_isSharedCheck_823_ == 0)
{
lean_object* v_unused_824_; 
v_unused_824_ = lean_ctor_get(v_b_796_, 0);
lean_dec(v_unused_824_);
v___x_808_ = v_b_796_;
v_isShared_809_ = v_isSharedCheck_823_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_snd_806_);
lean_dec(v_b_796_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_823_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_810_; lean_object* v_a_812_; lean_object* v_a_819_; 
v___x_810_ = lean_box(0);
v_a_819_ = lean_array_uget_borrowed(v_as_793_, v_i_795_);
if (lean_obj_tag(v_a_819_) == 0)
{
v_a_812_ = v_snd_806_;
goto v___jp_811_;
}
else
{
lean_object* v_val_820_; uint8_t v___x_821_; 
v_val_820_ = lean_ctor_get(v_a_819_, 0);
v___x_821_ = l_Lean_LocalDecl_isAuxDecl(v_val_820_);
if (v___x_821_ == 0)
{
lean_object* v___x_822_; 
lean_inc(v_val_820_);
v___x_822_ = lean_array_push(v_snd_806_, v_val_820_);
v_a_812_ = v___x_822_;
goto v___jp_811_;
}
else
{
v_a_812_ = v_snd_806_;
goto v___jp_811_;
}
}
v___jp_811_:
{
lean_object* v___x_814_; 
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 1, v_a_812_);
lean_ctor_set(v___x_808_, 0, v___x_810_);
v___x_814_ = v___x_808_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_a_812_);
v___x_814_ = v_reuseFailAlloc_818_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
size_t v___x_815_; size_t v___x_816_; lean_object* v___x_817_; 
v___x_815_ = ((size_t)1ULL);
v___x_816_ = lean_usize_add(v_i_795_, v___x_815_);
v___x_817_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15___redArg(v_as_793_, v_sz_794_, v___x_816_, v___x_814_);
return v___x_817_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6___boxed(lean_object* v_as_825_, lean_object* v_sz_826_, lean_object* v_i_827_, lean_object* v_b_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
size_t v_sz_boxed_836_; size_t v_i_boxed_837_; lean_object* v_res_838_; 
v_sz_boxed_836_ = lean_unbox_usize(v_sz_826_);
lean_dec(v_sz_826_);
v_i_boxed_837_ = lean_unbox_usize(v_i_827_);
lean_dec(v_i_827_);
v_res_838_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6(v_as_825_, v_sz_boxed_836_, v_i_boxed_837_, v_b_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec_ref(v_as_825_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0(lean_object* v_init_839_, lean_object* v_n_840_, lean_object* v_b_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
if (lean_obj_tag(v_n_840_) == 0)
{
lean_object* v_cs_849_; lean_object* v___x_850_; lean_object* v___x_851_; size_t v_sz_852_; size_t v___x_853_; lean_object* v___x_854_; 
v_cs_849_ = lean_ctor_get(v_n_840_, 0);
v___x_850_ = lean_box(0);
v___x_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
lean_ctor_set(v___x_851_, 1, v_b_841_);
v_sz_852_ = lean_array_size(v_cs_849_);
v___x_853_ = ((size_t)0ULL);
v___x_854_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__5(v_init_839_, v_cs_849_, v_sz_852_, v___x_853_, v___x_851_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_869_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_869_ == 0)
{
v___x_857_ = v___x_854_;
v_isShared_858_ = v_isSharedCheck_869_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_854_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_869_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v_fst_859_; 
v_fst_859_ = lean_ctor_get(v_a_855_, 0);
if (lean_obj_tag(v_fst_859_) == 0)
{
lean_object* v_snd_860_; lean_object* v___x_861_; lean_object* v___x_863_; 
v_snd_860_ = lean_ctor_get(v_a_855_, 1);
lean_inc(v_snd_860_);
lean_dec(v_a_855_);
v___x_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_861_, 0, v_snd_860_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_861_);
v___x_863_ = v___x_857_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_861_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
else
{
lean_object* v_val_865_; lean_object* v___x_867_; 
lean_inc_ref(v_fst_859_);
lean_dec(v_a_855_);
v_val_865_ = lean_ctor_get(v_fst_859_, 0);
lean_inc(v_val_865_);
lean_dec_ref_known(v_fst_859_, 1);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v_val_865_);
v___x_867_ = v___x_857_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_val_865_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
v_a_870_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_854_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_854_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
else
{
lean_object* v_vs_878_; lean_object* v___x_879_; lean_object* v___x_880_; size_t v_sz_881_; size_t v___x_882_; lean_object* v___x_883_; 
v_vs_878_ = lean_ctor_get(v_n_840_, 0);
v___x_879_ = lean_box(0);
v___x_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
lean_ctor_set(v___x_880_, 1, v_b_841_);
v_sz_881_ = lean_array_size(v_vs_878_);
v___x_882_ = ((size_t)0ULL);
v___x_883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6(v_vs_878_, v_sz_881_, v___x_882_, v___x_880_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_898_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_898_ == 0)
{
v___x_886_ = v___x_883_;
v_isShared_887_ = v_isSharedCheck_898_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_883_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_898_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v_fst_888_; 
v_fst_888_ = lean_ctor_get(v_a_884_, 0);
if (lean_obj_tag(v_fst_888_) == 0)
{
lean_object* v_snd_889_; lean_object* v___x_890_; lean_object* v___x_892_; 
v_snd_889_ = lean_ctor_get(v_a_884_, 1);
lean_inc(v_snd_889_);
lean_dec(v_a_884_);
v___x_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_890_, 0, v_snd_889_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v___x_890_);
v___x_892_ = v___x_886_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
else
{
lean_object* v_val_894_; lean_object* v___x_896_; 
lean_inc_ref(v_fst_888_);
lean_dec(v_a_884_);
v_val_894_ = lean_ctor_get(v_fst_888_, 0);
lean_inc(v_val_894_);
lean_dec_ref_known(v_fst_888_, 1);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v_val_894_);
v___x_896_ = v___x_886_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_val_894_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
v_a_899_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_883_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_883_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__5(lean_object* v_init_907_, lean_object* v_as_908_, size_t v_sz_909_, size_t v_i_910_, lean_object* v_b_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
uint8_t v___x_919_; 
v___x_919_ = lean_usize_dec_lt(v_i_910_, v_sz_909_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; 
v___x_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_920_, 0, v_b_911_);
return v___x_920_;
}
else
{
lean_object* v_snd_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_955_; 
v_snd_921_ = lean_ctor_get(v_b_911_, 1);
v_isSharedCheck_955_ = !lean_is_exclusive(v_b_911_);
if (v_isSharedCheck_955_ == 0)
{
lean_object* v_unused_956_; 
v_unused_956_ = lean_ctor_get(v_b_911_, 0);
lean_dec(v_unused_956_);
v___x_923_ = v_b_911_;
v_isShared_924_ = v_isSharedCheck_955_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_snd_921_);
lean_dec(v_b_911_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_955_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_925_; lean_object* v_a_926_; lean_object* v___x_927_; 
v___x_925_ = lean_box(0);
v_a_926_ = lean_array_uget_borrowed(v_as_908_, v_i_910_);
lean_inc(v_snd_921_);
v___x_927_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0(v_init_907_, v_a_926_, v_snd_921_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_946_; 
v_a_928_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_946_ == 0)
{
v___x_930_ = v___x_927_;
v_isShared_931_ = v_isSharedCheck_946_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_927_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_946_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
if (lean_obj_tag(v_a_928_) == 0)
{
lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_932_, 0, v_a_928_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v___x_932_);
v___x_934_ = v___x_923_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_932_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v_snd_921_);
v___x_934_ = v_reuseFailAlloc_938_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
lean_object* v___x_936_; 
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v___x_934_);
v___x_936_ = v___x_930_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_934_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
else
{
lean_object* v_a_939_; lean_object* v___x_941_; 
lean_del_object(v___x_930_);
lean_dec(v_snd_921_);
v_a_939_ = lean_ctor_get(v_a_928_, 0);
lean_inc(v_a_939_);
lean_dec_ref_known(v_a_928_, 1);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 1, v_a_939_);
lean_ctor_set(v___x_923_, 0, v___x_925_);
v___x_941_ = v___x_923_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_925_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v_a_939_);
v___x_941_ = v_reuseFailAlloc_945_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
size_t v___x_942_; size_t v___x_943_; 
v___x_942_ = ((size_t)1ULL);
v___x_943_ = lean_usize_add(v_i_910_, v___x_942_);
v_i_910_ = v___x_943_;
v_b_911_ = v___x_941_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
lean_del_object(v___x_923_);
lean_dec(v_snd_921_);
v_a_947_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___x_927_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_927_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
if (v_isShared_950_ == 0)
{
v___x_952_ = v___x_949_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_947_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__5___boxed(lean_object* v_init_957_, lean_object* v_as_958_, lean_object* v_sz_959_, lean_object* v_i_960_, lean_object* v_b_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
size_t v_sz_boxed_969_; size_t v_i_boxed_970_; lean_object* v_res_971_; 
v_sz_boxed_969_ = lean_unbox_usize(v_sz_959_);
lean_dec(v_sz_959_);
v_i_boxed_970_ = lean_unbox_usize(v_i_960_);
lean_dec(v_i_960_);
v_res_971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__5(v_init_957_, v_as_958_, v_sz_boxed_969_, v_i_boxed_970_, v_b_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec_ref(v_as_958_);
lean_dec_ref(v_init_957_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0___boxed(lean_object* v_init_972_, lean_object* v_n_973_, lean_object* v_b_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0(v_init_972_, v_n_973_, v_b_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec_ref(v_n_973_);
lean_dec_ref(v_init_972_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0(lean_object* v_t_983_, lean_object* v_init_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v_root_992_; lean_object* v_tail_993_; lean_object* v___x_994_; 
v_root_992_ = lean_ctor_get(v_t_983_, 0);
v_tail_993_ = lean_ctor_get(v_t_983_, 1);
lean_inc_ref(v_init_984_);
v___x_994_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0(v_init_984_, v_root_992_, v_init_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
lean_dec_ref(v_init_984_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1031_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_997_ = v___x_994_;
v_isShared_998_ = v_isSharedCheck_1031_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_994_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1031_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
if (lean_obj_tag(v_a_995_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1001_; 
v_a_999_ = lean_ctor_get(v_a_995_, 0);
lean_inc(v_a_999_);
lean_dec_ref_known(v_a_995_, 1);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v_a_999_);
v___x_1001_ = v___x_997_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; size_t v_sz_1006_; size_t v___x_1007_; lean_object* v___x_1008_; 
lean_del_object(v___x_997_);
v_a_1003_ = lean_ctor_get(v_a_995_, 0);
lean_inc(v_a_1003_);
lean_dec_ref_known(v_a_995_, 1);
v___x_1004_ = lean_box(0);
v___x_1005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
lean_ctor_set(v___x_1005_, 1, v_a_1003_);
v_sz_1006_ = lean_array_size(v_tail_993_);
v___x_1007_ = ((size_t)0ULL);
v___x_1008_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1(v_tail_993_, v_sz_1006_, v___x_1007_, v___x_1005_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1022_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1011_ = v___x_1008_;
v_isShared_1012_ = v_isSharedCheck_1022_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1008_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1022_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v_fst_1013_; 
v_fst_1013_ = lean_ctor_get(v_a_1009_, 0);
if (lean_obj_tag(v_fst_1013_) == 0)
{
lean_object* v_snd_1014_; lean_object* v___x_1016_; 
v_snd_1014_ = lean_ctor_get(v_a_1009_, 1);
lean_inc(v_snd_1014_);
lean_dec(v_a_1009_);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v_snd_1014_);
v___x_1016_ = v___x_1011_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_snd_1014_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
else
{
lean_object* v_val_1018_; lean_object* v___x_1020_; 
lean_inc_ref(v_fst_1013_);
lean_dec(v_a_1009_);
v_val_1018_ = lean_ctor_get(v_fst_1013_, 0);
lean_inc(v_val_1018_);
lean_dec_ref_known(v_fst_1013_, 1);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v_val_1018_);
v___x_1020_ = v___x_1011_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_val_1018_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
v_a_1023_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_1008_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1008_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
v_a_1032_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_994_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_994_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0___boxed(lean_object* v_t_1040_, lean_object* v_init_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0(v_t_1040_, v_init_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec_ref(v_t_1040_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__1(size_t v_sz_1050_, size_t v_i_1051_, lean_object* v_bs_1052_){
_start:
{
uint8_t v___x_1053_; 
v___x_1053_ = lean_usize_dec_lt(v_i_1051_, v_sz_1050_);
if (v___x_1053_ == 0)
{
return v_bs_1052_;
}
else
{
lean_object* v_v_1054_; lean_object* v___x_1055_; lean_object* v_bs_x27_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; size_t v___x_1059_; size_t v___x_1060_; lean_object* v___x_1061_; 
v_v_1054_ = lean_array_uget(v_bs_1052_, v_i_1051_);
v___x_1055_ = lean_unsigned_to_nat(0u);
v_bs_x27_1056_ = lean_array_uset(v_bs_1052_, v_i_1051_, v___x_1055_);
v___x_1057_ = l_Lean_LocalDecl_fvarId(v_v_1054_);
lean_dec(v_v_1054_);
v___x_1058_ = l_Lean_mkFVar(v___x_1057_);
v___x_1059_ = ((size_t)1ULL);
v___x_1060_ = lean_usize_add(v_i_1051_, v___x_1059_);
v___x_1061_ = lean_array_uset(v_bs_x27_1056_, v_i_1051_, v___x_1058_);
v_i_1051_ = v___x_1060_;
v_bs_1052_ = v___x_1061_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__1___boxed(lean_object* v_sz_1063_, lean_object* v_i_1064_, lean_object* v_bs_1065_){
_start:
{
size_t v_sz_boxed_1066_; size_t v_i_boxed_1067_; lean_object* v_res_1068_; 
v_sz_boxed_1066_ = lean_unbox_usize(v_sz_1063_);
lean_dec(v_sz_1063_);
v_i_boxed_1067_ = lean_unbox_usize(v_i_1064_);
lean_dec(v_i_1064_);
v_res_1068_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__1(v_sz_boxed_1066_, v_i_boxed_1067_, v_bs_1065_);
return v_res_1068_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__2(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1074_ = lean_box(0);
v___x_1075_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__1));
v___x_1076_ = l_Lean_Expr_const___override(v___x_1075_, v___x_1074_);
return v___x_1076_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1082_ = lean_box(0);
v___x_1083_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__5));
v___x_1084_ = l_Lean_mkConst(v___x_1083_, v___x_1082_);
return v___x_1084_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1089_ = lean_box(0);
v___x_1090_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__8));
v___x_1091_ = l_Lean_mkConst(v___x_1090_, v___x_1089_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg(size_t v_sz_1092_, size_t v_i_1093_, lean_object* v_bs_1094_){
_start:
{
uint8_t v___x_1096_; 
v___x_1096_ = lean_usize_dec_lt(v_i_1093_, v_sz_1092_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; 
v___x_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1097_, 0, v_bs_1094_);
return v___x_1097_;
}
else
{
lean_object* v_v_1098_; lean_object* v_module_1099_; uint8_t v_importAll_1100_; uint8_t v_isExported_1101_; uint8_t v_isMeta_1102_; lean_object* v___x_1103_; lean_object* v_bs_x27_1104_; lean_object* v___x_1105_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1128_; 
v_v_1098_ = lean_array_uget_borrowed(v_bs_1094_, v_i_1093_);
v_module_1099_ = lean_ctor_get(v_v_1098_, 0);
lean_inc(v_module_1099_);
v_importAll_1100_ = lean_ctor_get_uint8(v_v_1098_, sizeof(void*)*1);
v_isExported_1101_ = lean_ctor_get_uint8(v_v_1098_, sizeof(void*)*1 + 1);
v_isMeta_1102_ = lean_ctor_get_uint8(v_v_1098_, sizeof(void*)*1 + 2);
v___x_1103_ = lean_unsigned_to_nat(0u);
v_bs_x27_1104_ = lean_array_uset(v_bs_1094_, v_i_1093_, v___x_1103_);
v___x_1105_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_module_1099_);
if (v_importAll_1100_ == 0)
{
lean_object* v___x_1131_; 
v___x_1131_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6);
v___y_1128_ = v___x_1131_;
goto v___jp_1127_;
}
else
{
lean_object* v___x_1132_; 
v___x_1132_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9);
v___y_1128_ = v___x_1132_;
goto v___jp_1127_;
}
v___jp_1106_:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; size_t v___x_1118_; size_t v___x_1119_; lean_object* v___x_1120_; 
v___x_1110_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__2);
v___x_1111_ = lean_unsigned_to_nat(4u);
v___x_1112_ = lean_mk_empty_array_with_capacity(v___x_1111_);
v___x_1113_ = lean_array_push(v___x_1112_, v___x_1105_);
lean_inc_ref(v___y_1108_);
v___x_1114_ = lean_array_push(v___x_1113_, v___y_1108_);
lean_inc_ref(v___y_1107_);
v___x_1115_ = lean_array_push(v___x_1114_, v___y_1107_);
lean_inc_ref(v___y_1109_);
v___x_1116_ = lean_array_push(v___x_1115_, v___y_1109_);
v___x_1117_ = l_Lean_mkAppN(v___x_1110_, v___x_1116_);
lean_dec_ref(v___x_1116_);
v___x_1118_ = ((size_t)1ULL);
v___x_1119_ = lean_usize_add(v_i_1093_, v___x_1118_);
v___x_1120_ = lean_array_uset(v_bs_x27_1104_, v_i_1093_, v___x_1117_);
v_i_1093_ = v___x_1119_;
v_bs_1094_ = v___x_1120_;
goto _start;
}
v___jp_1122_:
{
if (v_isMeta_1102_ == 0)
{
lean_object* v___x_1125_; 
v___x_1125_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6);
v___y_1107_ = v___y_1124_;
v___y_1108_ = v___y_1123_;
v___y_1109_ = v___x_1125_;
goto v___jp_1106_;
}
else
{
lean_object* v___x_1126_; 
v___x_1126_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9);
v___y_1107_ = v___y_1124_;
v___y_1108_ = v___y_1123_;
v___y_1109_ = v___x_1126_;
goto v___jp_1106_;
}
}
v___jp_1127_:
{
if (v_isExported_1101_ == 0)
{
lean_object* v___x_1129_; 
v___x_1129_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__6);
v___y_1123_ = v___y_1128_;
v___y_1124_ = v___x_1129_;
goto v___jp_1122_;
}
else
{
lean_object* v___x_1130_; 
v___x_1130_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___closed__9);
v___y_1123_ = v___y_1128_;
v___y_1124_ = v___x_1130_;
goto v___jp_1122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg___boxed(lean_object* v_sz_1133_, lean_object* v_i_1134_, lean_object* v_bs_1135_, lean_object* v___y_1136_){
_start:
{
size_t v_sz_boxed_1137_; size_t v_i_boxed_1138_; lean_object* v_res_1139_; 
v_sz_boxed_1137_ = lean_unbox_usize(v_sz_1133_);
lean_dec(v_sz_1133_);
v_i_boxed_1138_ = lean_unbox_usize(v_i_1134_);
lean_dec(v_i_1134_);
v_res_1139_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg(v_sz_boxed_1137_, v_i_boxed_1138_, v_bs_1135_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12_spec__20___redArg(lean_object* v_x_1140_, lean_object* v_x_1141_, lean_object* v_x_1142_, lean_object* v_x_1143_){
_start:
{
lean_object* v_ks_1144_; lean_object* v_vs_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1169_; 
v_ks_1144_ = lean_ctor_get(v_x_1140_, 0);
v_vs_1145_ = lean_ctor_get(v_x_1140_, 1);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_x_1140_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1147_ = v_x_1140_;
v_isShared_1148_ = v_isSharedCheck_1169_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_vs_1145_);
lean_inc(v_ks_1144_);
lean_dec(v_x_1140_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1169_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1149_; uint8_t v___x_1150_; 
v___x_1149_ = lean_array_get_size(v_ks_1144_);
v___x_1150_ = lean_nat_dec_lt(v_x_1141_, v___x_1149_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1154_; 
lean_dec(v_x_1141_);
v___x_1151_ = lean_array_push(v_ks_1144_, v_x_1142_);
v___x_1152_ = lean_array_push(v_vs_1145_, v_x_1143_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 1, v___x_1152_);
lean_ctor_set(v___x_1147_, 0, v___x_1151_);
v___x_1154_ = v___x_1147_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v___x_1152_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
else
{
lean_object* v_k_x27_1156_; uint8_t v___x_1157_; 
v_k_x27_1156_ = lean_array_fget_borrowed(v_ks_1144_, v_x_1141_);
v___x_1157_ = l_Lean_instBEqFVarId_beq(v_x_1142_, v_k_x27_1156_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1159_; 
if (v_isShared_1148_ == 0)
{
v___x_1159_ = v___x_1147_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_ks_1144_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v_vs_1145_);
v___x_1159_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = lean_unsigned_to_nat(1u);
v___x_1161_ = lean_nat_add(v_x_1141_, v___x_1160_);
lean_dec(v_x_1141_);
v_x_1140_ = v___x_1159_;
v_x_1141_ = v___x_1161_;
goto _start;
}
}
else
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1167_; 
v___x_1164_ = lean_array_fset(v_ks_1144_, v_x_1141_, v_x_1142_);
v___x_1165_ = lean_array_fset(v_vs_1145_, v_x_1141_, v_x_1143_);
lean_dec(v_x_1141_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 1, v___x_1165_);
lean_ctor_set(v___x_1147_, 0, v___x_1164_);
v___x_1167_ = v___x_1147_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1164_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v___x_1165_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12___redArg(lean_object* v_n_1170_, lean_object* v_k_1171_, lean_object* v_v_1172_){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = lean_unsigned_to_nat(0u);
v___x_1174_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12_spec__20___redArg(v_n_1170_, v___x_1173_, v_k_1171_, v_v_1172_);
return v___x_1174_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg(lean_object* v_x_1176_, size_t v_x_1177_, size_t v_x_1178_, lean_object* v_x_1179_, lean_object* v_x_1180_){
_start:
{
if (lean_obj_tag(v_x_1176_) == 0)
{
lean_object* v_es_1181_; size_t v___x_1182_; size_t v___x_1183_; lean_object* v_j_1184_; lean_object* v___x_1185_; uint8_t v___x_1186_; 
v_es_1181_ = lean_ctor_get(v_x_1176_, 0);
v___x_1182_ = ((size_t)31ULL);
v___x_1183_ = lean_usize_land(v_x_1177_, v___x_1182_);
v_j_1184_ = lean_usize_to_nat(v___x_1183_);
v___x_1185_ = lean_array_get_size(v_es_1181_);
v___x_1186_ = lean_nat_dec_lt(v_j_1184_, v___x_1185_);
if (v___x_1186_ == 0)
{
lean_dec(v_j_1184_);
lean_dec(v_x_1180_);
lean_dec(v_x_1179_);
return v_x_1176_;
}
else
{
lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1225_; 
lean_inc_ref(v_es_1181_);
v_isSharedCheck_1225_ = !lean_is_exclusive(v_x_1176_);
if (v_isSharedCheck_1225_ == 0)
{
lean_object* v_unused_1226_; 
v_unused_1226_ = lean_ctor_get(v_x_1176_, 0);
lean_dec(v_unused_1226_);
v___x_1188_ = v_x_1176_;
v_isShared_1189_ = v_isSharedCheck_1225_;
goto v_resetjp_1187_;
}
else
{
lean_dec(v_x_1176_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1225_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v_v_1190_; lean_object* v___x_1191_; lean_object* v_xs_x27_1192_; lean_object* v___y_1194_; 
v_v_1190_ = lean_array_fget(v_es_1181_, v_j_1184_);
v___x_1191_ = lean_box(0);
v_xs_x27_1192_ = lean_array_fset(v_es_1181_, v_j_1184_, v___x_1191_);
switch(lean_obj_tag(v_v_1190_))
{
case 0:
{
lean_object* v_key_1199_; lean_object* v_val_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1210_; 
v_key_1199_ = lean_ctor_get(v_v_1190_, 0);
v_val_1200_ = lean_ctor_get(v_v_1190_, 1);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_v_1190_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1202_ = v_v_1190_;
v_isShared_1203_ = v_isSharedCheck_1210_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_val_1200_);
lean_inc(v_key_1199_);
lean_dec(v_v_1190_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1210_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
uint8_t v___x_1204_; 
v___x_1204_ = l_Lean_instBEqFVarId_beq(v_x_1179_, v_key_1199_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_del_object(v___x_1202_);
v___x_1205_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1199_, v_val_1200_, v_x_1179_, v_x_1180_);
v___x_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
v___y_1194_ = v___x_1206_;
goto v___jp_1193_;
}
else
{
lean_object* v___x_1208_; 
lean_dec(v_val_1200_);
lean_dec(v_key_1199_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 1, v_x_1180_);
lean_ctor_set(v___x_1202_, 0, v_x_1179_);
v___x_1208_ = v___x_1202_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_x_1179_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_x_1180_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
v___y_1194_ = v___x_1208_;
goto v___jp_1193_;
}
}
}
}
case 1:
{
lean_object* v_node_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1223_; 
v_node_1211_ = lean_ctor_get(v_v_1190_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_v_1190_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1213_ = v_v_1190_;
v_isShared_1214_ = v_isSharedCheck_1223_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_node_1211_);
lean_dec(v_v_1190_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1223_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
size_t v___x_1215_; size_t v___x_1216_; size_t v___x_1217_; size_t v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1221_; 
v___x_1215_ = ((size_t)5ULL);
v___x_1216_ = lean_usize_shift_right(v_x_1177_, v___x_1215_);
v___x_1217_ = ((size_t)1ULL);
v___x_1218_ = lean_usize_add(v_x_1178_, v___x_1217_);
v___x_1219_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg(v_node_1211_, v___x_1216_, v___x_1218_, v_x_1179_, v_x_1180_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v___x_1219_);
v___x_1221_ = v___x_1213_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1219_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
v___y_1194_ = v___x_1221_;
goto v___jp_1193_;
}
}
}
default: 
{
lean_object* v___x_1224_; 
v___x_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1224_, 0, v_x_1179_);
lean_ctor_set(v___x_1224_, 1, v_x_1180_);
v___y_1194_ = v___x_1224_;
goto v___jp_1193_;
}
}
v___jp_1193_:
{
lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1195_ = lean_array_fset(v_xs_x27_1192_, v_j_1184_, v___y_1194_);
lean_dec(v_j_1184_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1195_);
v___x_1197_ = v___x_1188_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
}
else
{
lean_object* v_ks_1227_; lean_object* v_vs_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1246_; 
v_ks_1227_ = lean_ctor_get(v_x_1176_, 0);
v_vs_1228_ = lean_ctor_get(v_x_1176_, 1);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_x_1176_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1230_ = v_x_1176_;
v_isShared_1231_ = v_isSharedCheck_1246_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_vs_1228_);
lean_inc(v_ks_1227_);
lean_dec(v_x_1176_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1246_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_ks_1227_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_vs_1228_);
v___x_1233_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
lean_object* v_newNode_1234_; size_t v___x_1235_; uint8_t v___x_1236_; 
v_newNode_1234_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12___redArg(v___x_1233_, v_x_1179_, v_x_1180_);
v___x_1235_ = ((size_t)7ULL);
v___x_1236_ = lean_usize_dec_le(v___x_1235_, v_x_1178_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; 
v___x_1237_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1234_);
v___x_1238_ = lean_unsigned_to_nat(4u);
v___x_1239_ = lean_nat_dec_lt(v___x_1237_, v___x_1238_);
lean_dec(v___x_1237_);
if (v___x_1239_ == 0)
{
lean_object* v_ks_1240_; lean_object* v_vs_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v_ks_1240_ = lean_ctor_get(v_newNode_1234_, 0);
lean_inc_ref(v_ks_1240_);
v_vs_1241_ = lean_ctor_get(v_newNode_1234_, 1);
lean_inc_ref(v_vs_1241_);
lean_dec_ref(v_newNode_1234_);
v___x_1242_ = lean_unsigned_to_nat(0u);
v___x_1243_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg___closed__0);
v___x_1244_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13___redArg(v_x_1178_, v_ks_1240_, v_vs_1241_, v___x_1242_, v___x_1243_);
lean_dec_ref(v_vs_1241_);
lean_dec_ref(v_ks_1240_);
return v___x_1244_;
}
else
{
return v_newNode_1234_;
}
}
else
{
return v_newNode_1234_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13___redArg(size_t v_depth_1247_, lean_object* v_keys_1248_, lean_object* v_vals_1249_, lean_object* v_i_1250_, lean_object* v_entries_1251_){
_start:
{
lean_object* v___x_1252_; uint8_t v___x_1253_; 
v___x_1252_ = lean_array_get_size(v_keys_1248_);
v___x_1253_ = lean_nat_dec_lt(v_i_1250_, v___x_1252_);
if (v___x_1253_ == 0)
{
lean_dec(v_i_1250_);
return v_entries_1251_;
}
else
{
lean_object* v_k_1254_; lean_object* v_v_1255_; uint64_t v___x_1256_; size_t v_h_1257_; size_t v___x_1258_; lean_object* v___x_1259_; size_t v___x_1260_; size_t v___x_1261_; size_t v___x_1262_; size_t v_h_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v_k_1254_ = lean_array_fget_borrowed(v_keys_1248_, v_i_1250_);
v_v_1255_ = lean_array_fget_borrowed(v_vals_1249_, v_i_1250_);
v___x_1256_ = l_Lean_instHashableFVarId_hash(v_k_1254_);
v_h_1257_ = lean_uint64_to_usize(v___x_1256_);
v___x_1258_ = ((size_t)5ULL);
v___x_1259_ = lean_unsigned_to_nat(1u);
v___x_1260_ = ((size_t)1ULL);
v___x_1261_ = lean_usize_sub(v_depth_1247_, v___x_1260_);
v___x_1262_ = lean_usize_mul(v___x_1258_, v___x_1261_);
v_h_1263_ = lean_usize_shift_right(v_h_1257_, v___x_1262_);
v___x_1264_ = lean_nat_add(v_i_1250_, v___x_1259_);
lean_dec(v_i_1250_);
lean_inc(v_v_1255_);
lean_inc(v_k_1254_);
v___x_1265_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg(v_entries_1251_, v_h_1263_, v_depth_1247_, v_k_1254_, v_v_1255_);
v_i_1250_ = v___x_1264_;
v_entries_1251_ = v___x_1265_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13___redArg___boxed(lean_object* v_depth_1267_, lean_object* v_keys_1268_, lean_object* v_vals_1269_, lean_object* v_i_1270_, lean_object* v_entries_1271_){
_start:
{
size_t v_depth_boxed_1272_; lean_object* v_res_1273_; 
v_depth_boxed_1272_ = lean_unbox_usize(v_depth_1267_);
lean_dec(v_depth_1267_);
v_res_1273_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13___redArg(v_depth_boxed_1272_, v_keys_1268_, v_vals_1269_, v_i_1270_, v_entries_1271_);
lean_dec_ref(v_vals_1269_);
lean_dec_ref(v_keys_1268_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg___boxed(lean_object* v_x_1274_, lean_object* v_x_1275_, lean_object* v_x_1276_, lean_object* v_x_1277_, lean_object* v_x_1278_){
_start:
{
size_t v_x_35263__boxed_1279_; size_t v_x_35264__boxed_1280_; lean_object* v_res_1281_; 
v_x_35263__boxed_1279_ = lean_unbox_usize(v_x_1275_);
lean_dec(v_x_1275_);
v_x_35264__boxed_1280_ = lean_unbox_usize(v_x_1276_);
lean_dec(v_x_1276_);
v_res_1281_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg(v_x_1274_, v_x_35263__boxed_1279_, v_x_35264__boxed_1280_, v_x_1277_, v_x_1278_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2___redArg(lean_object* v_x_1282_, lean_object* v_x_1283_, lean_object* v_x_1284_){
_start:
{
uint64_t v___x_1285_; size_t v___x_1286_; size_t v___x_1287_; lean_object* v___x_1288_; 
v___x_1285_ = l_Lean_instHashableFVarId_hash(v_x_1283_);
v___x_1286_ = lean_uint64_to_usize(v___x_1285_);
v___x_1287_ = ((size_t)1ULL);
v___x_1288_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg(v_x_1282_, v___x_1286_, v___x_1287_, v_x_1283_, v_x_1284_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__11(lean_object* v_as_1289_, size_t v_i_1290_, size_t v_stop_1291_, lean_object* v_b_1292_){
_start:
{
lean_object* v___y_1294_; uint8_t v___x_1298_; 
v___x_1298_ = lean_usize_dec_eq(v_i_1290_, v_stop_1291_);
if (v___x_1298_ == 0)
{
lean_object* v_fvarIdToDecl_1299_; lean_object* v_decls_1300_; lean_object* v_auxDeclToFullName_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v_fvarIdToDecl_1299_ = lean_ctor_get(v_b_1292_, 0);
v_decls_1300_ = lean_ctor_get(v_b_1292_, 1);
v_auxDeclToFullName_1301_ = lean_ctor_get(v_b_1292_, 2);
v___x_1302_ = lean_array_uget_borrowed(v_as_1289_, v_i_1290_);
v___x_1303_ = l_Lean_LocalDecl_fvarId(v___x_1302_);
lean_inc_ref(v_b_1292_);
v___x_1304_ = lean_local_ctx_find(v_b_1292_, v___x_1303_);
if (lean_obj_tag(v___x_1304_) == 0)
{
v___y_1294_ = v_b_1292_;
goto v___jp_1293_;
}
else
{
lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1330_; 
lean_inc(v_auxDeclToFullName_1301_);
lean_inc_ref(v_decls_1300_);
lean_inc_ref(v_fvarIdToDecl_1299_);
v_isSharedCheck_1330_ = !lean_is_exclusive(v_b_1292_);
if (v_isSharedCheck_1330_ == 0)
{
lean_object* v_unused_1331_; lean_object* v_unused_1332_; lean_object* v_unused_1333_; 
v_unused_1331_ = lean_ctor_get(v_b_1292_, 2);
lean_dec(v_unused_1331_);
v_unused_1332_ = lean_ctor_get(v_b_1292_, 1);
lean_dec(v_unused_1332_);
v_unused_1333_ = lean_ctor_get(v_b_1292_, 0);
lean_dec(v_unused_1333_);
v___x_1306_ = v_b_1292_;
v_isShared_1307_ = v_isSharedCheck_1330_;
goto v_resetjp_1305_;
}
else
{
lean_dec(v_b_1292_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1330_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v_val_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1329_; 
v_val_1308_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1310_ = v___x_1304_;
v_isShared_1311_ = v_isSharedCheck_1329_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_val_1308_);
lean_dec(v___x_1304_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1329_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
uint8_t v___x_1312_; lean_object* v___x_1313_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1325_; lean_object* v_fvarId_1328_; 
v___x_1312_ = 1;
v___x_1313_ = l_Lean_LocalDecl_setNondep(v_val_1308_, v___x_1312_);
v_fvarId_1328_ = lean_ctor_get(v___x_1313_, 1);
lean_inc(v_fvarId_1328_);
v___y_1325_ = v_fvarId_1328_;
goto v___jp_1324_;
v___jp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v___x_1313_);
v___x_1318_ = v___x_1310_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1313_);
v___x_1318_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
lean_object* v___x_1319_; lean_object* v___x_1321_; 
v___x_1319_ = l_Lean_PersistentArray_set___redArg(v_decls_1300_, v___y_1316_, v___x_1318_);
lean_dec(v___y_1316_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 1, v___x_1319_);
lean_ctor_set(v___x_1306_, 0, v___y_1315_);
v___x_1321_ = v___x_1306_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___y_1315_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v___x_1319_);
lean_ctor_set(v_reuseFailAlloc_1322_, 2, v_auxDeclToFullName_1301_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
v___y_1294_ = v___x_1321_;
goto v___jp_1293_;
}
}
}
v___jp_1324_:
{
lean_object* v___x_1326_; lean_object* v_index_1327_; 
lean_inc_ref(v___x_1313_);
v___x_1326_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2___redArg(v_fvarIdToDecl_1299_, v___y_1325_, v___x_1313_);
v_index_1327_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_index_1327_);
v___y_1315_ = v___x_1326_;
v___y_1316_ = v_index_1327_;
goto v___jp_1314_;
}
}
}
}
}
else
{
return v_b_1292_;
}
v___jp_1293_:
{
size_t v___x_1295_; size_t v___x_1296_; 
v___x_1295_ = ((size_t)1ULL);
v___x_1296_ = lean_usize_add(v_i_1290_, v___x_1295_);
v_i_1290_ = v___x_1296_;
v_b_1292_ = v___y_1294_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__11___boxed(lean_object* v_as_1334_, lean_object* v_i_1335_, lean_object* v_stop_1336_, lean_object* v_b_1337_){
_start:
{
size_t v_i_boxed_1338_; size_t v_stop_boxed_1339_; lean_object* v_res_1340_; 
v_i_boxed_1338_ = lean_unbox_usize(v_i_1335_);
lean_dec(v_i_1335_);
v_stop_boxed_1339_ = lean_unbox_usize(v_stop_1336_);
lean_dec(v_stop_1336_);
v_res_1340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__11(v_as_1334_, v_i_boxed_1338_, v_stop_boxed_1339_, v_b_1337_);
lean_dec_ref(v_as_1334_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__15(lean_object* v_msgData_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v___x_1347_; lean_object* v_env_1348_; uint8_t v___x_1349_; lean_object* v_env_1350_; lean_object* v___x_1351_; lean_object* v_toCold_1352_; lean_object* v_mctx_1353_; lean_object* v_lctx_1354_; lean_object* v_options_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1347_ = lean_st_ref_get(v___y_1345_);
v_env_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc_ref(v_env_1348_);
lean_dec(v___x_1347_);
v___x_1349_ = 0;
v_env_1350_ = l_Lean_Environment_setRecordingDeps(v_env_1348_, v___x_1349_);
v___x_1351_ = lean_st_ref_get(v___y_1343_);
v_toCold_1352_ = lean_ctor_get(v___y_1344_, 0);
v_mctx_1353_ = lean_ctor_get(v___x_1351_, 0);
lean_inc_ref(v_mctx_1353_);
lean_dec(v___x_1351_);
v_lctx_1354_ = lean_ctor_get(v___y_1342_, 2);
v_options_1355_ = lean_ctor_get(v_toCold_1352_, 2);
lean_inc_ref(v_options_1355_);
lean_inc_ref(v_lctx_1354_);
v___x_1356_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1356_, 0, v_env_1350_);
lean_ctor_set(v___x_1356_, 1, v_mctx_1353_);
lean_ctor_set(v___x_1356_, 2, v_lctx_1354_);
lean_ctor_set(v___x_1356_, 3, v_options_1355_);
v___x_1357_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1356_);
lean_ctor_set(v___x_1357_, 1, v_msgData_1341_);
v___x_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__15___boxed(lean_object* v_msgData_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__15(v_msgData_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
return v_res_1365_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__0(void){
_start:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = lean_box(1);
v___x_1367_ = l_Lean_MessageData_ofFormat(v___x_1366_);
return v___x_1367_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__3(void){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__2));
v___x_1372_ = l_Lean_MessageData_ofFormat(v___x_1371_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23(lean_object* v_x_1373_, lean_object* v_x_1374_){
_start:
{
if (lean_obj_tag(v_x_1374_) == 0)
{
return v_x_1373_;
}
else
{
lean_object* v_head_1375_; lean_object* v_tail_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1398_; 
v_head_1375_ = lean_ctor_get(v_x_1374_, 0);
v_tail_1376_ = lean_ctor_get(v_x_1374_, 1);
v_isSharedCheck_1398_ = !lean_is_exclusive(v_x_1374_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1378_ = v_x_1374_;
v_isShared_1379_ = v_isSharedCheck_1398_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_tail_1376_);
lean_inc(v_head_1375_);
lean_dec(v_x_1374_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1398_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v_before_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1396_; 
v_before_1380_ = lean_ctor_get(v_head_1375_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v_head_1375_);
if (v_isSharedCheck_1396_ == 0)
{
lean_object* v_unused_1397_; 
v_unused_1397_ = lean_ctor_get(v_head_1375_, 1);
lean_dec(v_unused_1397_);
v___x_1382_ = v_head_1375_;
v_isShared_1383_ = v_isSharedCheck_1396_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_before_1380_);
lean_dec(v_head_1375_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1396_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1384_; lean_object* v___x_1386_; 
v___x_1384_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__0);
if (v_isShared_1383_ == 0)
{
lean_ctor_set_tag(v___x_1382_, 7);
lean_ctor_set(v___x_1382_, 1, v___x_1384_);
lean_ctor_set(v___x_1382_, 0, v_x_1373_);
v___x_1386_ = v___x_1382_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_x_1373_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v___x_1384_);
v___x_1386_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1387_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__3);
if (v_isShared_1379_ == 0)
{
lean_ctor_set_tag(v___x_1378_, 7);
lean_ctor_set(v___x_1378_, 1, v___x_1387_);
lean_ctor_set(v___x_1378_, 0, v___x_1386_);
v___x_1389_ = v___x_1378_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1390_ = l_Lean_MessageData_ofSyntax(v_before_1380_);
v___x_1391_ = l_Lean_indentD(v___x_1390_);
v___x_1392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1389_);
lean_ctor_set(v___x_1392_, 1, v___x_1391_);
v_x_1373_ = v___x_1392_;
v_x_1374_ = v_tail_1376_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__2(void){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1402_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__1));
v___x_1403_ = l_Lean_MessageData_ofFormat(v___x_1402_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg(lean_object* v_msgData_1404_, lean_object* v_macroStack_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; uint8_t v___x_1410_; 
v___x_1408_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1406_);
v___x_1409_ = l_Lean_Elab_pp_macroStack;
v___x_1410_ = l_Lean_Option_get___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__8(v___x_1408_, v___x_1409_);
lean_dec_ref(v___x_1408_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1411_; 
lean_dec(v_macroStack_1405_);
v___x_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1411_, 0, v_msgData_1404_);
return v___x_1411_;
}
else
{
if (lean_obj_tag(v_macroStack_1405_) == 0)
{
lean_object* v___x_1412_; 
v___x_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1412_, 0, v_msgData_1404_);
return v___x_1412_;
}
else
{
lean_object* v_head_1413_; lean_object* v_after_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1429_; 
v_head_1413_ = lean_ctor_get(v_macroStack_1405_, 0);
lean_inc(v_head_1413_);
v_after_1414_ = lean_ctor_get(v_head_1413_, 1);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_head_1413_);
if (v_isSharedCheck_1429_ == 0)
{
lean_object* v_unused_1430_; 
v_unused_1430_ = lean_ctor_get(v_head_1413_, 0);
lean_dec(v_unused_1430_);
v___x_1416_ = v_head_1413_;
v_isShared_1417_ = v_isSharedCheck_1429_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_after_1414_);
lean_dec(v_head_1413_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1429_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1418_; lean_object* v___x_1420_; 
v___x_1418_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23___closed__0);
if (v_isShared_1417_ == 0)
{
lean_ctor_set_tag(v___x_1416_, 7);
lean_ctor_set(v___x_1416_, 1, v___x_1418_);
lean_ctor_set(v___x_1416_, 0, v_msgData_1404_);
v___x_1420_ = v___x_1416_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_msgData_1404_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v___x_1418_);
v___x_1420_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v_msgData_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1421_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___closed__2);
v___x_1422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1420_);
lean_ctor_set(v___x_1422_, 1, v___x_1421_);
v___x_1423_ = l_Lean_MessageData_ofSyntax(v_after_1414_);
v___x_1424_ = l_Lean_indentD(v___x_1423_);
v_msgData_1425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1425_, 0, v___x_1422_);
lean_ctor_set(v_msgData_1425_, 1, v___x_1424_);
v___x_1426_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16_spec__23(v_msgData_1425_, v_macroStack_1405_);
v___x_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
return v___x_1427_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg___boxed(lean_object* v_msgData_1431_, lean_object* v_macroStack_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg(v_msgData_1431_, v_macroStack_1432_, v___y_1433_);
lean_dec_ref(v___y_1433_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___redArg(lean_object* v_msg_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v_ref_1444_; lean_object* v_macroStack_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v_a_1448_; lean_object* v___x_1449_; lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1458_; 
v_ref_1444_ = lean_ctor_get(v___y_1441_, 2);
v_macroStack_1445_ = lean_ctor_get(v___y_1437_, 1);
v___x_1446_ = l_Lean_Elab_getBetterRef(v_ref_1444_, v_macroStack_1445_);
v___x_1447_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__15(v_msg_1436_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_a_1448_);
lean_dec_ref(v___x_1447_);
lean_inc(v_macroStack_1445_);
v___x_1449_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg(v_a_1448_, v_macroStack_1445_, v___y_1441_);
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1452_ = v___x_1449_;
v_isShared_1453_ = v_isSharedCheck_1458_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1449_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1458_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1454_; lean_object* v___x_1456_; 
v___x_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1446_);
lean_ctor_set(v___x_1454_, 1, v_a_1450_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set_tag(v___x_1452_, 1);
lean_ctor_set(v___x_1452_, 0, v___x_1454_);
v___x_1456_ = v___x_1452_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1454_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___redArg___boxed(lean_object* v_msg_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___redArg(v_msg_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
return v_res_1467_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__5(void){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1476_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__0));
v___x_1477_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__4));
v___x_1478_ = l_Lean_Expr_const___override(v___x_1477_, v___x_1476_);
return v___x_1478_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__8(void){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1483_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__0));
v___x_1484_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__7));
v___x_1485_ = l_Lean_Expr_const___override(v___x_1484_, v___x_1483_);
return v___x_1485_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__9(void){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1486_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4);
v___x_1487_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__8, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__8_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__8);
v___x_1488_ = l_Lean_Expr_app___override(v___x_1487_, v___x_1486_);
return v___x_1488_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__15(void){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__14));
v___x_1500_ = l_String_toRawSubstring_x27(v___x_1499_);
return v___x_1500_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__30(void){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_Array_mkArray0___redArg();
return v___x_1535_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__36(void){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__35));
v___x_1542_ = l_Lean_stringToMessageData(v___x_1541_);
return v___x_1542_;
}
}
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__38(void){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1544_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__37));
v___x_1545_ = l_Lean_stringToMessageData(v___x_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore(lean_object* v_e_1556_, lean_object* v_body_1557_, lean_object* v_ref_1558_, lean_object* v_expectedType_x3f_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_){
_start:
{
lean_object* v_toCold_1567_; lean_object* v_ref_1568_; lean_object* v_fileName_1569_; lean_object* v___x_1570_; 
v_toCold_1567_ = lean_ctor_get(v_a_1564_, 0);
v_ref_1568_ = lean_ctor_get(v_a_1564_, 2);
v_fileName_1569_ = lean_ctor_get(v_toCold_1567_, 0);
lean_inc_ref(v_fileName_1569_);
v___x_1570_ = lean_io_realpath(v_fileName_1569_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; uint8_t v___x_1574_; uint8_t v___y_1576_; size_t v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1675_; uint8_t v___y_1676_; lean_object* v___y_1677_; lean_object* v___y_1678_; size_t v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1743_; uint8_t v___y_1744_; lean_object* v___y_1745_; size_t v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; uint8_t v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; uint8_t v___y_1774_; lean_object* v___y_1775_; size_t v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1812_; lean_object* v___x_1875_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1571_);
lean_dec_ref_known(v___x_1570_, 1);
v___x_1572_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__0));
v___x_1573_ = lean_string_append(v_a_1571_, v___x_1572_);
v___x_1574_ = 0;
v___x_1875_ = l_Lean_Syntax_getPos_x3f(v_ref_1558_, v___x_1574_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v___x_1876_; 
v___x_1876_ = lean_unsigned_to_nat(0u);
v___y_1812_ = v___x_1876_;
goto v___jp_1811_;
}
else
{
lean_object* v_val_1877_; 
v_val_1877_ = lean_ctor_get(v___x_1875_, 0);
lean_inc(v_val_1877_);
lean_dec_ref_known(v___x_1875_, 1);
v___y_1812_ = v_val_1877_;
goto v___jp_1811_;
}
v___jp_1575_:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; uint8_t v___x_1590_; uint8_t v___x_1591_; lean_object* v___x_1592_; 
v___x_1587_ = lean_box(2);
v___x_1588_ = l_Lean_Syntax_mkStrLit(v___y_1580_, v___x_1587_);
v___x_1589_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__2));
v___x_1590_ = 0;
v___x_1591_ = 0;
v___x_1592_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__5___redArg(v___x_1589_, v___x_1590_, v___y_1578_, v___y_1579_, v___x_1591_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; lean_object* v___x_1594_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_a_1593_);
lean_dec_ref_known(v___x_1592_, 1);
v___x_1594_ = l_Lean_Elab_Term_exprToSyntax(v_a_1593_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; lean_object* v___x_1596_; lean_object* v_env_1597_; lean_object* v___x_1598_; lean_object* v_env_1599_; lean_object* v___x_1600_; lean_object* v_imports_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; size_t v_sz_1605_; lean_object* v___x_1606_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_a_1595_);
lean_dec_ref_known(v___x_1594_, 1);
v___x_1596_ = lean_st_ref_get(v___y_1586_);
v_env_1597_ = lean_ctor_get(v___x_1596_, 0);
lean_inc_ref(v_env_1597_);
lean_dec(v___x_1596_);
v___x_1598_ = lean_st_ref_get(v___y_1586_);
v_env_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc_ref(v_env_1599_);
lean_dec(v___x_1598_);
v___x_1600_ = l_Lean_Environment_header(v_env_1597_);
lean_dec_ref(v_env_1597_);
v_imports_1601_ = lean_ctor_get(v___x_1600_, 1);
lean_inc_ref(v_imports_1601_);
lean_dec_ref(v___x_1600_);
v___x_1602_ = l_Lean_Environment_mainModule(v_env_1599_);
lean_dec_ref(v_env_1599_);
v___x_1603_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
lean_ctor_set_uint8(v___x_1603_, sizeof(void*)*1, v___x_1574_);
lean_ctor_set_uint8(v___x_1603_, sizeof(void*)*1 + 1, v___y_1576_);
lean_ctor_set_uint8(v___x_1603_, sizeof(void*)*1 + 2, v___x_1574_);
v___x_1604_ = lean_array_push(v_imports_1601_, v___x_1603_);
v_sz_1605_ = lean_array_size(v___x_1604_);
v___x_1606_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg(v_sz_1605_, v___y_1577_, v___x_1604_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v_a_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_a_1607_);
lean_dec_ref_known(v___x_1606_, 1);
v___x_1608_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__5, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__5_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__5);
v___x_1609_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7_spec__10___closed__4);
v___x_1610_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__9, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__9_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__9);
v___x_1611_ = lean_array_to_list(v_a_1607_);
v___x_1612_ = l_List_foldrTR___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__7(v___x_1610_, v___x_1611_);
v___x_1613_ = l_Lean_mkAppB(v___x_1608_, v___x_1609_, v___x_1612_);
v___x_1614_ = l_Lean_Elab_Term_exprToSyntax(v___x_1613_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_toCold_1615_; lean_object* v_a_1616_; lean_object* v_ref_1617_; lean_object* v_quotContext_1618_; lean_object* v_currMacroScope_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v_toCold_1615_ = lean_ctor_get(v___y_1585_, 0);
v_a_1616_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_a_1616_);
lean_dec_ref_known(v___x_1614_, 1);
v_ref_1617_ = lean_ctor_get(v___y_1585_, 2);
v_quotContext_1618_ = lean_ctor_get(v_toCold_1615_, 8);
v_currMacroScope_1619_ = lean_ctor_get(v_toCold_1615_, 9);
v___x_1620_ = l_Lean_SourceInfo_fromRef(v_ref_1617_, v___x_1574_);
v___x_1621_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__11));
v___x_1622_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__13));
v___x_1623_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__15, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__15_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__15);
v___x_1624_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__17));
lean_inc(v_currMacroScope_1619_);
lean_inc(v_quotContext_1618_);
v___x_1625_ = l_Lean_addMacroScope(v_quotContext_1618_, v___x_1624_, v_currMacroScope_1619_);
v___x_1626_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__19));
lean_inc_n(v___x_1620_, 12);
v___x_1627_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1620_);
lean_ctor_set(v___x_1627_, 1, v___x_1623_);
lean_ctor_set(v___x_1627_, 2, v___x_1625_);
lean_ctor_set(v___x_1627_, 3, v___x_1626_);
v___x_1628_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__21));
v___x_1629_ = l_Lean_Syntax_node3(v___x_1620_, v___x_1628_, v___x_1588_, v_a_1616_, v_a_1595_);
v___x_1630_ = l_Lean_Syntax_node2(v___x_1620_, v___x_1622_, v___x_1627_, v___x_1629_);
v___x_1631_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__22));
v___x_1632_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1620_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__23));
v___x_1634_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__24));
v___x_1635_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1620_);
lean_ctor_set(v___x_1635_, 1, v___x_1633_);
v___x_1636_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__26));
v___x_1637_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__28));
v___x_1638_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__29));
v___x_1639_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1620_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
v___x_1640_ = l_Lean_Syntax_node1(v___x_1620_, v___x_1637_, v___x_1639_);
v___x_1641_ = l_Lean_Syntax_node1(v___x_1620_, v___x_1628_, v___x_1640_);
v___x_1642_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__30, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__30_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__30);
v___x_1643_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1620_);
lean_ctor_set(v___x_1643_, 1, v___x_1628_);
lean_ctor_set(v___x_1643_, 2, v___x_1642_);
v___x_1644_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__31));
v___x_1645_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1620_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
v___x_1646_ = l_Lean_Syntax_node4(v___x_1620_, v___x_1636_, v___x_1641_, v___x_1643_, v___x_1645_, v_body_1557_);
v___x_1647_ = l_Lean_Syntax_node2(v___x_1620_, v___x_1634_, v___x_1635_, v___x_1646_);
v___x_1648_ = l_Lean_Syntax_node3(v___x_1620_, v___x_1621_, v___x_1630_, v___x_1632_, v___x_1647_);
v___x_1649_ = l_Lean_Elab_Term_elabTerm(v___x_1648_, v_expectedType_x3f_1559_, v___y_1576_, v___y_1576_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_);
return v___x_1649_;
}
else
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
lean_dec(v_a_1595_);
lean_dec(v___x_1588_);
lean_dec(v_expectedType_x3f_1559_);
lean_dec(v_body_1557_);
v_a_1650_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1614_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1614_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
else
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
lean_dec(v_a_1595_);
lean_dec(v___x_1588_);
lean_dec(v_expectedType_x3f_1559_);
lean_dec(v_body_1557_);
v_a_1658_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1606_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1606_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
else
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
lean_dec(v___x_1588_);
lean_dec(v_expectedType_x3f_1559_);
lean_dec(v_body_1557_);
v_a_1666_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v___x_1594_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1594_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
if (v_isShared_1669_ == 0)
{
v___x_1671_ = v___x_1668_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1666_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
else
{
lean_dec(v___x_1588_);
lean_dec(v_expectedType_x3f_1559_);
lean_dec(v_body_1557_);
return v___x_1592_;
}
}
v___jp_1674_:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; uint8_t v___x_1691_; 
v___x_1689_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1687_);
v___x_1690_ = l_Lean_Elab_inServer;
v___x_1691_ = l_Lean_Option_get___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__8(v___x_1689_, v___x_1690_);
lean_dec_ref(v___x_1689_);
if (v___x_1691_ == 0)
{
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1675_);
lean_dec(v_ref_1558_);
v___y_1576_ = v___y_1676_;
v___y_1577_ = v___y_1679_;
v___y_1578_ = v___y_1678_;
v___y_1579_ = v___y_1682_;
v___y_1580_ = v___y_1681_;
v___y_1581_ = v___y_1683_;
v___y_1582_ = v___y_1684_;
v___y_1583_ = v___y_1685_;
v___y_1584_ = v___y_1686_;
v___y_1585_ = v___y_1687_;
v___y_1586_ = v___y_1688_;
goto v___jp_1575_;
}
else
{
uint8_t v___x_1692_; 
v___x_1692_ = l_Lean_Expr_hasSorry(v___y_1680_);
if (v___x_1692_ == 0)
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___f_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1693_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__32));
lean_inc_ref(v___y_1678_);
v___x_1694_ = l_Lean_Idbg_exprToJson(v___y_1678_);
v___x_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1693_);
lean_ctor_set(v___x_1695_, 1, v___x_1694_);
v___x_1696_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__33));
v___x_1697_ = l_Lean_Idbg_exprToJson(v___y_1680_);
v___x_1698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1696_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
v___x_1699_ = lean_box(0);
v___x_1700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1698_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
v___x_1701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1695_);
lean_ctor_set(v___x_1701_, 1, v___x_1700_);
v___x_1702_ = l_Lean_Json_mkObj(v___x_1701_);
lean_dec_ref_known(v___x_1701_, 2);
lean_inc(v_ref_1558_);
v___f_1703_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__0___boxed), 7, 3);
lean_closure_set(v___f_1703_, 0, v___y_1675_);
lean_closure_set(v___f_1703_, 1, v___x_1702_);
lean_closure_set(v___f_1703_, 2, v_ref_1558_);
v___x_1704_ = l_IO_CancelToken_new();
v___x_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1704_);
v___x_1706_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__0));
v___x_1707_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__8));
v___x_1708_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__11));
lean_inc(v___y_1677_);
v___x_1709_ = l_Lean_Name_num___override(v___x_1708_, v___y_1677_);
v___x_1710_ = l_Lean_Name_str___override(v___x_1709_, v___x_1706_);
v___x_1711_ = l_Lean_Name_str___override(v___x_1710_, v___x_1707_);
v___x_1712_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__15));
v___x_1713_ = l_Lean_Name_str___override(v___x_1711_, v___x_1712_);
v___x_1714_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__34));
v___x_1715_ = l_Lean_Name_str___override(v___x_1713_, v___x_1714_);
v___x_1716_ = l_Lean_Name_toString(v___x_1715_, v___y_1676_);
lean_inc_ref(v___x_1705_);
v___x_1717_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___f_1703_, v___x_1705_, v___x_1716_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_a_1718_);
lean_dec_ref_known(v___x_1717_, 1);
v___x_1719_ = lean_box(0);
v___x_1720_ = lean_apply_1(v_a_1718_, v___x_1719_);
v___x_1721_ = lean_io_as_task(v___x_1720_, v___y_1677_);
v___x_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1722_, 0, v_ref_1558_);
v___x_1723_ = l_Lean_Language_SnapshotTask_defaultReportingRange(v___x_1722_);
v___x_1724_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1722_);
lean_ctor_set(v___x_1724_, 1, v___x_1723_);
lean_ctor_set(v___x_1724_, 2, v___x_1705_);
lean_ctor_set(v___x_1724_, 3, v___x_1721_);
v___x_1725_ = l_Lean_Core_logSnapshotTask___redArg(v___x_1724_, v___y_1688_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_dec_ref_known(v___x_1725_, 1);
v___y_1576_ = v___y_1676_;
v___y_1577_ = v___y_1679_;
v___y_1578_ = v___y_1678_;
v___y_1579_ = v___y_1682_;
v___y_1580_ = v___y_1681_;
v___y_1581_ = v___y_1683_;
v___y_1582_ = v___y_1684_;
v___y_1583_ = v___y_1685_;
v___y_1584_ = v___y_1686_;
v___y_1585_ = v___y_1687_;
v___y_1586_ = v___y_1688_;
goto v___jp_1575_;
}
else
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
lean_dec_ref(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec_ref(v___y_1678_);
lean_dec(v_expectedType_x3f_1559_);
lean_dec(v_body_1557_);
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___x_1725_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1725_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
else
{
lean_object* v_a_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1741_; 
lean_dec_ref_known(v___x_1705_, 1);
lean_dec_ref(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1677_);
lean_dec(v_expectedType_x3f_1559_);
lean_dec(v_ref_1558_);
lean_dec(v_body_1557_);
v_a_1734_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1736_ = v___x_1717_;
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_dec(v___x_1717_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1739_; 
if (v_isShared_1737_ == 0)
{
v___x_1739_ = v___x_1736_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_a_1734_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
}
else
{
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1675_);
lean_dec(v_ref_1558_);
v___y_1576_ = v___y_1676_;
v___y_1577_ = v___y_1679_;
v___y_1578_ = v___y_1678_;
v___y_1579_ = v___y_1682_;
v___y_1580_ = v___y_1681_;
v___y_1581_ = v___y_1683_;
v___y_1582_ = v___y_1684_;
v___y_1583_ = v___y_1685_;
v___y_1584_ = v___y_1686_;
v___y_1585_ = v___y_1687_;
v___y_1586_ = v___y_1688_;
goto v___jp_1575_;
}
}
}
v___jp_1742_:
{
uint8_t v___x_1757_; 
v___x_1757_ = l_Lean_Expr_hasMVar(v___y_1747_);
if (v___x_1757_ == 0)
{
v___y_1675_ = v___y_1743_;
v___y_1676_ = v___y_1744_;
v___y_1677_ = v___y_1745_;
v___y_1678_ = v___y_1747_;
v___y_1679_ = v___y_1746_;
v___y_1680_ = v___y_1750_;
v___y_1681_ = v___y_1749_;
v___y_1682_ = v___y_1748_;
v___y_1683_ = v___y_1751_;
v___y_1684_ = v___y_1752_;
v___y_1685_ = v___y_1753_;
v___y_1686_ = v___y_1754_;
v___y_1687_ = v___y_1755_;
v___y_1688_ = v___y_1756_;
goto v___jp_1674_;
}
else
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1767_; 
lean_dec_ref(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1743_);
lean_dec(v_expectedType_x3f_1559_);
lean_dec(v_ref_1558_);
lean_dec(v_body_1557_);
v___x_1758_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__36, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__36_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__36);
v___x_1759_ = l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___redArg(v___x_1758_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1762_ = v___x_1759_;
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1759_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1765_; 
if (v_isShared_1763_ == 0)
{
v___x_1765_ = v___x_1762_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1760_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
}
v___jp_1768_:
{
uint8_t v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___f_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___f_1787_; lean_object* v___x_1788_; 
v___x_1779_ = 1;
v___x_1780_ = lean_box(v___x_1574_);
v___x_1781_ = lean_box(v___y_1769_);
v___x_1782_ = lean_box(v___x_1779_);
lean_inc_ref(v___y_1771_);
v___f_1783_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__1___boxed), 13, 5);
lean_closure_set(v___f_1783_, 0, v___y_1771_);
lean_closure_set(v___f_1783_, 1, v___y_1772_);
lean_closure_set(v___f_1783_, 2, v___x_1780_);
lean_closure_set(v___f_1783_, 3, v___x_1781_);
lean_closure_set(v___f_1783_, 4, v___x_1782_);
v___x_1784_ = lean_box(v___x_1574_);
v___x_1785_ = lean_box(v___y_1769_);
v___x_1786_ = lean_box(v___x_1779_);
v___f_1787_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___lam__2___boxed), 12, 5);
lean_closure_set(v___f_1787_, 0, v___y_1771_);
lean_closure_set(v___f_1787_, 1, v___y_1770_);
lean_closure_set(v___f_1787_, 2, v___x_1784_);
lean_closure_set(v___f_1787_, 3, v___x_1785_);
lean_closure_set(v___f_1787_, 4, v___x_1786_);
v___x_1788_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__4___redArg(v___y_1778_, v___f_1787_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v_fst_1790_; lean_object* v_snd_1791_; uint8_t v___x_1792_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1789_);
lean_dec_ref_known(v___x_1788_, 1);
v_fst_1790_ = lean_ctor_get(v_a_1789_, 0);
lean_inc(v_fst_1790_);
v_snd_1791_ = lean_ctor_get(v_a_1789_, 1);
lean_inc(v_snd_1791_);
lean_dec(v_a_1789_);
v___x_1792_ = l_Lean_Expr_hasMVar(v_fst_1790_);
if (v___x_1792_ == 0)
{
v___y_1743_ = v___y_1773_;
v___y_1744_ = v___y_1774_;
v___y_1745_ = v___y_1775_;
v___y_1746_ = v___y_1776_;
v___y_1747_ = v_snd_1791_;
v___y_1748_ = v___f_1783_;
v___y_1749_ = v___y_1777_;
v___y_1750_ = v_fst_1790_;
v___y_1751_ = v_a_1560_;
v___y_1752_ = v_a_1561_;
v___y_1753_ = v_a_1562_;
v___y_1754_ = v_a_1563_;
v___y_1755_ = v_a_1564_;
v___y_1756_ = v_a_1565_;
goto v___jp_1742_;
}
else
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
lean_dec(v_snd_1791_);
lean_dec(v_fst_1790_);
lean_dec_ref(v___f_1783_);
lean_dec_ref(v___y_1777_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1773_);
lean_dec(v_expectedType_x3f_1559_);
lean_dec(v_ref_1558_);
lean_dec(v_body_1557_);
v___x_1793_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__38, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__38_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__38);
v___x_1794_ = l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___redArg(v___x_1793_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_);
v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v___x_1794_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1794_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
}
else
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1810_; 
lean_dec_ref(v___f_1783_);
lean_dec_ref(v___y_1777_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1773_);
lean_dec(v_expectedType_x3f_1559_);
lean_dec(v_ref_1558_);
lean_dec(v_body_1557_);
v_a_1803_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1805_ = v___x_1788_;
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1788_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1806_ == 0)
{
v___x_1808_ = v___x_1805_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_a_1803_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
v___jp_1811_:
{
lean_object* v_lctx_1813_; lean_object* v_decls_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; uint64_t v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v_lctx_1813_ = lean_ctor_get(v_a_1562_, 2);
v_decls_1814_ = lean_ctor_get(v_lctx_1813_, 1);
v___x_1815_ = l_Nat_reprFast(v___y_1812_);
v___x_1816_ = lean_string_append(v___x_1573_, v___x_1815_);
lean_dec_ref(v___x_1815_);
v___x_1817_ = lean_string_hash(v___x_1816_);
lean_dec_ref(v___x_1816_);
v___x_1818_ = lean_uint64_to_nat(v___x_1817_);
v___x_1819_ = l_Nat_reprFast(v___x_1818_);
v___x_1820_ = lean_unsigned_to_nat(0u);
v___x_1821_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__39));
v___x_1822_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0(v_decls_1814_, v___x_1821_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; size_t v_sz_1824_; size_t v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; uint8_t v___x_1828_; lean_object* v___x_1829_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc_n(v_a_1823_, 2);
lean_dec_ref_known(v___x_1822_, 1);
v_sz_1824_ = lean_array_size(v_a_1823_);
v___x_1825_ = ((size_t)0ULL);
v___x_1826_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__1(v_sz_1824_, v___x_1825_, v_a_1823_);
v___x_1827_ = lean_box(0);
v___x_1828_ = 1;
v___x_1829_ = l_Lean_Elab_Term_elabTerm(v_e_1556_, v___x_1827_, v___x_1828_, v___x_1828_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1830_; lean_object* v___x_1831_; 
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_a_1830_);
lean_dec_ref_known(v___x_1829_, 1);
v___x_1831_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_1574_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v___x_1832_; lean_object* v_a_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
lean_dec_ref_known(v___x_1831_, 1);
v___x_1832_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg(v_a_1830_, v_a_1563_);
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
lean_inc(v_a_1833_);
lean_dec_ref(v___x_1832_);
v___x_1834_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__41));
v___x_1835_ = lean_unsigned_to_nat(1u);
v___x_1836_ = lean_mk_empty_array_with_capacity(v___x_1835_);
lean_inc_ref(v___x_1836_);
v___x_1837_ = lean_array_push(v___x_1836_, v_a_1833_);
v___x_1838_ = l_Lean_Meta_mkAppM(v___x_1834_, v___x_1837_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v_a_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
lean_inc(v_a_1839_);
lean_dec_ref_known(v___x_1838_, 1);
v___x_1840_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___closed__44));
lean_inc_ref(v___x_1836_);
v___x_1841_ = lean_array_push(v___x_1836_, v_a_1839_);
v___x_1842_ = l_Lean_Meta_mkAppM(v___x_1840_, v___x_1841_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_a_1843_; lean_object* v___x_1844_; 
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
lean_inc(v_a_1843_);
lean_dec_ref_known(v___x_1842_, 1);
v___x_1844_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_1574_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v___x_1845_; lean_object* v_a_1846_; lean_object* v___x_1847_; uint8_t v___x_1848_; 
lean_dec_ref_known(v___x_1844_, 1);
v___x_1845_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__3___redArg(v_a_1843_, v_a_1563_);
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_a_1846_);
lean_dec_ref(v___x_1845_);
v___x_1847_ = lean_array_get_size(v_a_1823_);
v___x_1848_ = lean_nat_dec_lt(v___x_1820_, v___x_1847_);
if (v___x_1848_ == 0)
{
lean_dec(v_a_1823_);
lean_inc_ref(v_lctx_1813_);
lean_inc_ref(v___x_1819_);
v___y_1769_ = v___x_1828_;
v___y_1770_ = v_a_1846_;
v___y_1771_ = v___x_1826_;
v___y_1772_ = v___x_1836_;
v___y_1773_ = v___x_1819_;
v___y_1774_ = v___x_1828_;
v___y_1775_ = v___x_1820_;
v___y_1776_ = v___x_1825_;
v___y_1777_ = v___x_1819_;
v___y_1778_ = v_lctx_1813_;
goto v___jp_1768_;
}
else
{
size_t v___x_1849_; lean_object* v___x_1850_; 
v___x_1849_ = lean_usize_of_nat(v___x_1847_);
lean_inc_ref(v_lctx_1813_);
v___x_1850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__11(v_a_1823_, v___x_1825_, v___x_1849_, v_lctx_1813_);
lean_dec(v_a_1823_);
lean_inc_ref(v___x_1819_);
v___y_1769_ = v___x_1828_;
v___y_1770_ = v_a_1846_;
v___y_1771_ = v___x_1826_;
v___y_1772_ = v___x_1836_;
v___y_1773_ = v___x_1819_;
v___y_1774_ = v___x_1828_;
v___y_1775_ = v___x_1820_;
v___y_1776_ = v___x_1825_;
v___y_1777_ = v___x_1819_;
v___y_1778_ = v___x_1850_;
goto v___jp_1768_;
}
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
lean_dec(v_a_1843_);
lean_dec_ref(v___x_1836_);
lean_dec_ref(v___x_1826_);
lean_dec(v_a_1823_);
lean_dec_ref(v___x_1819_);
lean_dec(v_expectedType_x3f_1559_);
lean_dec(v_ref_1558_);
lean_dec(v_body_1557_);
v_a_1851_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1844_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1844_);
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
lean_dec_ref(v___x_1836_);
lean_dec_ref(v___x_1826_);
lean_dec(v_a_1823_);
lean_dec_ref(v___x_1819_);
lean_dec(v_expectedType_x3f_1559_);
lean_dec(v_ref_1558_);
lean_dec(v_body_1557_);
return v___x_1842_;
}
}
else
{
lean_dec_ref(v___x_1836_);
lean_dec_ref(v___x_1826_);
lean_dec(v_a_1823_);
lean_dec_ref(v___x_1819_);
lean_dec(v_expectedType_x3f_1559_);
lean_dec(v_ref_1558_);
lean_dec(v_body_1557_);
return v___x_1838_;
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
lean_dec(v_a_1830_);
lean_dec_ref(v___x_1826_);
lean_dec(v_a_1823_);
lean_dec_ref(v___x_1819_);
lean_dec(v_expectedType_x3f_1559_);
lean_dec(v_ref_1558_);
lean_dec(v_body_1557_);
v_a_1859_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1831_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1831_);
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
else
{
lean_dec_ref(v___x_1826_);
lean_dec(v_a_1823_);
lean_dec_ref(v___x_1819_);
lean_dec(v_expectedType_x3f_1559_);
lean_dec(v_ref_1558_);
lean_dec(v_body_1557_);
return v___x_1829_;
}
}
else
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
lean_dec_ref(v___x_1819_);
lean_dec(v_expectedType_x3f_1559_);
lean_dec(v_ref_1558_);
lean_dec(v_body_1557_);
lean_dec(v_e_1556_);
v_a_1867_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1822_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1822_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1867_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
}
else
{
lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1889_; 
lean_dec(v_expectedType_x3f_1559_);
lean_dec(v_ref_1558_);
lean_dec(v_body_1557_);
lean_dec(v_e_1556_);
v_a_1878_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1880_ = v___x_1570_;
v_isShared_1881_ = v_isSharedCheck_1889_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1570_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1889_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1887_; 
v___x_1882_ = lean_io_error_to_string(v_a_1878_);
v___x_1883_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
v___x_1884_ = l_Lean_MessageData_ofFormat(v___x_1883_);
lean_inc(v_ref_1568_);
v___x_1885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1885_, 0, v_ref_1568_);
lean_ctor_set(v___x_1885_, 1, v___x_1884_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v___x_1885_);
v___x_1887_ = v___x_1880_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1885_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore___boxed(lean_object* v_e_1890_, lean_object* v_body_1891_, lean_object* v_ref_1892_, lean_object* v_expectedType_x3f_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore(v_e_1890_, v_body_1891_, v_ref_1892_, v_expectedType_x3f_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
lean_dec(v_a_1895_);
lean_dec_ref(v_a_1894_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2(lean_object* v_00_u03b2_1902_, lean_object* v_x_1903_, lean_object* v_x_1904_, lean_object* v_x_1905_){
_start:
{
lean_object* v___x_1906_; 
v___x_1906_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2___redArg(v_x_1903_, v_x_1904_, v_x_1905_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6(size_t v_sz_1907_, size_t v_i_1908_, lean_object* v_bs_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___redArg(v_sz_1907_, v_i_1908_, v_bs_1909_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6___boxed(lean_object* v_sz_1918_, lean_object* v_i_1919_, lean_object* v_bs_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
size_t v_sz_boxed_1928_; size_t v_i_boxed_1929_; lean_object* v_res_1930_; 
v_sz_boxed_1928_ = lean_unbox_usize(v_sz_1918_);
lean_dec(v_sz_1918_);
v_i_boxed_1929_ = lean_unbox_usize(v_i_1919_);
lean_dec(v_i_1919_);
v_res_1930_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__6(v_sz_boxed_1928_, v_i_boxed_1929_, v_bs_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10(lean_object* v_00_u03b1_1931_, lean_object* v_msg_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v___x_1940_; 
v___x_1940_ = l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___redArg(v_msg_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10___boxed(lean_object* v_00_u03b1_1941_, lean_object* v_msg_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l_Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10(v_00_u03b1_1941_, v_msg_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4(lean_object* v_00_u03b2_1951_, lean_object* v_x_1952_, size_t v_x_1953_, size_t v_x_1954_, lean_object* v_x_1955_, lean_object* v_x_1956_){
_start:
{
lean_object* v___x_1957_; 
v___x_1957_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___redArg(v_x_1952_, v_x_1953_, v_x_1954_, v_x_1955_, v_x_1956_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1958_, lean_object* v_x_1959_, lean_object* v_x_1960_, lean_object* v_x_1961_, lean_object* v_x_1962_, lean_object* v_x_1963_){
_start:
{
size_t v_x_36737__boxed_1964_; size_t v_x_36738__boxed_1965_; lean_object* v_res_1966_; 
v_x_36737__boxed_1964_ = lean_unbox_usize(v_x_1960_);
lean_dec(v_x_1960_);
v_x_36738__boxed_1965_ = lean_unbox_usize(v_x_1961_);
lean_dec(v_x_1961_);
v_res_1966_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4(v_00_u03b2_1958_, v_x_1959_, v_x_36737__boxed_1964_, v_x_36738__boxed_1965_, v_x_1962_, v_x_1963_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16(lean_object* v_msgData_1967_, lean_object* v_macroStack_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v___x_1976_; 
v___x_1976_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___redArg(v_msgData_1967_, v_macroStack_1968_, v___y_1973_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16___boxed(lean_object* v_msgData_1977_, lean_object* v_macroStack_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__10_spec__16(v_msgData_1977_, v_macroStack_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8(lean_object* v_as_1987_, size_t v_sz_1988_, size_t v_i_1989_, lean_object* v_b_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8___redArg(v_as_1987_, v_sz_1988_, v_i_1989_, v_b_1990_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8___boxed(lean_object* v_as_1999_, lean_object* v_sz_2000_, lean_object* v_i_2001_, lean_object* v_b_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_){
_start:
{
size_t v_sz_boxed_2010_; size_t v_i_boxed_2011_; lean_object* v_res_2012_; 
v_sz_boxed_2010_ = lean_unbox_usize(v_sz_2000_);
lean_dec(v_sz_2000_);
v_i_boxed_2011_ = lean_unbox_usize(v_i_2001_);
lean_dec(v_i_2001_);
v_res_2012_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__1_spec__8(v_as_1999_, v_sz_boxed_2010_, v_i_boxed_2011_, v_b_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec_ref(v_as_1999_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12(lean_object* v_00_u03b2_2013_, lean_object* v_n_2014_, lean_object* v_k_2015_, lean_object* v_v_2016_){
_start:
{
lean_object* v___x_2017_; 
v___x_2017_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12___redArg(v_n_2014_, v_k_2015_, v_v_2016_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13(lean_object* v_00_u03b2_2018_, size_t v_depth_2019_, lean_object* v_keys_2020_, lean_object* v_vals_2021_, lean_object* v_heq_2022_, lean_object* v_i_2023_, lean_object* v_entries_2024_){
_start:
{
lean_object* v___x_2025_; 
v___x_2025_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13___redArg(v_depth_2019_, v_keys_2020_, v_vals_2021_, v_i_2023_, v_entries_2024_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13___boxed(lean_object* v_00_u03b2_2026_, lean_object* v_depth_2027_, lean_object* v_keys_2028_, lean_object* v_vals_2029_, lean_object* v_heq_2030_, lean_object* v_i_2031_, lean_object* v_entries_2032_){
_start:
{
size_t v_depth_boxed_2033_; lean_object* v_res_2034_; 
v_depth_boxed_2033_ = lean_unbox_usize(v_depth_2027_);
lean_dec(v_depth_2027_);
v_res_2034_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__13(v_00_u03b2_2026_, v_depth_boxed_2033_, v_keys_2028_, v_vals_2029_, v_heq_2030_, v_i_2031_, v_entries_2032_);
lean_dec_ref(v_vals_2029_);
lean_dec_ref(v_keys_2028_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15(lean_object* v_as_2035_, size_t v_sz_2036_, size_t v_i_2037_, lean_object* v_b_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v___x_2046_; 
v___x_2046_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15___redArg(v_as_2035_, v_sz_2036_, v_i_2037_, v_b_2038_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15___boxed(lean_object* v_as_2047_, lean_object* v_sz_2048_, lean_object* v_i_2049_, lean_object* v_b_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_){
_start:
{
size_t v_sz_boxed_2058_; size_t v_i_boxed_2059_; lean_object* v_res_2060_; 
v_sz_boxed_2058_ = lean_unbox_usize(v_sz_2048_);
lean_dec(v_sz_2048_);
v_i_boxed_2059_ = lean_unbox_usize(v_i_2049_);
lean_dec(v_i_2049_);
v_res_2060_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__0_spec__0_spec__6_spec__15(v_as_2047_, v_sz_boxed_2058_, v_i_boxed_2059_, v_b_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec(v___y_2054_);
lean_dec_ref(v___y_2053_);
lean_dec(v___y_2052_);
lean_dec_ref(v___y_2051_);
lean_dec_ref(v_as_2047_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12_spec__20(lean_object* v_00_u03b2_2061_, lean_object* v_x_2062_, lean_object* v_x_2063_, lean_object* v_x_2064_, lean_object* v_x_2065_){
_start:
{
lean_object* v___x_2066_; 
v___x_2066_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore_spec__2_spec__4_spec__12_spec__20___redArg(v_x_2062_, v_x_2063_, v_x_2064_, v_x_2065_);
return v___x_2066_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2067_ = lean_box(0);
v___x_2068_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_2069_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
lean_ctor_set(v___x_2069_, 1, v___x_2067_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg(){
_start:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2071_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___closed__0);
v___x_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2071_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___boxed(lean_object* v___y_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg();
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0(lean_object* v_00_u03b1_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
lean_object* v___x_2083_; 
v___x_2083_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg();
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___boxed(lean_object* v_00_u03b1_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0(v_00_u03b1_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm(lean_object* v_stx_2099_, lean_object* v_expectedType_x3f_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_){
_start:
{
lean_object* v___x_2108_; uint8_t v___x_2109_; 
v___x_2108_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__1));
lean_inc(v_stx_2099_);
v___x_2109_ = l_Lean_Syntax_isOfKind(v_stx_2099_, v___x_2108_);
if (v___x_2109_ == 0)
{
lean_object* v___x_2110_; 
lean_dec(v_expectedType_x3f_2100_);
lean_dec(v_stx_2099_);
v___x_2110_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg();
return v___x_2110_;
}
else
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v_body_2114_; lean_object* v___x_2115_; 
v___x_2111_ = lean_unsigned_to_nat(1u);
v___x_2112_ = l_Lean_Syntax_getArg(v_stx_2099_, v___x_2111_);
v___x_2113_ = lean_unsigned_to_nat(3u);
v_body_2114_ = l_Lean_Syntax_getArg(v_stx_2099_, v___x_2113_);
v___x_2115_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore(v___x_2112_, v_body_2114_, v_stx_2099_, v_expectedType_x3f_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
return v___x_2115_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___boxed(lean_object* v_stx_2116_, lean_object* v_expectedType_x3f_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm(v_stx_2116_, v_expectedType_x3f_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_);
lean_dec(v_a_2123_);
lean_dec_ref(v_a_2122_);
lean_dec(v_a_2121_);
lean_dec_ref(v_a_2120_);
lean_dec(v_a_2119_);
lean_dec_ref(v_a_2118_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1(){
_start:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2131_ = l_Lean_Elab_Term_termElabAttribute;
v___x_2132_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___closed__1));
v___x_2133_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1___closed__1));
v___x_2134_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___boxed), 9, 0);
v___x_2135_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2131_, v___x_2132_, v___x_2133_, v___x_2134_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1___boxed(lean_object* v_a_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1();
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0___redArg(){
_start:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2139_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm_spec__0___redArg___closed__0);
v___x_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2139_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0___redArg___boxed(lean_object* v___y_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0___redArg();
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0(lean_object* v_00_u03b1_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v___x_2152_; 
v___x_2152_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0___redArg();
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0___boxed(lean_object* v_00_u03b1_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0(v_00_u03b1_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec_ref(v___y_2154_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___lam__0(lean_object* v_a_2163_, lean_object* v___x_2164_, lean_object* v_stx_2165_, lean_object* v_body_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2175_, 0, v_a_2163_);
v___x_2176_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgCore(v___x_2164_, v_body_2166_, v_stx_2165_, v___x_2175_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___lam__0___boxed(lean_object* v_a_2177_, lean_object* v___x_2178_, lean_object* v_stx_2179_, lean_object* v_body_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___lam__0(v_a_2177_, v___x_2178_, v_stx_2179_, v_body_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
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
static lean_object* _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__2(void){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2193_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__1));
v___x_2194_ = l_Lean_MessageData_ofFormat(v___x_2193_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg(lean_object* v_stx_2195_, lean_object* v_dec_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_){
_start:
{
lean_object* v___x_2205_; uint8_t v___x_2206_; 
v___x_2205_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__4));
lean_inc(v_stx_2195_);
v___x_2206_ = l_Lean_Syntax_isOfKind(v_stx_2195_, v___x_2205_);
if (v___x_2206_ == 0)
{
lean_object* v___x_2207_; 
lean_dec_ref(v_dec_2196_);
lean_dec(v_stx_2195_);
v___x_2207_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg_spec__0___redArg();
return v___x_2207_;
}
else
{
lean_object* v_doBlockResultType_2208_; lean_object* v___x_2209_; lean_object* v_tk_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v_doBlockResultType_2208_ = lean_ctor_get(v_a_2197_, 3);
v___x_2209_ = lean_unsigned_to_nat(0u);
v_tk_2210_ = l_Lean_Syntax_getArg(v_stx_2195_, v___x_2209_);
v___x_2211_ = lean_unsigned_to_nat(1u);
v___x_2212_ = l_Lean_Syntax_getArg(v_stx_2195_, v___x_2211_);
lean_inc_ref(v_doBlockResultType_2208_);
v___x_2213_ = l_Lean_Elab_Do_mkMonadApp(v_doBlockResultType_2208_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_);
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v_a_2214_; lean_object* v___f_2215_; lean_object* v___x_2216_; 
v_a_2214_ = lean_ctor_get(v___x_2213_, 0);
lean_inc(v_a_2214_);
lean_dec_ref_known(v___x_2213_, 1);
v___f_2215_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___lam__0___boxed), 12, 3);
lean_closure_set(v___f_2215_, 0, v_a_2214_);
lean_closure_set(v___f_2215_, 1, v___x_2212_);
lean_closure_set(v___f_2215_, 2, v_stx_2195_);
v___x_2216_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(v_dec_2196_, v_tk_2210_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_);
lean_dec(v_tk_2210_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v_a_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_a_2217_);
lean_dec_ref_known(v___x_2216_, 1);
v___x_2218_ = lean_obj_once(&l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__2, &l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__2_once, _init_l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___closed__2);
v___x_2219_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_DoElemCont_continueWithUnit___boxed), 9, 1);
lean_closure_set(v___x_2219_, 0, v_a_2217_);
v___x_2220_ = lean_box(0);
v___x_2221_ = l_Lean_Elab_Do_doElabToSyntax___redArg(v___x_2218_, v___x_2219_, v___f_2215_, v___x_2220_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_);
return v___x_2221_;
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
lean_dec_ref(v___f_2215_);
v_a_2222_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2216_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2216_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2225_ == 0)
{
v___x_2227_ = v___x_2224_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2222_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
else
{
lean_dec(v___x_2212_);
lean_dec(v_tk_2210_);
lean_dec_ref(v_dec_2196_);
lean_dec(v_stx_2195_);
return v___x_2213_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___boxed(lean_object* v_stx_2230_, lean_object* v_dec_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg(v_stx_2230_, v_dec_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_);
lean_dec(v_a_2238_);
lean_dec_ref(v_a_2237_);
lean_dec(v_a_2236_);
lean_dec_ref(v_a_2235_);
lean_dec(v_a_2234_);
lean_dec_ref(v_a_2233_);
lean_dec_ref(v_a_2232_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1(){
_start:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2246_ = l_Lean_Elab_Do_doElemElabAttribute;
v___x_2247_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1___closed__4));
v___x_2248_ = ((lean_object*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1___closed__1));
v___x_2249_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___boxed), 10, 0);
v___x_2250_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_2246_, v___x_2247_, v___x_2248_, v___x_2249_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1___boxed(lean_object* v_a_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1();
return v_res_2252_;
}
}
lean_object* runtime_initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Idbg(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Idbg(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Idbg(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_controlInfoIdbg__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabIdbgTerm__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg___regBuiltin___private_Lean_Elab_Idbg_0__Lean_Elab_Do_elabDoIdbg__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Do(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Idbg(uint8_t builtin) {
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
lean_object* initialize_Lean_Idbg(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Idbg(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Idbg(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Idbg(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Idbg(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Idbg(builtin);
}
#ifdef __cplusplus
}
#endif
