// Lean compiler output
// Module: Lean.Linter.MissingDocs
// Imports: public import Lean.Parser.Syntax public import Lean.Meta.Tactic.Simp.RegisterCommand public import Lean.Elab.Command public import Lean.Linter.Util
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
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isAtom(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_Linter_linterMessageTag;
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t l_Lean_DataValue_sameCtor(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Int_repr(lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_sub(size_t, size_t);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Syntax_setArgs(lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecl(lean_object*);
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Elab_Command_withScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t l_String_instHashableRaw_hash(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_foldInfo___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_Syntax_getAtomVal(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addLinter(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "missingDocs"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(157, 241, 189, 233, 41, 176, 169, 7)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "enable the 'missing documentation' linter"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 243, 121, 207, 53, 172, 203, 87)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(94, 221, 43, 155, 63, 47, 239, 133)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_linter_missingDocs;
LEAN_EXPORT uint8_t l_Lean_Linter_getLinterMissingDocs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterMissingDocs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_SimpleHandler_toHandler(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Linter_MissingDocs_mkHandlerUnsafe_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Linter_MissingDocs_mkHandlerUnsafe_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Linter_MissingDocs_mkHandlerUnsafe_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Linter_MissingDocs_mkHandlerUnsafe_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "unexpected missing docs handler at '"};
static const lean_object* l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__0 = (const lean_object*)&l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__0_value;
static const lean_string_object l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "', `MissingDocs.Handler` or `MissingDocs.SimpleHandler` expected"};
static const lean_object* l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__1 = (const lean_object*)&l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__1_value;
static const lean_string_object l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__2 = (const lean_object*)&l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__2_value;
static const lean_string_object l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__3 = (const lean_object*)&l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__3_value;
static const lean_string_object l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "MissingDocs"};
static const lean_object* l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__4 = (const lean_object*)&l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__4_value;
static const lean_string_object l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "SimpleHandler"};
static const lean_object* l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__5 = (const lean_object*)&l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__5_value;
static const lean_string_object l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Handler"};
static const lean_object* l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__6 = (const lean_object*)&l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_mkHandlerUnsafe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_mkHandlerUnsafe___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_537855421____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_537855421____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_builtinHandlersRef;
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_(lean_object*);
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__0_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "number of local entries: "};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__0_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__0_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__1_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__0_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__1_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__1_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__3_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__4_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__4_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__5_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__5_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__0_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__0_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__0_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__1_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__1_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__1_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__2_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__2_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__2_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__3_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__3_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__3_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__3_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__4_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "missingDocsExt"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__4_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__4_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(25, 85, 84, 40, 188, 20, 254, 124)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__4_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 124, 238, 121, 86, 135, 253, 57)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__6_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__6_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__7_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__7_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__8_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__8_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__9_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__9_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_missingDocsExt;
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_addHandler___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_addHandler(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Linter_MissingDocs_getHandlers___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Linter_MissingDocs_getHandlers___closed__0 = (const lean_object*)&l_Lean_Linter_MissingDocs_getHandlers___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_getHandlers(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_MissingDocs_missingDocs_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_MissingDocs_missingDocs_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_MissingDocs_missingDocs_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_MissingDocs_missingDocs_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_missingDocs___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_missingDocs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_MissingDocs_missingDocs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_MissingDocs_missingDocs___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_MissingDocs_missingDocs___closed__0 = (const lean_object*)&l_Lean_Linter_MissingDocs_missingDocs___closed__0_value;
static const lean_ctor_object l_Lean_Linter_MissingDocs_missingDocs___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_missingDocs___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_missingDocs___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_missingDocs___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_missingDocs___closed__1_value_aux_1),((lean_object*)&l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(25, 85, 84, 40, 188, 20, 254, 124)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_missingDocs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_missingDocs___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(18, 71, 108, 38, 230, 58, 128, 97)}};
static const lean_object* l_Lean_Linter_MissingDocs_missingDocs___closed__1 = (const lean_object*)&l_Lean_Linter_MissingDocs_missingDocs___closed__1_value;
static const lean_ctor_object l_Lean_Linter_MissingDocs_missingDocs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_missingDocs___closed__0_value),((lean_object*)&l_Lean_Linter_MissingDocs_missingDocs___closed__1_value)}};
static const lean_object* l_Lean_Linter_MissingDocs_missingDocs___closed__2 = (const lean_object*)&l_Lean_Linter_MissingDocs_missingDocs___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_MissingDocs_missingDocs = (const lean_object*)&l_Lean_Linter_MissingDocs_missingDocs___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_MissingDocs_missingDocs_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_MissingDocs_missingDocs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_2727349317____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_2727349317____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_addBuiltinHandler(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_addBuiltinHandler___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0___closed__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0___closed__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0___closed__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0___closed__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0___closed__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0___closed__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Cannot add attribute `["};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` to declaration `"};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "` because it is in an imported module"};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Invalid attribute scope: Attribute `["};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "]` must be global, not `"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "global"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__4_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__5 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__5_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scoped"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__0;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__1_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__2 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__2_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__3_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__4;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__6;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__7;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__8_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__8_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__18_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "addBuiltinHandler"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "toHandler"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "Unexpected type for missing docs handler: Expected `"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__4_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "` or `"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__4_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__4_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__5_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__5_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__6_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "`, but `"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__6_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__6_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__7_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__7_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__8_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` has type"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__8_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__8_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__9_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__9_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(196, 60, 89, 104, 222, 184, 104, 61)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__4_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(109, 71, 38, 78, 110, 121, 74, 1)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__4_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__4_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__5_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__4_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(88, 142, 224, 55, 28, 93, 167, 225)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__5_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__5_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__6_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__5_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(209, 103, 172, 65, 70, 157, 34, 163)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__6_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__6_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__7_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__6_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(171, 148, 68, 129, 115, 167, 183, 177)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__7_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__7_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__8_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__7_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(206, 122, 164, 204, 198, 240, 47, 250)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__8_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__8_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__9_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__9_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__9_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__10_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__8_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__9_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(227, 126, 117, 226, 154, 200, 97, 116)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__10_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__10_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__11_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__11_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__11_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__12_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__10_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__11_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 196, 57, 107, 246, 197, 178, 184)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__12_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__12_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__13_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__12_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(127, 128, 182, 1, 36, 142, 177, 207)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__13_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__13_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__14_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__13_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(101, 71, 117, 107, 84, 87, 150, 165)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__14_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__14_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__15_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__14_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(184, 204, 34, 53, 202, 221, 81, 185)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__15_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__15_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__16_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__15_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),((lean_object*)(((size_t)(573930092) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(172, 197, 83, 166, 62, 29, 54, 93)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__16_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__16_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__17_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__17_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__17_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__18_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__16_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__17_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 131, 13, 165, 249, 155, 232, 74)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__18_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__18_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__19_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__19_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__19_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__20_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__18_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__19_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(3, 89, 8, 244, 216, 147, 164, 205)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__20_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__20_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__21_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__20_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(198, 101, 182, 233, 18, 154, 75, 102)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__21_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__21_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__22_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "adds a syntax traversal for the missing docs linter"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__22_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__22_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__23_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "(builtin) "};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__23_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__23_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "builtin_missing_docs_handler"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(113, 152, 43, 164, 254, 29, 181, 30)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "missing_docs_handler"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 38, 13, 120, 230, 132, 199, 211)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_MissingDocs_lint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "missing doc string for "};
static const lean_object* l_Lean_Linter_MissingDocs_lint___closed__0 = (const lean_object*)&l_Lean_Linter_MissingDocs_lint___closed__0_value;
static lean_once_cell_t l_Lean_Linter_MissingDocs_lint___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_MissingDocs_lint___closed__1;
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lint(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_MissingDocs_lintEmpty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "empty doc string for "};
static const lean_object* l_Lean_Linter_MissingDocs_lintEmpty___closed__0 = (const lean_object*)&l_Lean_Linter_MissingDocs_lintEmpty___closed__0_value;
static lean_once_cell_t l_Lean_Linter_MissingDocs_lintEmpty___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_MissingDocs_lintEmpty___closed__1;
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintEmpty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintNamed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintNamed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintEmptyNamed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintEmptyNamed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_MissingDocs_lintField___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Linter_MissingDocs_lintField___closed__0 = (const lean_object*)&l_Lean_Linter_MissingDocs_lintField___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintField(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintField___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintEmptyField(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintEmptyField___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintStructField(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintStructField___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unexpected doc string"};
static const lean_object* l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__0 = (const lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__1;
static const lean_string_object l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2 = (const lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2_value;
static const lean_string_object l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3 = (const lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3_value;
static const lean_string_object l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "commentBody"};
static const lean_object* l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__4 = (const lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "versoCommentBody"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString___closed__0 = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_isMissingDoc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_isMissingDoc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__2_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__2_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__2_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "inherit_doc"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(83, 8, 69, 42, 53, 230, 51, 166)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__4_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_MissingDocs_hasInheritDoc(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_hasInheritDoc___boxed(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tactic_alt"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0___closed__1_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 168, 96, 206, 229, 58, 101)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0___closed__1_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_MissingDocs_hasTacticAlt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_hasTacticAlt___boxed(lean_object*);
static const lean_ctor_object l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__0_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__0_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__0_value_aux_2),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__17_value),LEAN_SCALAR_PTR_LITERAL(213, 248, 16, 228, 25, 227, 72, 143)}};
static const lean_object* l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__0 = (const lean_object*)&l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__0_value;
static const lean_ctor_object l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__1_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__1_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__1_value_aux_2),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__18_value),LEAN_SCALAR_PTR_LITERAL(99, 134, 241, 204, 211, 206, 124, 144)}};
static const lean_object* l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__1 = (const lean_object*)&l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_declModifiersDocStatus(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_declModifiersDocStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_declModifiersPubNoDoc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_declModifiersPubNoDoc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "abbrev"};
static const lean_object* l_Lean_Linter_MissingDocs_lintDeclHead___closed__0 = (const lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__0_value;
static const lean_ctor_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__1_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__1_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__1_value_aux_2),((lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 181, 25, 109, 89, 238, 86, 99)}};
static const lean_object* l_Lean_Linter_MissingDocs_lintDeclHead___closed__1 = (const lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__1_value;
static const lean_string_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Linter_MissingDocs_lintDeclHead___closed__2 = (const lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__2_value;
static const lean_ctor_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__3_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__3_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__3_value_aux_2),((lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__2_value),LEAN_SCALAR_PTR_LITERAL(248, 187, 217, 228, 39, 184, 218, 135)}};
static const lean_object* l_Lean_Linter_MissingDocs_lintDeclHead___closed__3 = (const lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__3_value;
static const lean_string_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "opaque"};
static const lean_object* l_Lean_Linter_MissingDocs_lintDeclHead___closed__4 = (const lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__4_value;
static const lean_ctor_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__5_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__5_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__5_value_aux_2),((lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__4_value),LEAN_SCALAR_PTR_LITERAL(111, 217, 152, 21, 13, 97, 204, 102)}};
static const lean_object* l_Lean_Linter_MissingDocs_lintDeclHead___closed__5 = (const lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__5_value;
static const lean_string_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "axiom"};
static const lean_object* l_Lean_Linter_MissingDocs_lintDeclHead___closed__6 = (const lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__6_value;
static const lean_ctor_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__7_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__7_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__7_value_aux_2),((lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__6_value),LEAN_SCALAR_PTR_LITERAL(98, 213, 89, 132, 71, 178, 86, 86)}};
static const lean_object* l_Lean_Linter_MissingDocs_lintDeclHead___closed__7 = (const lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__7_value;
static const lean_string_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "inductive"};
static const lean_object* l_Lean_Linter_MissingDocs_lintDeclHead___closed__8 = (const lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__8_value;
static const lean_ctor_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__9_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__9_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__9_value_aux_2),((lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__8_value),LEAN_SCALAR_PTR_LITERAL(167, 178, 72, 69, 244, 64, 6, 60)}};
static const lean_object* l_Lean_Linter_MissingDocs_lintDeclHead___closed__9 = (const lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__9_value;
static const lean_string_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "classInductive"};
static const lean_object* l_Lean_Linter_MissingDocs_lintDeclHead___closed__10 = (const lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__10_value;
static const lean_ctor_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__11_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__11_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__11_value_aux_2),((lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__10_value),LEAN_SCALAR_PTR_LITERAL(25, 56, 34, 53, 6, 51, 66, 48)}};
static const lean_object* l_Lean_Linter_MissingDocs_lintDeclHead___closed__11 = (const lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__11_value;
static const lean_string_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "structure"};
static const lean_object* l_Lean_Linter_MissingDocs_lintDeclHead___closed__12 = (const lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__12_value;
static const lean_ctor_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__13_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__13_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__13_value_aux_2),((lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__12_value),LEAN_SCALAR_PTR_LITERAL(180, 236, 187, 15, 83, 171, 117, 65)}};
static const lean_object* l_Lean_Linter_MissingDocs_lintDeclHead___closed__13 = (const lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__13_value;
static const lean_string_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "public structure"};
static const lean_object* l_Lean_Linter_MissingDocs_lintDeclHead___closed__14 = (const lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__14_value;
static const lean_string_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "public inductive"};
static const lean_object* l_Lean_Linter_MissingDocs_lintDeclHead___closed__15 = (const lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__15_value;
static const lean_string_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "public axiom"};
static const lean_object* l_Lean_Linter_MissingDocs_lintDeclHead___closed__16 = (const lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__16_value;
static const lean_string_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "public opaque"};
static const lean_object* l_Lean_Linter_MissingDocs_lintDeclHead___closed__17 = (const lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__17_value;
static const lean_string_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "public def"};
static const lean_object* l_Lean_Linter_MissingDocs_lintDeclHead___closed__18 = (const lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__18_value;
static const lean_string_object l_Lean_Linter_MissingDocs_lintDeclHead___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "public abbrev"};
static const lean_object* l_Lean_Linter_MissingDocs_lintDeclHead___closed__19 = (const lean_object*)&l_Lean_Linter_MissingDocs_lintDeclHead___closed__19_value;
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintDeclHead(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintDeclHead___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus___closed__0 = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "computed field"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6___lam__0(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__7(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5_spec__7(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "public constructor"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__0(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "public field"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "structSimpleBinder"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12___closed__1_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12___closed__1_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 230, 214, 182, 254, 52, 213, 225)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Linter_MissingDocs_checkDecl___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_MissingDocs_checkDecl___closed__0;
static lean_once_cell_t l_Lean_Linter_MissingDocs_checkDecl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_MissingDocs_checkDecl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4_spec__9(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__0 = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__1_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__1_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__1 = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__1_value;
static lean_once_cell_t l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1();
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___boxed(lean_object*);
static const lean_string_object l_Lean_Linter_MissingDocs_checkInit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "initializer"};
static const lean_object* l_Lean_Linter_MissingDocs_checkInit___closed__0 = (const lean_object*)&l_Lean_Linter_MissingDocs_checkInit___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkInit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkInit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "initialize"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__0 = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__1_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__1_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 206, 156, 211, 241, 221, 187, 166)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__1 = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__1_value;
static lean_once_cell_t l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1();
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___boxed(lean_object*);
static const lean_string_object l_Lean_Linter_MissingDocs_checkNotation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Linter_MissingDocs_checkNotation___closed__0 = (const lean_object*)&l_Lean_Linter_MissingDocs_checkNotation___closed__0_value;
static const lean_ctor_object l_Lean_Linter_MissingDocs_checkNotation___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_checkNotation___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_checkNotation___closed__1_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_checkNotation___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_checkNotation___closed__1_value_aux_1),((lean_object*)&l_Lean_Linter_MissingDocs_checkNotation___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_checkNotation___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_checkNotation___closed__1_value_aux_2),((lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(136, 104, 45, 91, 146, 14, 86, 4)}};
static const lean_object* l_Lean_Linter_MissingDocs_checkNotation___closed__1 = (const lean_object*)&l_Lean_Linter_MissingDocs_checkNotation___closed__1_value;
static const lean_string_object l_Lean_Linter_MissingDocs_checkNotation___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "notation"};
static const lean_object* l_Lean_Linter_MissingDocs_checkNotation___closed__2 = (const lean_object*)&l_Lean_Linter_MissingDocs_checkNotation___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkNotation(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkNotation___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___closed__0_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___closed__0_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___closed__0_value_aux_2),((lean_object*)&l_Lean_Linter_MissingDocs_checkNotation___closed__2_value),LEAN_SCALAR_PTR_LITERAL(13, 34, 53, 7, 182, 20, 8, 182)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___closed__0 = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1();
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkMixfix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkMixfix___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mixfix"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__0 = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__1_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__1_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 31, 80, 86, 44, 46, 155, 0)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__1 = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__1_value;
static lean_once_cell_t l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1();
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___boxed(lean_object*);
static const lean_string_object l_Lean_Linter_MissingDocs_checkSyntax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "syntax"};
static const lean_object* l_Lean_Linter_MissingDocs_checkSyntax___closed__0 = (const lean_object*)&l_Lean_Linter_MissingDocs_checkSyntax___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntax(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___closed__0_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___closed__0_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___closed__0_value_aux_2),((lean_object*)&l_Lean_Linter_MissingDocs_checkSyntax___closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 60, 146, 133, 142, 21, 8, 39)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___closed__0 = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1();
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_mkSimpleHandler(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_mkSimpleHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntaxAbbrev(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntaxAbbrev___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "syntaxAbbrev"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__0 = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__1_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__1_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 194, 172, 134, 159, 244, 204, 250)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__1 = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__1_value;
static lean_once_cell_t l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1();
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___boxed(lean_object*);
static const lean_string_object l_Lean_Linter_MissingDocs_checkSyntaxCat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "syntax category"};
static const lean_object* l_Lean_Linter_MissingDocs_checkSyntaxCat___closed__0 = (const lean_object*)&l_Lean_Linter_MissingDocs_checkSyntaxCat___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntaxCat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntaxCat___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "syntaxCat"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__0 = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__1_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__1_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(224, 111, 111, 178, 172, 19, 49, 32)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__1 = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__1_value;
static lean_once_cell_t l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1();
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___boxed(lean_object*);
static const lean_string_object l_Lean_Linter_MissingDocs_checkMacro___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "macro"};
static const lean_object* l_Lean_Linter_MissingDocs_checkMacro___closed__0 = (const lean_object*)&l_Lean_Linter_MissingDocs_checkMacro___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkMacro(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkMacro___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___closed__0_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___closed__0_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___closed__0_value_aux_2),((lean_object*)&l_Lean_Linter_MissingDocs_checkMacro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(140, 185, 197, 33, 231, 124, 123, 210)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___closed__0 = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1();
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___boxed(lean_object*);
static const lean_string_object l_Lean_Linter_MissingDocs_checkElab___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "elab"};
static const lean_object* l_Lean_Linter_MissingDocs_checkElab___closed__0 = (const lean_object*)&l_Lean_Linter_MissingDocs_checkElab___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkElab(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkElab___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___closed__0_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___closed__0_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___closed__0_value_aux_2),((lean_object*)&l_Lean_Linter_MissingDocs_checkElab___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 177, 45, 203, 60, 20, 245, 118)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___closed__0 = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1();
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___boxed(lean_object*);
static const lean_string_object l_Lean_Linter_MissingDocs_checkClassAbbrev___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "class abbrev"};
static const lean_object* l_Lean_Linter_MissingDocs_checkClassAbbrev___closed__0 = (const lean_object*)&l_Lean_Linter_MissingDocs_checkClassAbbrev___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkClassAbbrev(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkClassAbbrev___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "classAbbrev"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__0 = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__1_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__1_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 112, 139, 141, 120, 66, 29, 3)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__1 = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__1_value;
static lean_once_cell_t l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1();
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___boxed(lean_object*);
static const lean_string_object l_Lean_Linter_MissingDocs_checkSimpLike___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "simp-like tactic"};
static const lean_object* l_Lean_Linter_MissingDocs_checkSimpLike___closed__0 = (const lean_object*)&l_Lean_Linter_MissingDocs_checkSimpLike___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSimpLike(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSimpLike___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__0 = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__0_value;
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "declareSimpLikeTactic"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__1 = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__2_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(79, 29, 238, 199, 239, 152, 213, 112)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__2 = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__2_value;
static lean_once_cell_t l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1();
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___boxed(lean_object*);
static const lean_string_object l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "option"};
static const lean_object* l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption___closed__0 = (const lean_object*)&l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__0 = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__0_value;
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "registerBuiltinOption"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__1 = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(54, 183, 132, 140, 253, 175, 101, 43)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 128, 225, 170, 242, 224, 12, 82)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__2 = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__2_value;
static lean_once_cell_t l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1();
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "registerOption"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__0 = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(54, 183, 132, 140, 253, 175, 101, 43)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 95, 60, 142, 241, 184, 36, 53)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__1 = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__1_value;
static lean_once_cell_t l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1();
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___boxed(lean_object*);
static const lean_string_object l_Lean_Linter_MissingDocs_checkRegisterSimpAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simp attr"};
static const lean_object* l_Lean_Linter_MissingDocs_checkRegisterSimpAttr___closed__0 = (const lean_object*)&l_Lean_Linter_MissingDocs_checkRegisterSimpAttr___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterSimpAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterSimpAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "registerSimpAttr"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__1_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__1_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(126, 98, 179, 212, 132, 154, 67, 50)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__1_value;
static lean_once_cell_t l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__0;
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Invalid `set_option` command: The option `"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__1;
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "` cannot be configured using `set_option`"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8_spec__10(lean_object*);
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "\nhas type"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__0 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__1;
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "\nbut the option `"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__2 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__3;
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "` expects a value of type"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__4 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__5;
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "set_option value type mismatch: The value"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__6 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__7;
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__8 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__8_value)}};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__9 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__9_value;
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__10 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__10_value)}};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__11 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__3_value)}};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__12 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__12_value;
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__13 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__13_value;
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__14 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__14_value;
static const lean_string_object l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__15 = (const lean_object*)&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__15_value;
static lean_once_cell_t l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__16;
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Unexpected set_option value `"};
static const lean_object* l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__0 = (const lean_object*)&l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__1;
static const lean_string_object l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "`; expected a literal of type `"};
static const lean_object* l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__2 = (const lean_object*)&l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_MissingDocs_handleIn___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "set_option"};
static const lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg___closed__0 = (const lean_object*)&l_Lean_Linter_MissingDocs_handleIn___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Linter_MissingDocs_handleIn___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_handleIn___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_handleIn___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_handleIn___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_handleIn___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Linter_MissingDocs_handleIn___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_MissingDocs_handleIn___redArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Linter_MissingDocs_handleIn___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 223, 149, 245, 150, 86, 134, 198)}};
static const lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg___closed__1 = (const lean_object*)&l_Lean_Linter_MissingDocs_handleIn___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleIn___regBuiltin_Lean_Linter_MissingDocs_handleIn__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "in"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleIn___regBuiltin_Lean_Linter_MissingDocs_handleIn__1___closed__0 = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleIn___regBuiltin_Lean_Linter_MissingDocs_handleIn__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleIn___regBuiltin_Lean_Linter_MissingDocs_handleIn__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleIn___regBuiltin_Lean_Linter_MissingDocs_handleIn__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleIn___regBuiltin_Lean_Linter_MissingDocs_handleIn__1___closed__1_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleIn___regBuiltin_Lean_Linter_MissingDocs_handleIn__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleIn___regBuiltin_Lean_Linter_MissingDocs_handleIn__1___closed__1_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleIn___regBuiltin_Lean_Linter_MissingDocs_handleIn__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleIn___regBuiltin_Lean_Linter_MissingDocs_handleIn__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleIn___regBuiltin_Lean_Linter_MissingDocs_handleIn__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 79, 35, 19, 21, 38, 89, 10)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleIn___regBuiltin_Lean_Linter_MissingDocs_handleIn__1___closed__1 = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleIn___regBuiltin_Lean_Linter_MissingDocs_handleIn__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleIn___regBuiltin_Lean_Linter_MissingDocs_handleIn__1();
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleIn___regBuiltin_Lean_Linter_MissingDocs_handleIn__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_MissingDocs_handleMutual_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_MissingDocs_handleMutual_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleMutual___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleMutual___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleMutual(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleMutual___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleMutual___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mutual"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleMutual___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1___closed__0 = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleMutual___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleMutual___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleMutual___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleMutual___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1___closed__1_value_aux_0),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleMutual___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleMutual___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1___closed__1_value_aux_1),((lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleMutual___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleMutual___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleMutual___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 205, 8, 5, 164, 77, 17, 1)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleMutual___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1___closed__1 = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleMutual___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleMutual___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1();
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleMutual___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_53_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_));
v___x_54_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_));
v___x_55_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_));
v___x_56_ = l_Lean_Option_register___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__spec__0(v___x_53_, v___x_54_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4____boxed(lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_();
return v_res_58_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_getLinterMissingDocs(lean_object* v_o_59_){
_start:
{
lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_60_ = l_Lean_Linter_linter_missingDocs;
v___x_61_ = l_Lean_Linter_getLinterValue(v___x_60_, v_o_59_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterMissingDocs___boxed(lean_object* v_o_62_){
_start:
{
uint8_t v_res_63_; lean_object* v_r_64_; 
v_res_63_ = l_Lean_Linter_getLinterMissingDocs(v_o_62_);
lean_dec_ref(v_o_62_);
v_r_64_ = lean_box(v_res_63_);
return v_r_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_SimpleHandler_toHandler(lean_object* v_h_65_, uint8_t v_enabled_66_, lean_object* v_stx_67_, lean_object* v_a_68_, lean_object* v_a_69_){
_start:
{
if (v_enabled_66_ == 0)
{
lean_object* v___x_71_; lean_object* v___x_72_; 
lean_dec(v_stx_67_);
lean_dec_ref(v_h_65_);
v___x_71_ = lean_box(0);
v___x_72_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
return v___x_72_;
}
else
{
lean_object* v___x_73_; 
lean_inc(v_a_69_);
lean_inc_ref(v_a_68_);
v___x_73_ = lean_apply_4(v_h_65_, v_stx_67_, v_a_68_, v_a_69_, lean_box(0));
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed(lean_object* v_h_74_, lean_object* v_enabled_75_, lean_object* v_stx_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
uint8_t v_enabled_boxed_80_; lean_object* v_res_81_; 
v_enabled_boxed_80_ = lean_unbox(v_enabled_75_);
v_res_81_ = l_Lean_Linter_MissingDocs_SimpleHandler_toHandler(v_h_74_, v_enabled_boxed_80_, v_stx_76_, v_a_77_, v_a_78_);
lean_dec(v_a_78_);
lean_dec_ref(v_a_77_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Linter_MissingDocs_mkHandlerUnsafe_spec__0___redArg(lean_object* v_e_82_){
_start:
{
if (lean_obj_tag(v_e_82_) == 0)
{
lean_object* v_a_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_92_; 
v_a_84_ = lean_ctor_get(v_e_82_, 0);
v_isSharedCheck_92_ = !lean_is_exclusive(v_e_82_);
if (v_isSharedCheck_92_ == 0)
{
v___x_86_ = v_e_82_;
v_isShared_87_ = v_isSharedCheck_92_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_a_84_);
lean_dec(v_e_82_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_92_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_88_; lean_object* v___x_90_; 
v___x_88_ = lean_mk_io_user_error(v_a_84_);
if (v_isShared_87_ == 0)
{
lean_ctor_set_tag(v___x_86_, 1);
lean_ctor_set(v___x_86_, 0, v___x_88_);
v___x_90_ = v___x_86_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v___x_88_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
}
else
{
lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_100_; 
v_a_93_ = lean_ctor_get(v_e_82_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v_e_82_);
if (v_isSharedCheck_100_ == 0)
{
v___x_95_ = v_e_82_;
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v_e_82_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_96_ == 0)
{
lean_ctor_set_tag(v___x_95_, 0);
v___x_98_ = v___x_95_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_a_93_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Linter_MissingDocs_mkHandlerUnsafe_spec__0___redArg___boxed(lean_object* v_e_101_, lean_object* v_a_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_IO_ofExcept___at___00Lean_Linter_MissingDocs_mkHandlerUnsafe_spec__0___redArg(v_e_101_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Linter_MissingDocs_mkHandlerUnsafe_spec__0(lean_object* v_00_u03b1_104_, lean_object* v_e_105_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_IO_ofExcept___at___00Lean_Linter_MissingDocs_mkHandlerUnsafe_spec__0___redArg(v_e_105_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Linter_MissingDocs_mkHandlerUnsafe_spec__0___boxed(lean_object* v_00_u03b1_108_, lean_object* v_e_109_, lean_object* v_a_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_IO_ofExcept___at___00Lean_Linter_MissingDocs_mkHandlerUnsafe_spec__0(v_00_u03b1_108_, v_e_109_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_mkHandlerUnsafe(lean_object* v_constName_119_, lean_object* v_a_120_){
_start:
{
lean_object* v_env_131_; lean_object* v_opts_132_; uint8_t v___x_133_; lean_object* v___x_134_; 
v_env_131_ = lean_ctor_get(v_a_120_, 0);
v_opts_132_ = lean_ctor_get(v_a_120_, 1);
v___x_133_ = 0;
lean_inc(v_constName_119_);
lean_inc_ref(v_env_131_);
v___x_134_ = l_Lean_Environment_find_x3f(v_env_131_, v_constName_119_, v___x_133_);
if (lean_obj_tag(v___x_134_) == 0)
{
lean_object* v___x_135_; uint8_t v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_135_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__2));
v___x_136_ = 1;
v___x_137_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_constName_119_, v___x_136_);
v___x_138_ = lean_string_append(v___x_135_, v___x_137_);
lean_dec_ref(v___x_137_);
v___x_139_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__3));
v___x_140_ = lean_string_append(v___x_138_, v___x_139_);
v___x_141_ = lean_mk_io_user_error(v___x_140_);
v___x_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
return v___x_142_;
}
else
{
lean_object* v_val_143_; lean_object* v___x_144_; 
v_val_143_ = lean_ctor_get(v___x_134_, 0);
lean_inc(v_val_143_);
lean_dec_ref_known(v___x_134_, 1);
v___x_144_ = l_Lean_ConstantInfo_type(v_val_143_);
lean_dec(v_val_143_);
if (lean_obj_tag(v___x_144_) == 4)
{
lean_object* v_declName_145_; 
v_declName_145_ = lean_ctor_get(v___x_144_, 0);
lean_inc(v_declName_145_);
lean_dec_ref_known(v___x_144_, 2);
if (lean_obj_tag(v_declName_145_) == 1)
{
lean_object* v_pre_146_; 
v_pre_146_ = lean_ctor_get(v_declName_145_, 0);
lean_inc(v_pre_146_);
if (lean_obj_tag(v_pre_146_) == 1)
{
lean_object* v_pre_147_; 
v_pre_147_ = lean_ctor_get(v_pre_146_, 0);
lean_inc(v_pre_147_);
if (lean_obj_tag(v_pre_147_) == 1)
{
lean_object* v_pre_148_; 
v_pre_148_ = lean_ctor_get(v_pre_147_, 0);
lean_inc(v_pre_148_);
if (lean_obj_tag(v_pre_148_) == 1)
{
lean_object* v_pre_149_; 
v_pre_149_ = lean_ctor_get(v_pre_148_, 0);
if (lean_obj_tag(v_pre_149_) == 0)
{
lean_object* v_str_150_; lean_object* v_str_151_; lean_object* v_str_152_; lean_object* v_str_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v_str_150_ = lean_ctor_get(v_declName_145_, 1);
lean_inc_ref(v_str_150_);
lean_dec_ref_known(v_declName_145_, 2);
v_str_151_ = lean_ctor_get(v_pre_146_, 1);
lean_inc_ref(v_str_151_);
lean_dec_ref_known(v_pre_146_, 2);
v_str_152_ = lean_ctor_get(v_pre_147_, 1);
lean_inc_ref(v_str_152_);
lean_dec_ref_known(v_pre_147_, 2);
v_str_153_ = lean_ctor_get(v_pre_148_, 1);
lean_inc_ref(v_str_153_);
lean_dec_ref_known(v_pre_148_, 2);
v___x_154_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_));
v___x_155_ = lean_string_dec_eq(v_str_153_, v___x_154_);
lean_dec_ref(v_str_153_);
if (v___x_155_ == 0)
{
lean_dec_ref(v_str_152_);
lean_dec_ref(v_str_151_);
lean_dec_ref(v_str_150_);
goto v___jp_122_;
}
else
{
lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_156_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_));
v___x_157_ = lean_string_dec_eq(v_str_152_, v___x_156_);
lean_dec_ref(v_str_152_);
if (v___x_157_ == 0)
{
lean_dec_ref(v_str_151_);
lean_dec_ref(v_str_150_);
goto v___jp_122_;
}
else
{
lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_158_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__4));
v___x_159_ = lean_string_dec_eq(v_str_151_, v___x_158_);
lean_dec_ref(v_str_151_);
if (v___x_159_ == 0)
{
lean_dec_ref(v_str_150_);
goto v___jp_122_;
}
else
{
lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_160_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__5));
v___x_161_ = lean_string_dec_eq(v_str_150_, v___x_160_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_162_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__6));
v___x_163_ = lean_string_dec_eq(v_str_150_, v___x_162_);
lean_dec_ref(v_str_150_);
if (v___x_163_ == 0)
{
goto v___jp_122_;
}
else
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = l_Lean_Environment_evalConst___redArg(v_env_131_, v_opts_132_, v_constName_119_, v___x_163_);
lean_dec(v_constName_119_);
v___x_165_ = l_IO_ofExcept___at___00Lean_Linter_MissingDocs_mkHandlerUnsafe_spec__0___redArg(v___x_164_);
return v___x_165_;
}
}
else
{
lean_object* v___x_166_; lean_object* v___x_167_; 
lean_dec_ref(v_str_150_);
v___x_166_ = l_Lean_Environment_evalConst___redArg(v_env_131_, v_opts_132_, v_constName_119_, v___x_161_);
lean_dec(v_constName_119_);
v___x_167_ = l_IO_ofExcept___at___00Lean_Linter_MissingDocs_mkHandlerUnsafe_spec__0___redArg(v___x_166_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_176_; 
v_a_168_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_176_ == 0)
{
v___x_170_ = v___x_167_;
v_isShared_171_ = v_isSharedCheck_176_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_167_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_176_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_172_; lean_object* v___x_174_; 
v___x_172_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_172_, 0, v_a_168_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v___x_172_);
v___x_174_ = v___x_170_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_172_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
else
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_184_; 
v_a_177_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_184_ == 0)
{
v___x_179_ = v___x_167_;
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_167_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_180_ == 0)
{
v___x_182_ = v___x_179_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_a_177_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_148_, 2);
lean_dec_ref_known(v_pre_147_, 2);
lean_dec_ref_known(v_pre_146_, 2);
lean_dec_ref_known(v_declName_145_, 2);
goto v___jp_122_;
}
}
else
{
lean_dec_ref_known(v_pre_147_, 2);
lean_dec(v_pre_148_);
lean_dec_ref_known(v_pre_146_, 2);
lean_dec_ref_known(v_declName_145_, 2);
goto v___jp_122_;
}
}
else
{
lean_dec_ref_known(v_pre_146_, 2);
lean_dec(v_pre_147_);
lean_dec_ref_known(v_declName_145_, 2);
goto v___jp_122_;
}
}
else
{
lean_dec_ref_known(v_declName_145_, 2);
lean_dec(v_pre_146_);
goto v___jp_122_;
}
}
else
{
lean_dec(v_declName_145_);
goto v___jp_122_;
}
}
else
{
lean_dec_ref(v___x_144_);
goto v___jp_122_;
}
}
v___jp_122_:
{
lean_object* v___x_123_; uint8_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_123_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__0));
v___x_124_ = 1;
v___x_125_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_constName_119_, v___x_124_);
v___x_126_ = lean_string_append(v___x_123_, v___x_125_);
lean_dec_ref(v___x_125_);
v___x_127_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__1));
v___x_128_ = lean_string_append(v___x_126_, v___x_127_);
v___x_129_ = lean_mk_io_user_error(v___x_128_);
v___x_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
return v___x_130_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_mkHandlerUnsafe___boxed(lean_object* v_constName_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_Linter_MissingDocs_mkHandlerUnsafe(v_constName_185_, v_a_186_);
lean_dec_ref(v_a_186_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_537855421____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_190_ = lean_box(1);
v___x_191_ = lean_st_mk_ref(v___x_190_);
v___x_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_537855421____hygCtx___hyg_2____boxed(lean_object* v_a_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_537855421____hygCtx___hyg_2_();
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_(lean_object* v_s_195_){
_start:
{
lean_object* v_fst_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v_fst_196_ = lean_ctor_get(v_s_195_, 0);
lean_inc(v_fst_196_);
lean_dec_ref(v_s_195_);
v___x_197_ = l_List_reverse___redArg(v_fst_196_);
v___x_198_ = lean_array_mk(v___x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_(lean_object* v_s_202_){
_start:
{
lean_object* v_fst_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_214_; 
v_fst_203_ = lean_ctor_get(v_s_202_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v_s_202_);
if (v_isSharedCheck_214_ == 0)
{
lean_object* v_unused_215_; 
v_unused_215_ = lean_ctor_get(v_s_202_, 1);
lean_dec(v_unused_215_);
v___x_205_ = v_s_202_;
v_isShared_206_ = v_isSharedCheck_214_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_fst_203_);
lean_dec(v_s_202_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_214_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_212_; 
v___x_207_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__1_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_));
v___x_208_ = l_List_lengthTR___redArg(v_fst_203_);
lean_dec(v_fst_203_);
v___x_209_ = l_Nat_reprFast(v___x_208_);
v___x_210_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
if (v_isShared_206_ == 0)
{
lean_ctor_set_tag(v___x_205_, 5);
lean_ctor_set(v___x_205_, 1, v___x_210_);
lean_ctor_set(v___x_205_, 0, v___x_207_);
v___x_212_ = v___x_205_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_207_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v___x_210_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_(lean_object* v_x_216_, lean_object* v_s_217_){
_start:
{
lean_object* v_fst_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v_fst_218_ = lean_ctor_get(v_s_217_, 0);
lean_inc(v_fst_218_);
lean_dec_ref(v_s_217_);
v___x_219_ = l_List_reverse___redArg(v_fst_218_);
v___x_220_ = lean_array_mk(v___x_219_);
lean_inc_ref_n(v___x_220_, 2);
v___x_221_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
lean_ctor_set(v___x_221_, 2, v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2____boxed(lean_object* v_x_222_, lean_object* v_s_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_(v_x_222_, v_s_223_);
lean_dec_ref(v_x_222_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__3_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_(lean_object* v_x_225_, lean_object* v_x_226_){
_start:
{
lean_object* v_snd_227_; lean_object* v_fst_228_; lean_object* v_snd_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_255_; 
v_snd_227_ = lean_ctor_get(v_x_226_, 1);
lean_inc(v_snd_227_);
v_fst_228_ = lean_ctor_get(v_x_225_, 0);
v_snd_229_ = lean_ctor_get(v_x_225_, 1);
v_isSharedCheck_255_ = !lean_is_exclusive(v_x_225_);
if (v_isSharedCheck_255_ == 0)
{
v___x_231_ = v_x_225_;
v_isShared_232_ = v_isSharedCheck_255_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_snd_229_);
lean_inc(v_fst_228_);
lean_dec(v_x_225_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_255_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v_fst_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_253_; 
v_fst_233_ = lean_ctor_get(v_x_226_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v_x_226_);
if (v_isSharedCheck_253_ == 0)
{
lean_object* v_unused_254_; 
v_unused_254_ = lean_ctor_get(v_x_226_, 1);
lean_dec(v_unused_254_);
v___x_235_ = v_x_226_;
v_isShared_236_ = v_isSharedCheck_253_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_fst_233_);
lean_dec(v_x_226_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_253_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v_fst_237_; lean_object* v_snd_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_252_; 
v_fst_237_ = lean_ctor_get(v_snd_227_, 0);
v_snd_238_ = lean_ctor_get(v_snd_227_, 1);
v_isSharedCheck_252_ = !lean_is_exclusive(v_snd_227_);
if (v_isSharedCheck_252_ == 0)
{
v___x_240_ = v_snd_227_;
v_isShared_241_ = v_isSharedCheck_252_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_snd_238_);
lean_inc(v_fst_237_);
lean_dec(v_snd_227_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_252_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
lean_inc(v_fst_237_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 1, v_fst_237_);
lean_ctor_set(v___x_240_, 0, v_fst_233_);
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_fst_233_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v_fst_237_);
v___x_243_ = v_reuseFailAlloc_251_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
lean_object* v___x_245_; 
if (v_isShared_232_ == 0)
{
lean_ctor_set_tag(v___x_231_, 1);
lean_ctor_set(v___x_231_, 1, v_fst_228_);
lean_ctor_set(v___x_231_, 0, v___x_243_);
v___x_245_ = v___x_231_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_243_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_fst_228_);
v___x_245_ = v_reuseFailAlloc_250_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_246_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_237_, v_snd_238_, v_snd_229_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 1, v___x_246_);
lean_ctor_set(v___x_235_, 0, v___x_245_);
v___x_248_ = v___x_235_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_245_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v___x_246_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__4_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_(lean_object* v___x_256_){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_258_ = lean_st_ref_get(v___x_256_);
v___x_259_ = lean_box(0);
v___x_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set(v___x_260_, 1, v___x_258_);
v___x_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__4_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2____boxed(lean_object* v___x_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__4_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_(v___x_262_);
lean_dec(v___x_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__spec__0(lean_object* v_as_265_, size_t v_i_266_, size_t v_stop_267_, lean_object* v_b_268_, lean_object* v___y_269_){
_start:
{
uint8_t v___x_271_; 
v___x_271_ = lean_usize_dec_eq(v_i_266_, v_stop_267_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; lean_object* v_fst_273_; lean_object* v_snd_274_; lean_object* v___x_275_; 
v___x_272_ = lean_array_uget_borrowed(v_as_265_, v_i_266_);
v_fst_273_ = lean_ctor_get(v___x_272_, 0);
v_snd_274_ = lean_ctor_get(v___x_272_, 1);
lean_inc(v_fst_273_);
v___x_275_ = l_Lean_Linter_MissingDocs_mkHandlerUnsafe(v_fst_273_, v___y_269_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v___x_277_; size_t v___x_278_; size_t v___x_279_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
lean_dec_ref_known(v___x_275_, 1);
lean_inc(v_snd_274_);
v___x_277_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_snd_274_, v_a_276_, v_b_268_);
v___x_278_ = ((size_t)1ULL);
v___x_279_ = lean_usize_add(v_i_266_, v___x_278_);
v_i_266_ = v___x_279_;
v_b_268_ = v___x_277_;
goto _start;
}
else
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_288_; 
lean_dec(v_b_268_);
v_a_281_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_288_ == 0)
{
v___x_283_ = v___x_275_;
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_275_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_286_; 
if (v_isShared_284_ == 0)
{
v___x_286_ = v___x_283_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_a_281_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
else
{
lean_object* v___x_289_; 
v___x_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_289_, 0, v_b_268_);
return v___x_289_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__spec__0___boxed(lean_object* v_as_290_, lean_object* v_i_291_, lean_object* v_stop_292_, lean_object* v_b_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
size_t v_i_boxed_296_; size_t v_stop_boxed_297_; lean_object* v_res_298_; 
v_i_boxed_296_ = lean_unbox_usize(v_i_291_);
lean_dec(v_i_291_);
v_stop_boxed_297_ = lean_unbox_usize(v_stop_292_);
lean_dec(v_stop_292_);
v_res_298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__spec__0(v_as_290_, v_i_boxed_296_, v_stop_boxed_297_, v_b_293_, v___y_294_);
lean_dec_ref(v___y_294_);
lean_dec_ref(v_as_290_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__spec__1(lean_object* v_as_299_, size_t v_i_300_, size_t v_stop_301_, lean_object* v_b_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_a_306_; uint8_t v___x_310_; 
v___x_310_ = lean_usize_dec_eq(v_i_300_, v_stop_301_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; uint8_t v___x_314_; 
v___x_311_ = lean_array_uget_borrowed(v_as_299_, v_i_300_);
v___x_312_ = lean_unsigned_to_nat(0u);
v___x_313_ = lean_array_get_size(v___x_311_);
v___x_314_ = lean_nat_dec_lt(v___x_312_, v___x_313_);
if (v___x_314_ == 0)
{
v_a_306_ = v_b_302_;
goto v___jp_305_;
}
else
{
size_t v___x_315_; size_t v___x_316_; lean_object* v___x_317_; 
v___x_315_ = ((size_t)0ULL);
v___x_316_ = lean_usize_of_nat(v___x_313_);
v___x_317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__spec__0(v___x_311_, v___x_315_, v___x_316_, v_b_302_, v___y_303_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v_a_318_; 
v_a_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc(v_a_318_);
lean_dec_ref_known(v___x_317_, 1);
v_a_306_ = v_a_318_;
goto v___jp_305_;
}
else
{
return v___x_317_;
}
}
}
else
{
lean_object* v___x_319_; 
v___x_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_319_, 0, v_b_302_);
return v___x_319_;
}
v___jp_305_:
{
size_t v___x_307_; size_t v___x_308_; 
v___x_307_ = ((size_t)1ULL);
v___x_308_ = lean_usize_add(v_i_300_, v___x_307_);
v_i_300_ = v___x_308_;
v_b_302_ = v_a_306_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_320_, lean_object* v_i_321_, lean_object* v_stop_322_, lean_object* v_b_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
size_t v_i_boxed_326_; size_t v_stop_boxed_327_; lean_object* v_res_328_; 
v_i_boxed_326_ = lean_unbox_usize(v_i_321_);
lean_dec(v_i_321_);
v_stop_boxed_327_ = lean_unbox_usize(v_stop_322_);
lean_dec(v_stop_322_);
v_res_328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__spec__1(v_as_320_, v_i_boxed_326_, v_stop_boxed_327_, v_b_323_, v___y_324_);
lean_dec_ref(v___y_324_);
lean_dec_ref(v_as_320_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__5_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_(lean_object* v___x_329_, lean_object* v_as_330_, lean_object* v___y_331_){
_start:
{
lean_object* v_a_334_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_338_ = lean_st_ref_get(v___x_329_);
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = lean_array_get_size(v_as_330_);
v___x_341_ = lean_nat_dec_lt(v___x_339_, v___x_340_);
if (v___x_341_ == 0)
{
v_a_334_ = v___x_338_;
goto v___jp_333_;
}
else
{
size_t v___x_342_; size_t v___x_343_; lean_object* v___x_344_; 
v___x_342_ = ((size_t)0ULL);
v___x_343_ = lean_usize_of_nat(v___x_340_);
v___x_344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__spec__1(v_as_330_, v___x_342_, v___x_343_, v___x_338_, v___y_331_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_a_345_);
lean_dec_ref_known(v___x_344_, 1);
v_a_334_ = v_a_345_;
goto v___jp_333_;
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
v_a_346_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_344_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_344_);
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
v___jp_333_:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_335_ = lean_box(0);
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v_a_334_);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__5_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2____boxed(lean_object* v___x_354_, lean_object* v_as_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__5_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_(v___x_354_, v_as_355_, v___y_356_);
lean_dec_ref(v___y_356_);
lean_dec_ref(v_as_355_);
lean_dec(v___x_354_);
return v_res_358_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__6_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_369_; lean_object* v___f_370_; 
v___x_369_ = l_Lean_Linter_MissingDocs_builtinHandlersRef;
v___f_370_ = lean_alloc_closure((void*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__4_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_370_, 0, v___x_369_);
return v___f_370_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__7_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_371_; lean_object* v___f_372_; 
v___x_371_ = l_Lean_Linter_MissingDocs_builtinHandlersRef;
v___f_372_ = lean_alloc_closure((void*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__5_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2____boxed), 4, 1);
lean_closure_set(v___f_372_, 0, v___x_371_);
return v___f_372_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__8_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___f_376_; lean_object* v___f_377_; lean_object* v___f_378_; lean_object* v___f_379_; lean_object* v___f_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_373_ = 0;
v___x_374_ = lean_box(0);
v___x_375_ = lean_box(2);
v___f_376_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__1_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_));
v___f_377_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__2_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_));
v___f_378_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__3_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_));
v___f_379_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__7_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__7_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__7_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_);
v___f_380_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__6_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__6_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__6_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_);
v___x_381_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_));
v___x_382_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_382_, 0, v___x_381_);
lean_ctor_set(v___x_382_, 1, v___f_380_);
lean_ctor_set(v___x_382_, 2, v___f_379_);
lean_ctor_set(v___x_382_, 3, v___f_378_);
lean_ctor_set(v___x_382_, 4, v___f_377_);
lean_ctor_set(v___x_382_, 5, v___f_376_);
lean_ctor_set(v___x_382_, 6, v___x_375_);
lean_ctor_set(v___x_382_, 7, v___x_374_);
lean_ctor_set_uint8(v___x_382_, sizeof(void*)*8, v___x_373_);
lean_ctor_set_uint8(v___x_382_, sizeof(void*)*8 + 1, v___x_373_);
return v___x_382_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__9_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___f_383_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__0_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_));
v___x_384_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__8_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__8_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__8_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_);
v___x_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
lean_ctor_set(v___x_385_, 1, v___f_383_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__9_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__9_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__9_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_);
v___x_388_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2____boxed(lean_object* v_a_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_();
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_addHandler___lam__0(lean_object* v_addEntryFn_391_, lean_object* v___x_392_, lean_object* v_s_393_){
_start:
{
lean_object* v_importedEntries_394_; lean_object* v_state_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_403_; 
v_importedEntries_394_ = lean_ctor_get(v_s_393_, 0);
v_state_395_ = lean_ctor_get(v_s_393_, 1);
v_isSharedCheck_403_ = !lean_is_exclusive(v_s_393_);
if (v_isSharedCheck_403_ == 0)
{
v___x_397_ = v_s_393_;
v_isShared_398_ = v_isSharedCheck_403_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_state_395_);
lean_inc(v_importedEntries_394_);
lean_dec(v_s_393_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_403_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v_state_399_; lean_object* v___x_401_; 
v_state_399_ = lean_apply_2(v_addEntryFn_391_, v_state_395_, v___x_392_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 1, v_state_399_);
v___x_401_ = v___x_397_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_importedEntries_394_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_state_399_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_addHandler(lean_object* v_env_404_, lean_object* v_declName_405_, lean_object* v_key_406_, lean_object* v_h_407_){
_start:
{
lean_object* v___x_408_; lean_object* v_toEnvExtension_409_; lean_object* v_addEntryFn_410_; lean_object* v_asyncMode_411_; uint8_t v_logWrites_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___f_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_408_ = l_Lean_Linter_MissingDocs_missingDocsExt;
v_toEnvExtension_409_ = lean_ctor_get(v___x_408_, 0);
v_addEntryFn_410_ = lean_ctor_get(v___x_408_, 3);
v_asyncMode_411_ = lean_ctor_get(v_toEnvExtension_409_, 2);
v_logWrites_412_ = lean_ctor_get_uint8(v_toEnvExtension_409_, sizeof(void*)*6);
v___x_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_413_, 0, v_key_406_);
lean_ctor_set(v___x_413_, 1, v_h_407_);
v___x_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_414_, 0, v_declName_405_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
lean_inc(v_addEntryFn_410_);
v___f_415_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_addHandler___lam__0), 3, 2);
lean_closure_set(v___f_415_, 0, v_addEntryFn_410_);
lean_closure_set(v___f_415_, 1, v___x_414_);
v___x_416_ = lean_box(0);
v___x_417_ = 1;
if (v_logWrites_412_ == 0)
{
lean_object* v___x_418_; 
lean_inc_ref(v_toEnvExtension_409_);
v___x_418_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_409_, v_env_404_, v___f_415_, v_asyncMode_411_, v___x_416_, v___x_417_);
return v___x_418_;
}
else
{
lean_object* v___x_419_; lean_object* v___x_420_; 
lean_inc_ref_n(v_toEnvExtension_409_, 2);
v___x_419_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_409_, v_env_404_);
lean_dec_ref(v_env_404_);
v___x_420_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_409_, v___x_419_, v___f_415_, v_asyncMode_411_, v___x_416_, v___x_417_);
return v___x_420_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_getHandlers(lean_object* v_env_424_){
_start:
{
lean_object* v___x_425_; lean_object* v_toEnvExtension_426_; lean_object* v_asyncMode_427_; lean_object* v___x_428_; lean_object* v___x_429_; uint8_t v___x_430_; lean_object* v___x_431_; lean_object* v_snd_432_; 
v___x_425_ = l_Lean_Linter_MissingDocs_missingDocsExt;
v_toEnvExtension_426_ = lean_ctor_get(v___x_425_, 0);
v_asyncMode_427_ = lean_ctor_get(v_toEnvExtension_426_, 2);
v___x_428_ = ((lean_object*)(l_Lean_Linter_MissingDocs_getHandlers___closed__0));
v___x_429_ = lean_box(0);
v___x_430_ = 0;
v___x_431_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_428_, v___x_425_, v_env_424_, v_asyncMode_427_, v___x_429_, v___x_430_);
v_snd_432_ = lean_ctor_get(v___x_431_, 1);
lean_inc(v_snd_432_);
lean_dec(v___x_431_);
return v_snd_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_MissingDocs_missingDocs_spec__0_spec__0___redArg(lean_object* v_o_433_, lean_object* v___y_434_){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v_env_438_; lean_object* v___x_439_; lean_object* v_toEnvExtension_440_; lean_object* v_asyncMode_441_; lean_object* v___x_442_; uint8_t v___x_443_; lean_object* v___x_444_; lean_object* v_merged_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_453_; 
v___x_436_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_437_ = lean_st_ref_get(v___y_434_);
v_env_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc_ref(v_env_438_);
lean_dec(v___x_437_);
v___x_439_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_440_ = lean_ctor_get(v___x_439_, 0);
v_asyncMode_441_ = lean_ctor_get(v_toEnvExtension_440_, 2);
v___x_442_ = lean_box(0);
v___x_443_ = 0;
v___x_444_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_436_, v___x_439_, v_env_438_, v_asyncMode_441_, v___x_442_, v___x_443_);
v_merged_445_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_453_ == 0)
{
lean_object* v_unused_454_; 
v_unused_454_ = lean_ctor_get(v___x_444_, 1);
lean_dec(v_unused_454_);
v___x_447_ = v___x_444_;
v_isShared_448_ = v_isSharedCheck_453_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_merged_445_);
lean_dec(v___x_444_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_453_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 1, v_merged_445_);
lean_ctor_set(v___x_447_, 0, v_o_433_);
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_o_433_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_merged_445_);
v___x_450_ = v_reuseFailAlloc_452_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_451_; 
v___x_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
return v___x_451_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_MissingDocs_missingDocs_spec__0_spec__0___redArg___boxed(lean_object* v_o_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_MissingDocs_missingDocs_spec__0_spec__0___redArg(v_o_455_, v___y_456_);
lean_dec(v___y_456_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_MissingDocs_missingDocs_spec__0(lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v_scopes_464_; lean_object* v___x_465_; lean_object* v_opts_466_; lean_object* v___x_467_; 
v___x_462_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_463_ = lean_st_ref_get(v___y_460_);
v_scopes_464_ = lean_ctor_get(v___x_463_, 2);
lean_inc(v_scopes_464_);
lean_dec(v___x_463_);
v___x_465_ = l_List_head_x21___redArg(v___x_462_, v_scopes_464_);
lean_dec(v_scopes_464_);
v_opts_466_ = lean_ctor_get(v___x_465_, 1);
lean_inc_ref(v_opts_466_);
lean_dec(v___x_465_);
v___x_467_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_MissingDocs_missingDocs_spec__0_spec__0___redArg(v_opts_466_, v___y_460_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_MissingDocs_missingDocs_spec__0___boxed(lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_MissingDocs_missingDocs_spec__0(v___y_468_, v___y_469_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_missingDocs___lam__0(lean_object* v_stx_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v___x_476_; lean_object* v_env_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_476_ = lean_st_ref_get(v___y_474_);
v_env_477_ = lean_ctor_get(v___x_476_, 0);
lean_inc_ref(v_env_477_);
lean_dec(v___x_476_);
v___x_478_ = l_Lean_Linter_MissingDocs_getHandlers(v_env_477_);
lean_inc(v_stx_472_);
v___x_479_ = l_Lean_Syntax_getKind(v_stx_472_);
v___x_480_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_478_, v___x_479_);
lean_dec(v___x_479_);
lean_dec(v___x_478_);
if (lean_obj_tag(v___x_480_) == 1)
{
lean_object* v_val_481_; lean_object* v___x_482_; lean_object* v_a_483_; uint8_t v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v_val_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_val_481_);
lean_dec_ref_known(v___x_480_, 1);
v___x_482_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_MissingDocs_missingDocs_spec__0(v___y_473_, v___y_474_);
v_a_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_a_483_);
lean_dec_ref(v___x_482_);
v___x_484_ = l_Lean_Linter_getLinterMissingDocs(v_a_483_);
lean_dec(v_a_483_);
v___x_485_ = lean_box(v___x_484_);
lean_inc(v___y_474_);
lean_inc_ref(v___y_473_);
v___x_486_ = lean_apply_5(v_val_481_, v___x_485_, v_stx_472_, v___y_473_, v___y_474_, lean_box(0));
return v___x_486_;
}
else
{
lean_object* v___x_487_; lean_object* v___x_488_; 
lean_dec(v___x_480_);
lean_dec(v_stx_472_);
v___x_487_ = lean_box(0);
v___x_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
return v___x_488_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_missingDocs___lam__0___boxed(lean_object* v_stx_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_Linter_MissingDocs_missingDocs___lam__0(v_stx_489_, v___y_490_, v___y_491_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_MissingDocs_missingDocs_spec__0_spec__0(lean_object* v_o_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_MissingDocs_missingDocs_spec__0_spec__0___redArg(v_o_504_, v___y_506_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_MissingDocs_missingDocs_spec__0_spec__0___boxed(lean_object* v_o_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_MissingDocs_missingDocs_spec__0_spec__0(v_o_509_, v___y_510_, v___y_511_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_2727349317____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = ((lean_object*)(l_Lean_Linter_MissingDocs_missingDocs));
v___x_516_ = l_Lean_Elab_Command_addLinter(v___x_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_2727349317____hygCtx___hyg_2____boxed(lean_object* v_a_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_2727349317____hygCtx___hyg_2_();
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_addBuiltinHandler(lean_object* v_key_519_, lean_object* v_h_520_){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_522_ = l_Lean_Linter_MissingDocs_builtinHandlersRef;
v___x_523_ = lean_st_ref_take(v___x_522_);
v___x_524_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_key_519_, v_h_520_, v___x_523_);
v___x_525_ = lean_st_ref_put(v___x_522_, v___x_524_);
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_addBuiltinHandler___boxed(lean_object* v_key_527_, lean_object* v_h_528_, lean_object* v_a_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v_key_527_, v_h_528_);
return v_res_530_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_531_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__0);
v___x_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
return v___x_533_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__1, &l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__1_once, _init_l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__1);
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg(lean_object* v_env_536_, lean_object* v___y_537_){
_start:
{
lean_object* v___x_539_; lean_object* v_nextMacroScope_540_; lean_object* v_ngen_541_; lean_object* v_auxDeclNGen_542_; lean_object* v_traceState_543_; lean_object* v_recordedDeps_544_; lean_object* v_messages_545_; lean_object* v_infoState_546_; lean_object* v_snapshotTasks_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_558_; 
v___x_539_ = lean_st_ref_take(v___y_537_);
v_nextMacroScope_540_ = lean_ctor_get(v___x_539_, 1);
v_ngen_541_ = lean_ctor_get(v___x_539_, 2);
v_auxDeclNGen_542_ = lean_ctor_get(v___x_539_, 3);
v_traceState_543_ = lean_ctor_get(v___x_539_, 4);
v_recordedDeps_544_ = lean_ctor_get(v___x_539_, 6);
v_messages_545_ = lean_ctor_get(v___x_539_, 7);
v_infoState_546_ = lean_ctor_get(v___x_539_, 8);
v_snapshotTasks_547_ = lean_ctor_get(v___x_539_, 9);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_558_ == 0)
{
lean_object* v_unused_559_; lean_object* v_unused_560_; 
v_unused_559_ = lean_ctor_get(v___x_539_, 5);
lean_dec(v_unused_559_);
v_unused_560_ = lean_ctor_get(v___x_539_, 0);
lean_dec(v_unused_560_);
v___x_549_ = v___x_539_;
v_isShared_550_ = v_isSharedCheck_558_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_snapshotTasks_547_);
lean_inc(v_infoState_546_);
lean_inc(v_messages_545_);
lean_inc(v_recordedDeps_544_);
lean_inc(v_traceState_543_);
lean_inc(v_auxDeclNGen_542_);
lean_inc(v_ngen_541_);
lean_inc(v_nextMacroScope_540_);
lean_dec(v___x_539_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_558_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_551_ = lean_box(0);
v___x_552_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__2);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 5, v___x_552_);
lean_ctor_set(v___x_549_, 0, v_env_536_);
v___x_554_ = v___x_549_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_env_536_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v_nextMacroScope_540_);
lean_ctor_set(v_reuseFailAlloc_557_, 2, v_ngen_541_);
lean_ctor_set(v_reuseFailAlloc_557_, 3, v_auxDeclNGen_542_);
lean_ctor_set(v_reuseFailAlloc_557_, 4, v_traceState_543_);
lean_ctor_set(v_reuseFailAlloc_557_, 5, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_557_, 6, v_recordedDeps_544_);
lean_ctor_set(v_reuseFailAlloc_557_, 7, v_messages_545_);
lean_ctor_set(v_reuseFailAlloc_557_, 8, v_infoState_546_);
lean_ctor_set(v_reuseFailAlloc_557_, 9, v_snapshotTasks_547_);
v___x_554_ = v_reuseFailAlloc_557_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_st_ref_put(v___y_537_, v___x_554_);
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_551_);
return v___x_556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_env_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg(v_env_561_, v___y_562_);
lean_dec(v___y_562_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2(lean_object* v_env_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg(v_env_565_, v___y_567_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___boxed(lean_object* v_env_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2(v_env_570_, v___y_571_, v___y_572_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
return v_res_574_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__0);
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
return v___x_576_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_577_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_578_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_579_ = lean_unsigned_to_nat(0u);
v___x_580_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
lean_ctor_set(v___x_580_, 2, v___x_579_);
lean_ctor_set(v___x_580_, 3, v___x_579_);
lean_ctor_set(v___x_580_, 4, v___x_578_);
lean_ctor_set(v___x_580_, 5, v___x_578_);
lean_ctor_set(v___x_580_, 6, v___x_578_);
lean_ctor_set(v___x_580_, 7, v___x_578_);
lean_ctor_set(v___x_580_, 8, v___x_578_);
lean_ctor_set(v___x_580_, 9, v___x_578_);
lean_ctor_set(v___x_580_, 10, v___x_578_);
lean_ctor_set(v___x_580_, 11, v___x_577_);
return v___x_580_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_581_ = lean_unsigned_to_nat(32u);
v___x_582_ = lean_mk_empty_array_with_capacity(v___x_581_);
v___x_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
return v___x_583_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_584_ = ((size_t)5ULL);
v___x_585_ = lean_unsigned_to_nat(0u);
v___x_586_ = lean_unsigned_to_nat(32u);
v___x_587_ = lean_mk_empty_array_with_capacity(v___x_586_);
v___x_588_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_589_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_589_, 0, v___x_588_);
lean_ctor_set(v___x_589_, 1, v___x_587_);
lean_ctor_set(v___x_589_, 2, v___x_585_);
lean_ctor_set(v___x_589_, 3, v___x_585_);
lean_ctor_set_usize(v___x_589_, 4, v___x_584_);
return v___x_589_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_590_ = lean_box(1);
v___x_591_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_592_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_593_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
lean_ctor_set(v___x_593_, 1, v___x_591_);
lean_ctor_set(v___x_593_, 2, v___x_590_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
lean_object* v___x_598_; lean_object* v_toCold_599_; lean_object* v_env_600_; lean_object* v_options_601_; uint8_t v___x_602_; lean_object* v_env_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_598_ = lean_st_ref_get(v___y_596_);
v_toCold_599_ = lean_ctor_get(v___y_595_, 0);
v_env_600_ = lean_ctor_get(v___x_598_, 0);
lean_inc_ref(v_env_600_);
lean_dec(v___x_598_);
v_options_601_ = lean_ctor_get(v_toCold_599_, 2);
v___x_602_ = 0;
v_env_603_ = l_Lean_Environment_setRecordingDeps(v_env_600_, v___x_602_);
v___x_604_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_605_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__4);
lean_inc_ref(v_options_601_);
v___x_606_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_606_, 0, v_env_603_);
lean_ctor_set(v___x_606_, 1, v___x_604_);
lean_ctor_set(v___x_606_, 2, v___x_605_);
lean_ctor_set(v___x_606_, 3, v_options_601_);
v___x_607_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
lean_ctor_set(v___x_607_, 1, v_msgData_594_);
v___x_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0(v_msgData_609_, v___y_610_, v___y_611_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v_ref_618_; lean_object* v___x_619_; lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_628_; 
v_ref_618_ = lean_ctor_get(v___y_615_, 2);
v___x_619_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0(v_msg_614_, v___y_615_, v___y_616_);
v_a_620_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_628_ == 0)
{
v___x_622_ = v___x_619_;
v_isShared_623_ = v_isSharedCheck_628_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_619_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_628_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_624_; lean_object* v___x_626_; 
lean_inc(v_ref_618_);
v___x_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_624_, 0, v_ref_618_);
lean_ctor_set(v___x_624_, 1, v_a_620_);
if (v_isShared_623_ == 0)
{
lean_ctor_set_tag(v___x_622_, 1);
lean_ctor_set(v___x_622_, 0, v___x_624_);
v___x_626_ = v___x_622_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_624_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0___redArg(v_msg_629_, v___y_630_, v___y_631_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
return v_res_633_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0___closed__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___x_636_ = l_Lean_stringToMessageData(v___x_635_);
return v___x_636_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0___closed__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___x_639_ = l_Lean_stringToMessageData(v___x_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(lean_object* v_name_640_, lean_object* v_decl_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_645_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_);
v___x_646_ = l_Lean_MessageData_ofName(v_name_640_);
v___x_647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_645_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
v___x_648_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_);
v___x_649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_647_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0___redArg(v___x_649_, v___y_642_, v___y_643_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2____boxed(lean_object* v_name_651_, lean_object* v_decl_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(v_name_651_, v_decl_652_, v___y_653_, v___y_654_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v_decl_652_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__13___redArg(lean_object* v_ref_657_, lean_object* v_msg_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v_toCold_662_; lean_object* v_currRecDepth_663_; lean_object* v_ref_664_; uint16_t v_optionFlags_665_; uint8_t v_suppressElabErrors_666_; uint8_t v_isRecordingDeps_667_; lean_object* v_ref_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v_toCold_662_ = lean_ctor_get(v___y_659_, 0);
v_currRecDepth_663_ = lean_ctor_get(v___y_659_, 1);
v_ref_664_ = lean_ctor_get(v___y_659_, 2);
v_optionFlags_665_ = lean_ctor_get_uint16(v___y_659_, sizeof(void*)*3);
v_suppressElabErrors_666_ = lean_ctor_get_uint8(v___y_659_, sizeof(void*)*3 + 2);
v_isRecordingDeps_667_ = lean_ctor_get_uint8(v___y_659_, sizeof(void*)*3 + 3);
v_ref_668_ = l_Lean_replaceRef(v_ref_657_, v_ref_664_);
lean_inc(v_currRecDepth_663_);
lean_inc_ref(v_toCold_662_);
v___x_669_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_669_, 0, v_toCold_662_);
lean_ctor_set(v___x_669_, 1, v_currRecDepth_663_);
lean_ctor_set(v___x_669_, 2, v_ref_668_);
lean_ctor_set_uint16(v___x_669_, sizeof(void*)*3, v_optionFlags_665_);
lean_ctor_set_uint8(v___x_669_, sizeof(void*)*3 + 2, v_suppressElabErrors_666_);
lean_ctor_set_uint8(v___x_669_, sizeof(void*)*3 + 3, v_isRecordingDeps_667_);
v___x_670_ = l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0___redArg(v_msg_658_, v___x_669_, v___y_660_);
lean_dec_ref_known(v___x_669_, 3);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__13___redArg___boxed(lean_object* v_ref_671_, lean_object* v_msg_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__13___redArg(v_ref_671_, v_msg_672_, v___y_673_, v___y_674_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v_ref_671_);
return v_res_676_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__0));
v___x_679_ = l_Lean_stringToMessageData(v___x_678_);
return v___x_679_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__2));
v___x_682_ = l_Lean_stringToMessageData(v___x_681_);
return v___x_682_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__5(void){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__4));
v___x_685_ = l_Lean_stringToMessageData(v___x_684_);
return v___x_685_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__7(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__6));
v___x_688_ = l_Lean_stringToMessageData(v___x_687_);
return v___x_688_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__9(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__8));
v___x_691_ = l_Lean_stringToMessageData(v___x_690_);
return v___x_691_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__11(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__10));
v___x_694_ = l_Lean_stringToMessageData(v___x_693_);
return v___x_694_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__13(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__12));
v___x_697_ = l_Lean_stringToMessageData(v___x_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg(lean_object* v_msg_698_, lean_object* v_declHint_699_, lean_object* v___y_700_){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v_env_704_; uint8_t v___x_705_; 
v___x_702_ = lean_box(0);
v___x_703_ = lean_st_ref_get(v___y_700_);
v_env_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc_ref(v_env_704_);
lean_dec(v___x_703_);
v___x_705_ = l_Lean_Name_isAnonymous(v_declHint_699_);
if (v___x_705_ == 0)
{
uint8_t v_isExporting_706_; 
v_isExporting_706_ = lean_ctor_get_uint8(v_env_704_, sizeof(void*)*13);
if (v_isExporting_706_ == 0)
{
lean_object* v___x_707_; 
lean_dec_ref(v_env_704_);
lean_dec(v_declHint_699_);
v___x_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_707_, 0, v_msg_698_);
return v___x_707_;
}
else
{
lean_object* v___x_708_; uint8_t v___x_709_; 
lean_inc_ref(v_env_704_);
v___x_708_ = l_Lean_Environment_setExporting(v_env_704_, v___x_705_);
lean_inc(v_declHint_699_);
lean_inc_ref(v___x_708_);
v___x_709_ = l_Lean_Environment_contains(v___x_708_, v_declHint_699_, v_isExporting_706_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; 
lean_dec_ref(v___x_708_);
lean_dec_ref(v_env_704_);
lean_dec(v_declHint_699_);
v___x_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_710_, 0, v_msg_698_);
return v___x_710_;
}
else
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v_c_716_; lean_object* v___x_717_; 
v___x_711_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_712_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_713_ = l_Lean_Options_empty;
v___x_714_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_714_, 0, v___x_708_);
lean_ctor_set(v___x_714_, 1, v___x_711_);
lean_ctor_set(v___x_714_, 2, v___x_712_);
lean_ctor_set(v___x_714_, 3, v___x_713_);
lean_inc(v_declHint_699_);
v___x_715_ = l_Lean_MessageData_ofConstName(v_declHint_699_, v___x_705_);
v_c_716_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_716_, 0, v___x_714_);
lean_ctor_set(v_c_716_, 1, v___x_715_);
v___x_717_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_704_, v_declHint_699_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
lean_dec_ref(v_env_704_);
lean_dec(v_declHint_699_);
v___x_718_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__1);
v___x_719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
lean_ctor_set(v___x_719_, 1, v_c_716_);
v___x_720_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__3);
v___x_721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_719_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
v___x_722_ = l_Lean_MessageData_note(v___x_721_);
v___x_723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_723_, 0, v_msg_698_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
v___x_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
return v___x_724_;
}
else
{
lean_object* v_val_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_759_; 
v_val_725_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_759_ == 0)
{
v___x_727_ = v___x_717_;
v_isShared_728_ = v_isSharedCheck_759_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_val_725_);
lean_dec(v___x_717_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_759_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v_moduleNames_730_; lean_object* v_mod_731_; uint8_t v___x_732_; 
v___x_729_ = l_Lean_Environment_header(v_env_704_);
lean_dec_ref(v_env_704_);
v_moduleNames_730_ = lean_ctor_get(v___x_729_, 4);
lean_inc_ref(v_moduleNames_730_);
lean_dec_ref(v___x_729_);
v_mod_731_ = lean_array_get(v___x_702_, v_moduleNames_730_, v_val_725_);
lean_dec(v_val_725_);
lean_dec_ref(v_moduleNames_730_);
v___x_732_ = l_Lean_isPrivateName(v_declHint_699_);
lean_dec(v_declHint_699_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_744_; 
v___x_733_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__5);
v___x_734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
lean_ctor_set(v___x_734_, 1, v_c_716_);
v___x_735_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__7);
v___x_736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_734_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = l_Lean_MessageData_ofName(v_mod_731_);
v___x_738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_736_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
v___x_739_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__9);
v___x_740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_738_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v___x_741_ = l_Lean_MessageData_note(v___x_740_);
v___x_742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_742_, 0, v_msg_698_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
if (v_isShared_728_ == 0)
{
lean_ctor_set_tag(v___x_727_, 0);
lean_ctor_set(v___x_727_, 0, v___x_742_);
v___x_744_ = v___x_727_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_742_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
else
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_746_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__1);
v___x_747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
lean_ctor_set(v___x_747_, 1, v_c_716_);
v___x_748_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__11);
v___x_749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_747_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = l_Lean_MessageData_ofName(v_mod_731_);
v___x_751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_749_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
v___x_752_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__13);
v___x_753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_751_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = l_Lean_MessageData_note(v___x_753_);
v___x_755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_755_, 0, v_msg_698_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
if (v_isShared_728_ == 0)
{
lean_ctor_set_tag(v___x_727_, 0);
lean_ctor_set(v___x_727_, 0, v___x_755_);
v___x_757_ = v___x_727_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_755_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_760_; 
lean_dec_ref(v_env_704_);
lean_dec(v_declHint_699_);
v___x_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_760_, 0, v_msg_698_);
return v___x_760_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___boxed(lean_object* v_msg_761_, lean_object* v_declHint_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg(v_msg_761_, v_declHint_762_, v___y_763_);
lean_dec(v___y_763_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12(lean_object* v_msg_766_, lean_object* v_declHint_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v___x_771_; lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_781_; 
v___x_771_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg(v_msg_766_, v_declHint_767_, v___y_769_);
v_a_772_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_781_ == 0)
{
v___x_774_ = v___x_771_;
v_isShared_775_ = v_isSharedCheck_781_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_771_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_781_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_779_; 
v___x_776_ = l_Lean_unknownIdentifierMessageTag;
v___x_777_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
lean_ctor_set(v___x_777_, 1, v_a_772_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v___x_777_);
v___x_779_ = v___x_774_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_777_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12___boxed(lean_object* v_msg_782_, lean_object* v_declHint_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12(v_msg_782_, v_declHint_783_, v___y_784_, v___y_785_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8___redArg(lean_object* v_ref_788_, lean_object* v_msg_789_, lean_object* v_declHint_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v___x_794_; lean_object* v_a_795_; lean_object* v___x_796_; 
v___x_794_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12(v_msg_789_, v_declHint_790_, v___y_791_, v___y_792_);
v_a_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_a_795_);
lean_dec_ref(v___x_794_);
v___x_796_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__13___redArg(v_ref_788_, v_a_795_, v___y_791_, v___y_792_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_ref_797_, lean_object* v_msg_798_, lean_object* v_declHint_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8___redArg(v_ref_797_, v_msg_798_, v_declHint_799_, v___y_800_, v___y_801_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v_ref_797_);
return v_res_803_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__2));
v___x_805_ = l_Lean_stringToMessageData(v___x_804_);
return v___x_805_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__3));
v___x_807_ = l_Lean_stringToMessageData(v___x_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(lean_object* v_ref_808_, lean_object* v_constName_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v___x_813_; uint8_t v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_813_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__0, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__0);
v___x_814_ = 0;
lean_inc(v_constName_809_);
v___x_815_ = l_Lean_MessageData_ofConstName(v_constName_809_, v___x_814_);
v___x_816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_813_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1);
v___x_818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_816_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8___redArg(v_ref_808_, v___x_818_, v_constName_809_, v___y_810_, v___y_811_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_820_, lean_object* v_constName_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_ref_820_, v_constName_821_, v___y_822_, v___y_823_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec(v_ref_820_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_constName_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_ref_830_; lean_object* v___x_831_; 
v_ref_830_ = lean_ctor_get(v___y_827_, 2);
v___x_831_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_ref_830_, v_constName_826_, v___y_827_, v___y_828_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_constName_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2___redArg(v_constName_832_, v___y_833_, v___y_834_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1(lean_object* v_constName_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v___x_841_; lean_object* v_env_842_; uint8_t v___x_843_; lean_object* v___x_844_; 
v___x_841_ = lean_st_ref_get(v___y_839_);
v_env_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc_ref(v_env_842_);
lean_dec(v___x_841_);
v___x_843_ = 0;
lean_inc(v_constName_837_);
v___x_844_ = l_Lean_Environment_find_x3f(v_env_842_, v_constName_837_, v___x_843_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2___redArg(v_constName_837_, v___y_838_, v___y_839_);
return v___x_845_;
}
else
{
lean_object* v_val_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
lean_dec(v_constName_837_);
v_val_846_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v___x_844_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_val_846_);
lean_dec(v___x_844_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
lean_ctor_set_tag(v___x_848_, 0);
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_val_846_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1___boxed(lean_object* v_constName_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1(v_constName_854_, v___y_855_, v___y_856_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
return v_res_858_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__0));
v___x_861_ = l_Lean_stringToMessageData(v___x_860_);
return v___x_861_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__2));
v___x_864_ = l_Lean_stringToMessageData(v___x_863_);
return v___x_864_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__4));
v___x_867_ = l_Lean_stringToMessageData(v___x_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg(lean_object* v_attrName_868_, lean_object* v_declName_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; uint8_t v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_873_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__1);
v___x_874_ = l_Lean_MessageData_ofName(v_attrName_868_);
v___x_875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_873_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
v___x_876_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__3);
v___x_877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_875_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = 0;
v___x_879_ = l_Lean_MessageData_ofConstName(v_declName_869_, v___x_878_);
v___x_880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_877_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__5);
v___x_882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_880_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
v___x_883_ = l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0___redArg(v___x_882_, v___y_870_, v___y_871_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object* v_attrName_884_, lean_object* v_declName_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg(v_attrName_884_, v_declName_885_, v___y_886_, v___y_887_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
return v_res_889_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__0));
v___x_892_ = l_Lean_stringToMessageData(v___x_891_);
return v___x_892_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__2));
v___x_895_ = l_Lean_stringToMessageData(v___x_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg(lean_object* v_name_899_, uint8_t v_kind_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___y_910_; 
v___x_904_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__1);
v___x_905_ = l_Lean_MessageData_ofName(v_name_899_);
v___x_906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__3);
v___x_908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_906_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
switch(v_kind_900_)
{
case 0:
{
lean_object* v___x_917_; 
v___x_917_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__4));
v___y_910_ = v___x_917_;
goto v___jp_909_;
}
case 1:
{
lean_object* v___x_918_; 
v___x_918_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__5));
v___y_910_ = v___x_918_;
goto v___jp_909_;
}
default: 
{
lean_object* v___x_919_; 
v___x_919_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__6));
v___y_910_ = v___x_919_;
goto v___jp_909_;
}
}
v___jp_909_:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
lean_inc_ref(v___y_910_);
v___x_911_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_911_, 0, v___y_910_);
v___x_912_ = l_Lean_MessageData_ofFormat(v___x_911_);
v___x_913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_908_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1);
v___x_915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_913_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0___redArg(v___x_915_, v___y_901_, v___y_902_);
return v___x_916_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___boxed(lean_object* v_name_920_, lean_object* v_kind_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
uint8_t v_kind_boxed_925_; lean_object* v_res_926_; 
v_kind_boxed_925_ = lean_unbox(v_kind_921_);
v_res_926_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg(v_name_920_, v_kind_boxed_925_, v___y_922_, v___y_923_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___lam__0(lean_object* v___x_927_, lean_object* v_entry_928_, lean_object* v_s_929_){
_start:
{
lean_object* v_addEntryFn_930_; lean_object* v_importedEntries_931_; lean_object* v_state_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_940_; 
v_addEntryFn_930_ = lean_ctor_get(v___x_927_, 3);
lean_inc(v_addEntryFn_930_);
lean_dec_ref(v___x_927_);
v_importedEntries_931_ = lean_ctor_get(v_s_929_, 0);
v_state_932_ = lean_ctor_get(v_s_929_, 1);
v_isSharedCheck_940_ = !lean_is_exclusive(v_s_929_);
if (v_isSharedCheck_940_ == 0)
{
v___x_934_ = v_s_929_;
v_isShared_935_ = v_isSharedCheck_940_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_state_932_);
lean_inc(v_importedEntries_931_);
lean_dec(v_s_929_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_940_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v_state_936_; lean_object* v___x_938_; 
v_state_936_ = lean_apply_2(v_addEntryFn_930_, v_state_932_, v_entry_928_);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 1, v_state_936_);
v___x_938_ = v___x_934_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_importedEntries_931_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v_state_936_);
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16___redArg(lean_object* v_keys_941_, lean_object* v_i_942_, lean_object* v_k_943_){
_start:
{
lean_object* v___x_944_; uint8_t v___x_945_; 
v___x_944_ = lean_array_get_size(v_keys_941_);
v___x_945_ = lean_nat_dec_lt(v_i_942_, v___x_944_);
if (v___x_945_ == 0)
{
lean_dec(v_i_942_);
return v___x_945_;
}
else
{
lean_object* v_k_x27_946_; uint8_t v___x_947_; 
v_k_x27_946_ = lean_array_fget_borrowed(v_keys_941_, v_i_942_);
v___x_947_ = l_Lean_instBEqExtraModUse_beq(v_k_943_, v_k_x27_946_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = lean_unsigned_to_nat(1u);
v___x_949_ = lean_nat_add(v_i_942_, v___x_948_);
lean_dec(v_i_942_);
v_i_942_ = v___x_949_;
goto _start;
}
else
{
lean_dec(v_i_942_);
return v___x_945_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16___redArg___boxed(lean_object* v_keys_951_, lean_object* v_i_952_, lean_object* v_k_953_){
_start:
{
uint8_t v_res_954_; lean_object* v_r_955_; 
v_res_954_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16___redArg(v_keys_951_, v_i_952_, v_k_953_);
lean_dec_ref(v_k_953_);
lean_dec_ref(v_keys_951_);
v_r_955_ = lean_box(v_res_954_);
return v_r_955_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg(lean_object* v_x_956_, size_t v_x_957_, lean_object* v_x_958_){
_start:
{
if (lean_obj_tag(v_x_956_) == 0)
{
lean_object* v_es_959_; lean_object* v___x_960_; size_t v___x_961_; size_t v___x_962_; lean_object* v_j_963_; lean_object* v___x_964_; 
v_es_959_ = lean_ctor_get(v_x_956_, 0);
v___x_960_ = lean_box(2);
v___x_961_ = ((size_t)31ULL);
v___x_962_ = lean_usize_land(v_x_957_, v___x_961_);
v_j_963_ = lean_usize_to_nat(v___x_962_);
v___x_964_ = lean_array_get_borrowed(v___x_960_, v_es_959_, v_j_963_);
lean_dec(v_j_963_);
switch(lean_obj_tag(v___x_964_))
{
case 0:
{
lean_object* v_key_965_; uint8_t v___x_966_; 
v_key_965_ = lean_ctor_get(v___x_964_, 0);
v___x_966_ = l_Lean_instBEqExtraModUse_beq(v_x_958_, v_key_965_);
return v___x_966_;
}
case 1:
{
lean_object* v_node_967_; size_t v___x_968_; size_t v___x_969_; 
v_node_967_ = lean_ctor_get(v___x_964_, 0);
v___x_968_ = ((size_t)5ULL);
v___x_969_ = lean_usize_shift_right(v_x_957_, v___x_968_);
v_x_956_ = v_node_967_;
v_x_957_ = v___x_969_;
goto _start;
}
default: 
{
uint8_t v___x_971_; 
v___x_971_ = 0;
return v___x_971_;
}
}
}
else
{
lean_object* v_ks_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
v_ks_972_ = lean_ctor_get(v_x_956_, 0);
v___x_973_ = lean_unsigned_to_nat(0u);
v___x_974_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16___redArg(v_ks_972_, v___x_973_, v_x_958_);
return v___x_974_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg___boxed(lean_object* v_x_975_, lean_object* v_x_976_, lean_object* v_x_977_){
_start:
{
size_t v_x_9132__boxed_978_; uint8_t v_res_979_; lean_object* v_r_980_; 
v_x_9132__boxed_978_ = lean_unbox_usize(v_x_976_);
lean_dec(v_x_976_);
v_res_979_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg(v_x_975_, v_x_9132__boxed_978_, v_x_977_);
lean_dec_ref(v_x_977_);
lean_dec_ref(v_x_975_);
v_r_980_ = lean_box(v_res_979_);
return v_r_980_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(lean_object* v_x_981_, lean_object* v_x_982_){
_start:
{
uint64_t v___x_983_; size_t v___x_984_; uint8_t v___x_985_; 
v___x_983_ = l_Lean_instHashableExtraModUse_hash(v_x_982_);
v___x_984_ = lean_uint64_to_usize(v___x_983_);
v___x_985_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg(v_x_981_, v___x_984_, v_x_982_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_x_986_, lean_object* v_x_987_){
_start:
{
uint8_t v_res_988_; lean_object* v_r_989_; 
v_res_988_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(v_x_986_, v_x_987_);
lean_dec_ref(v_x_987_);
lean_dec_ref(v_x_986_);
v_r_989_ = lean_box(v_res_988_);
return v_r_989_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__0(void){
_start:
{
lean_object* v___x_990_; double v___x_991_; 
v___x_990_ = lean_unsigned_to_nat(0u);
v___x_991_ = lean_float_of_nat(v___x_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8(lean_object* v_cls_995_, lean_object* v_msg_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v_ref_1000_; lean_object* v___x_1001_; lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1047_; 
v_ref_1000_ = lean_ctor_get(v___y_997_, 2);
v___x_1001_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0(v_msg_996_, v___y_997_, v___y_998_);
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1004_ = v___x_1001_;
v_isShared_1005_ = v_isSharedCheck_1047_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_1001_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1047_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1006_; lean_object* v_traceState_1007_; lean_object* v_env_1008_; lean_object* v_nextMacroScope_1009_; lean_object* v_ngen_1010_; lean_object* v_auxDeclNGen_1011_; lean_object* v_cache_1012_; lean_object* v_recordedDeps_1013_; lean_object* v_messages_1014_; lean_object* v_infoState_1015_; lean_object* v_snapshotTasks_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1046_; 
v___x_1006_ = lean_st_ref_take(v___y_998_);
v_traceState_1007_ = lean_ctor_get(v___x_1006_, 4);
v_env_1008_ = lean_ctor_get(v___x_1006_, 0);
v_nextMacroScope_1009_ = lean_ctor_get(v___x_1006_, 1);
v_ngen_1010_ = lean_ctor_get(v___x_1006_, 2);
v_auxDeclNGen_1011_ = lean_ctor_get(v___x_1006_, 3);
v_cache_1012_ = lean_ctor_get(v___x_1006_, 5);
v_recordedDeps_1013_ = lean_ctor_get(v___x_1006_, 6);
v_messages_1014_ = lean_ctor_get(v___x_1006_, 7);
v_infoState_1015_ = lean_ctor_get(v___x_1006_, 8);
v_snapshotTasks_1016_ = lean_ctor_get(v___x_1006_, 9);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1018_ = v___x_1006_;
v_isShared_1019_ = v_isSharedCheck_1046_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_snapshotTasks_1016_);
lean_inc(v_infoState_1015_);
lean_inc(v_messages_1014_);
lean_inc(v_recordedDeps_1013_);
lean_inc(v_cache_1012_);
lean_inc(v_traceState_1007_);
lean_inc(v_auxDeclNGen_1011_);
lean_inc(v_ngen_1010_);
lean_inc(v_nextMacroScope_1009_);
lean_inc(v_env_1008_);
lean_dec(v___x_1006_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1046_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
uint64_t v_tid_1020_; lean_object* v_traces_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1045_; 
v_tid_1020_ = lean_ctor_get_uint64(v_traceState_1007_, sizeof(void*)*1);
v_traces_1021_ = lean_ctor_get(v_traceState_1007_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v_traceState_1007_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1023_ = v_traceState_1007_;
v_isShared_1024_ = v_isSharedCheck_1045_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_traces_1021_);
lean_dec(v_traceState_1007_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1045_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; double v___x_1027_; uint8_t v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1036_; 
v___x_1025_ = lean_box(0);
v___x_1026_ = lean_box(0);
v___x_1027_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__0);
v___x_1028_ = 0;
v___x_1029_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__1));
v___x_1030_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1030_, 0, v_cls_995_);
lean_ctor_set(v___x_1030_, 1, v___x_1026_);
lean_ctor_set(v___x_1030_, 2, v___x_1029_);
lean_ctor_set_float(v___x_1030_, sizeof(void*)*3, v___x_1027_);
lean_ctor_set_float(v___x_1030_, sizeof(void*)*3 + 8, v___x_1027_);
lean_ctor_set_uint8(v___x_1030_, sizeof(void*)*3 + 16, v___x_1028_);
v___x_1031_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__2));
v___x_1032_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1030_);
lean_ctor_set(v___x_1032_, 1, v_a_1002_);
lean_ctor_set(v___x_1032_, 2, v___x_1031_);
lean_inc(v_ref_1000_);
v___x_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1033_, 0, v_ref_1000_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = l_Lean_PersistentArray_push___redArg(v_traces_1021_, v___x_1033_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1034_);
v___x_1036_ = v___x_1023_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1034_);
lean_ctor_set_uint64(v_reuseFailAlloc_1044_, sizeof(void*)*1, v_tid_1020_);
v___x_1036_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
lean_object* v___x_1038_; 
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 4, v___x_1036_);
v___x_1038_ = v___x_1018_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_env_1008_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_nextMacroScope_1009_);
lean_ctor_set(v_reuseFailAlloc_1043_, 2, v_ngen_1010_);
lean_ctor_set(v_reuseFailAlloc_1043_, 3, v_auxDeclNGen_1011_);
lean_ctor_set(v_reuseFailAlloc_1043_, 4, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1043_, 5, v_cache_1012_);
lean_ctor_set(v_reuseFailAlloc_1043_, 6, v_recordedDeps_1013_);
lean_ctor_set(v_reuseFailAlloc_1043_, 7, v_messages_1014_);
lean_ctor_set(v_reuseFailAlloc_1043_, 8, v_infoState_1015_);
lean_ctor_set(v_reuseFailAlloc_1043_, 9, v_snapshotTasks_1016_);
v___x_1038_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1039_ = lean_st_ref_put(v___y_998_, v___x_1038_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v___x_1025_);
v___x_1041_ = v___x_1004_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1025_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___boxed(lean_object* v_cls_1048_, lean_object* v_msg_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8(v_cls_1048_, v_msg_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
return v_res_1053_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1054_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__4(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__3));
v___x_1060_ = l_Lean_stringToMessageData(v___x_1059_);
return v___x_1060_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__6(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__5));
v___x_1063_ = l_Lean_stringToMessageData(v___x_1062_);
return v___x_1063_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__7(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__1));
v___x_1065_ = l_Lean_stringToMessageData(v___x_1064_);
return v___x_1065_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__10(void){
_start:
{
lean_object* v_cls_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v_cls_1069_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__2));
v___x_1070_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__9));
v___x_1071_ = l_Lean_Name_append(v___x_1070_, v_cls_1069_);
return v___x_1071_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__12(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__11));
v___x_1074_ = l_Lean_stringToMessageData(v___x_1073_);
return v___x_1074_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__14(void){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__13));
v___x_1077_ = l_Lean_stringToMessageData(v___x_1076_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5(lean_object* v_mod_1082_, uint8_t v_isMeta_1083_, lean_object* v_hint_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v_env_1106_; uint8_t v_isExporting_1107_; lean_object* v_entry_1108_; lean_object* v___x_1109_; lean_object* v_env_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; 
v___x_1104_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__0);
v___x_1105_ = lean_st_ref_get(v___y_1086_);
v_env_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc_ref(v_env_1106_);
lean_dec(v___x_1105_);
v_isExporting_1107_ = lean_ctor_get_uint8(v_env_1106_, sizeof(void*)*13);
lean_dec_ref(v_env_1106_);
lean_inc(v_mod_1082_);
v_entry_1108_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1108_, 0, v_mod_1082_);
lean_ctor_set_uint8(v_entry_1108_, sizeof(void*)*1, v_isExporting_1107_);
lean_ctor_set_uint8(v_entry_1108_, sizeof(void*)*1 + 1, v_isMeta_1083_);
v___x_1109_ = lean_st_ref_get(v___y_1086_);
v_env_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc_ref(v_env_1110_);
lean_dec(v___x_1109_);
v___x_1111_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1112_ = lean_box(1);
v___x_1113_ = lean_box(0);
v___x_1114_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1104_, v___x_1111_, v_env_1110_, v___x_1112_, v___x_1113_);
v___x_1115_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(v___x_1114_, v_entry_1108_);
lean_dec(v___x_1114_);
if (v___x_1115_ == 0)
{
lean_object* v_toCold_1116_; lean_object* v_options_1117_; lean_object* v_inheritedTraceOptions_1118_; uint8_t v_hasTrace_1119_; lean_object* v___f_1120_; uint8_t v___x_1121_; lean_object* v___y_1123_; 
v_toCold_1116_ = lean_ctor_get(v___y_1085_, 0);
v_options_1117_ = lean_ctor_get(v_toCold_1116_, 2);
v_inheritedTraceOptions_1118_ = lean_ctor_get(v_toCold_1116_, 11);
v_hasTrace_1119_ = lean_ctor_get_uint8(v_options_1117_, sizeof(void*)*1);
v___f_1120_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___lam__0), 3, 2);
lean_closure_set(v___f_1120_, 0, v___x_1111_);
lean_closure_set(v___f_1120_, 1, v_entry_1108_);
v___x_1121_ = 1;
if (v_hasTrace_1119_ == 0)
{
lean_dec(v_hint_1084_);
lean_dec(v_mod_1082_);
v___y_1123_ = v___y_1086_;
goto v___jp_1122_;
}
else
{
lean_object* v_cls_1141_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___x_1161_; uint8_t v___x_1162_; 
v_cls_1141_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__2));
v___x_1161_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__10);
v___x_1162_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1118_, v_options_1117_, v___x_1161_);
if (v___x_1162_ == 0)
{
lean_dec(v_hint_1084_);
lean_dec(v_mod_1082_);
v___y_1123_ = v___y_1086_;
goto v___jp_1122_;
}
else
{
lean_object* v___x_1163_; lean_object* v___y_1165_; 
v___x_1163_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__12);
if (v_isExporting_1107_ == 0)
{
lean_object* v___x_1172_; 
v___x_1172_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__17));
v___y_1165_ = v___x_1172_;
goto v___jp_1164_;
}
else
{
lean_object* v___x_1173_; 
v___x_1173_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__18));
v___y_1165_ = v___x_1173_;
goto v___jp_1164_;
}
v___jp_1164_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
lean_inc_ref(v___y_1165_);
v___x_1166_ = l_Lean_stringToMessageData(v___y_1165_);
v___x_1167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1163_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
v___x_1168_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__14);
v___x_1169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1167_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
if (v_isMeta_1083_ == 0)
{
lean_object* v___x_1170_; 
v___x_1170_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__15));
v___y_1148_ = v___x_1169_;
v___y_1149_ = v___x_1170_;
goto v___jp_1147_;
}
else
{
lean_object* v___x_1171_; 
v___x_1171_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__16));
v___y_1148_ = v___x_1169_;
v___y_1149_ = v___x_1171_;
goto v___jp_1147_;
}
}
}
v___jp_1142_:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___y_1143_);
lean_ctor_set(v___x_1145_, 1, v___y_1144_);
v___x_1146_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8(v_cls_1141_, v___x_1145_, v___y_1085_, v___y_1086_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_dec_ref_known(v___x_1146_, 1);
v___y_1123_ = v___y_1086_;
goto v___jp_1122_;
}
else
{
lean_dec_ref(v___f_1120_);
return v___x_1146_;
}
}
v___jp_1147_:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; uint8_t v___x_1156_; 
lean_inc_ref(v___y_1149_);
v___x_1150_ = l_Lean_stringToMessageData(v___y_1149_);
v___x_1151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___y_1148_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__4);
v___x_1153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1151_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
v___x_1154_ = l_Lean_MessageData_ofName(v_mod_1082_);
v___x_1155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = l_Lean_Name_isAnonymous(v_hint_1084_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1157_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__6);
v___x_1158_ = l_Lean_MessageData_ofName(v_hint_1084_);
v___x_1159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1157_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___y_1143_ = v___x_1155_;
v___y_1144_ = v___x_1159_;
goto v___jp_1142_;
}
else
{
lean_object* v___x_1160_; 
lean_dec(v_hint_1084_);
v___x_1160_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__7);
v___y_1143_ = v___x_1155_;
v___y_1144_ = v___x_1160_;
goto v___jp_1142_;
}
}
}
v___jp_1122_:
{
lean_object* v___x_1124_; lean_object* v_toEnvExtension_1125_; lean_object* v_env_1126_; lean_object* v_nextMacroScope_1127_; lean_object* v_ngen_1128_; lean_object* v_auxDeclNGen_1129_; lean_object* v_traceState_1130_; lean_object* v_recordedDeps_1131_; lean_object* v_messages_1132_; lean_object* v_infoState_1133_; lean_object* v_snapshotTasks_1134_; lean_object* v_asyncMode_1135_; uint8_t v_logWrites_1136_; lean_object* v___x_1137_; 
v___x_1124_ = lean_st_ref_take(v___y_1123_);
v_toEnvExtension_1125_ = lean_ctor_get(v___x_1111_, 0);
v_env_1126_ = lean_ctor_get(v___x_1124_, 0);
lean_inc_ref(v_env_1126_);
v_nextMacroScope_1127_ = lean_ctor_get(v___x_1124_, 1);
lean_inc(v_nextMacroScope_1127_);
v_ngen_1128_ = lean_ctor_get(v___x_1124_, 2);
lean_inc_ref(v_ngen_1128_);
v_auxDeclNGen_1129_ = lean_ctor_get(v___x_1124_, 3);
lean_inc_ref(v_auxDeclNGen_1129_);
v_traceState_1130_ = lean_ctor_get(v___x_1124_, 4);
lean_inc_ref(v_traceState_1130_);
v_recordedDeps_1131_ = lean_ctor_get(v___x_1124_, 6);
lean_inc_ref(v_recordedDeps_1131_);
v_messages_1132_ = lean_ctor_get(v___x_1124_, 7);
lean_inc_ref(v_messages_1132_);
v_infoState_1133_ = lean_ctor_get(v___x_1124_, 8);
lean_inc_ref(v_infoState_1133_);
v_snapshotTasks_1134_ = lean_ctor_get(v___x_1124_, 9);
lean_inc_ref(v_snapshotTasks_1134_);
lean_dec(v___x_1124_);
v_asyncMode_1135_ = lean_ctor_get(v_toEnvExtension_1125_, 2);
v_logWrites_1136_ = lean_ctor_get_uint8(v_toEnvExtension_1125_, sizeof(void*)*6);
v___x_1137_ = lean_box(0);
if (v_logWrites_1136_ == 0)
{
lean_object* v___x_1138_; 
lean_inc_ref(v_toEnvExtension_1125_);
v___x_1138_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1125_, v_env_1126_, v___f_1120_, v_asyncMode_1135_, v___x_1113_, v___x_1121_);
v___y_1089_ = v_auxDeclNGen_1129_;
v___y_1090_ = v___y_1123_;
v___y_1091_ = v_nextMacroScope_1127_;
v___y_1092_ = v_messages_1132_;
v___y_1093_ = v___x_1137_;
v___y_1094_ = v_ngen_1128_;
v___y_1095_ = v_recordedDeps_1131_;
v___y_1096_ = v_snapshotTasks_1134_;
v___y_1097_ = v_infoState_1133_;
v___y_1098_ = v_traceState_1130_;
v___y_1099_ = v___x_1138_;
goto v___jp_1088_;
}
else
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
lean_inc_ref_n(v_toEnvExtension_1125_, 2);
v___x_1139_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1125_, v_env_1126_);
lean_dec_ref(v_env_1126_);
v___x_1140_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1125_, v___x_1139_, v___f_1120_, v_asyncMode_1135_, v___x_1113_, v___x_1121_);
v___y_1089_ = v_auxDeclNGen_1129_;
v___y_1090_ = v___y_1123_;
v___y_1091_ = v_nextMacroScope_1127_;
v___y_1092_ = v_messages_1132_;
v___y_1093_ = v___x_1137_;
v___y_1094_ = v_ngen_1128_;
v___y_1095_ = v_recordedDeps_1131_;
v___y_1096_ = v_snapshotTasks_1134_;
v___y_1097_ = v_infoState_1133_;
v___y_1098_ = v_traceState_1130_;
v___y_1099_ = v___x_1140_;
goto v___jp_1088_;
}
}
}
else
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
lean_dec_ref_known(v_entry_1108_, 1);
lean_dec(v_hint_1084_);
lean_dec(v_mod_1082_);
v___x_1174_ = lean_box(0);
v___x_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
return v___x_1175_;
}
v___jp_1088_:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1100_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__2);
v___x_1101_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1101_, 0, v___y_1099_);
lean_ctor_set(v___x_1101_, 1, v___y_1091_);
lean_ctor_set(v___x_1101_, 2, v___y_1094_);
lean_ctor_set(v___x_1101_, 3, v___y_1089_);
lean_ctor_set(v___x_1101_, 4, v___y_1098_);
lean_ctor_set(v___x_1101_, 5, v___x_1100_);
lean_ctor_set(v___x_1101_, 6, v___y_1095_);
lean_ctor_set(v___x_1101_, 7, v___y_1092_);
lean_ctor_set(v___x_1101_, 8, v___y_1097_);
lean_ctor_set(v___x_1101_, 9, v___y_1096_);
v___x_1102_ = lean_st_ref_put(v___y_1090_, v___x_1101_);
v___x_1103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1103_, 0, v___y_1093_);
return v___x_1103_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object* v_mod_1176_, lean_object* v_isMeta_1177_, lean_object* v_hint_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
uint8_t v_isMeta_boxed_1182_; lean_object* v_res_1183_; 
v_isMeta_boxed_1182_ = lean_unbox(v_isMeta_1177_);
v_res_1183_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5(v_mod_1176_, v_isMeta_boxed_1182_, v_hint_1178_, v___y_1179_, v___y_1180_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__6(lean_object* v___x_1184_, lean_object* v_declName_1185_, lean_object* v_as_1186_, size_t v_sz_1187_, size_t v_i_1188_, lean_object* v_b_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
uint8_t v___x_1193_; 
v___x_1193_ = lean_usize_dec_lt(v_i_1188_, v_sz_1187_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; 
lean_dec(v_declName_1185_);
v___x_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1194_, 0, v_b_1189_);
return v___x_1194_;
}
else
{
lean_object* v___x_1195_; lean_object* v_modules_1196_; lean_object* v___x_1197_; lean_object* v_a_1198_; lean_object* v___x_1199_; lean_object* v_toImport_1200_; lean_object* v_module_1201_; lean_object* v___x_1202_; uint8_t v___x_1203_; lean_object* v___x_1204_; 
v___x_1195_ = l_Lean_Environment_header(v___x_1184_);
v_modules_1196_ = lean_ctor_get(v___x_1195_, 3);
lean_inc_ref(v_modules_1196_);
lean_dec_ref(v___x_1195_);
v___x_1197_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1198_ = lean_array_uget_borrowed(v_as_1186_, v_i_1188_);
v___x_1199_ = lean_array_get(v___x_1197_, v_modules_1196_, v_a_1198_);
lean_dec_ref(v_modules_1196_);
v_toImport_1200_ = lean_ctor_get(v___x_1199_, 0);
lean_inc_ref(v_toImport_1200_);
lean_dec(v___x_1199_);
v_module_1201_ = lean_ctor_get(v_toImport_1200_, 0);
lean_inc(v_module_1201_);
lean_dec_ref(v_toImport_1200_);
v___x_1202_ = lean_box(0);
v___x_1203_ = 0;
lean_inc(v_declName_1185_);
v___x_1204_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5(v_module_1201_, v___x_1203_, v_declName_1185_, v___y_1190_, v___y_1191_);
if (lean_obj_tag(v___x_1204_) == 0)
{
size_t v___x_1205_; size_t v___x_1206_; 
lean_dec_ref_known(v___x_1204_, 1);
v___x_1205_ = ((size_t)1ULL);
v___x_1206_ = lean_usize_add(v_i_1188_, v___x_1205_);
v_i_1188_ = v___x_1206_;
v_b_1189_ = v___x_1202_;
goto _start;
}
else
{
lean_dec(v_declName_1185_);
return v___x_1204_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__6___boxed(lean_object* v___x_1208_, lean_object* v_declName_1209_, lean_object* v_as_1210_, lean_object* v_sz_1211_, lean_object* v_i_1212_, lean_object* v_b_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
size_t v_sz_boxed_1217_; size_t v_i_boxed_1218_; lean_object* v_res_1219_; 
v_sz_boxed_1217_ = lean_unbox_usize(v_sz_1211_);
lean_dec(v_sz_1211_);
v_i_boxed_1218_ = lean_unbox_usize(v_i_1212_);
lean_dec(v_i_1212_);
v_res_1219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__6(v___x_1208_, v_declName_1209_, v_as_1210_, v_sz_boxed_1217_, v_i_boxed_1218_, v_b_1213_, v___y_1214_, v___y_1215_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec_ref(v_as_1210_);
lean_dec_ref(v___x_1208_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11___redArg(lean_object* v_a_1220_, lean_object* v_x_1221_){
_start:
{
if (lean_obj_tag(v_x_1221_) == 0)
{
lean_object* v___x_1222_; 
v___x_1222_ = lean_box(0);
return v___x_1222_;
}
else
{
lean_object* v_key_1223_; lean_object* v_value_1224_; lean_object* v_tail_1225_; uint8_t v___x_1226_; 
v_key_1223_ = lean_ctor_get(v_x_1221_, 0);
v_value_1224_ = lean_ctor_get(v_x_1221_, 1);
v_tail_1225_ = lean_ctor_get(v_x_1221_, 2);
v___x_1226_ = lean_name_eq(v_key_1223_, v_a_1220_);
if (v___x_1226_ == 0)
{
v_x_1221_ = v_tail_1225_;
goto _start;
}
else
{
lean_object* v___x_1228_; 
lean_inc(v_value_1224_);
v___x_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1228_, 0, v_value_1224_);
return v___x_1228_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11___redArg___boxed(lean_object* v_a_1229_, lean_object* v_x_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11___redArg(v_a_1229_, v_x_1230_);
lean_dec(v_x_1230_);
lean_dec(v_a_1229_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___redArg(lean_object* v_m_1232_, lean_object* v_a_1233_){
_start:
{
lean_object* v_buckets_1234_; lean_object* v___x_1235_; uint64_t v___y_1237_; 
v_buckets_1234_ = lean_ctor_get(v_m_1232_, 1);
v___x_1235_ = lean_array_get_size(v_buckets_1234_);
if (lean_obj_tag(v_a_1233_) == 0)
{
uint64_t v___x_1251_; 
v___x_1251_ = 1723ULL;
v___y_1237_ = v___x_1251_;
goto v___jp_1236_;
}
else
{
uint64_t v_hash_1252_; 
v_hash_1252_ = lean_ctor_get_uint64(v_a_1233_, sizeof(void*)*2);
v___y_1237_ = v_hash_1252_;
goto v___jp_1236_;
}
v___jp_1236_:
{
uint64_t v___x_1238_; uint64_t v___x_1239_; uint64_t v_fold_1240_; uint64_t v___x_1241_; uint64_t v___x_1242_; uint64_t v___x_1243_; size_t v___x_1244_; size_t v___x_1245_; size_t v___x_1246_; size_t v___x_1247_; size_t v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1238_ = 32ULL;
v___x_1239_ = lean_uint64_shift_right(v___y_1237_, v___x_1238_);
v_fold_1240_ = lean_uint64_xor(v___y_1237_, v___x_1239_);
v___x_1241_ = 16ULL;
v___x_1242_ = lean_uint64_shift_right(v_fold_1240_, v___x_1241_);
v___x_1243_ = lean_uint64_xor(v_fold_1240_, v___x_1242_);
v___x_1244_ = lean_uint64_to_usize(v___x_1243_);
v___x_1245_ = lean_usize_of_nat(v___x_1235_);
v___x_1246_ = ((size_t)1ULL);
v___x_1247_ = lean_usize_sub(v___x_1245_, v___x_1246_);
v___x_1248_ = lean_usize_land(v___x_1244_, v___x_1247_);
v___x_1249_ = lean_array_uget_borrowed(v_buckets_1234_, v___x_1248_);
v___x_1250_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11___redArg(v_a_1233_, v___x_1249_);
return v___x_1250_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___redArg___boxed(lean_object* v_m_1253_, lean_object* v_a_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___redArg(v_m_1253_, v_a_1254_);
lean_dec(v_a_1254_);
lean_dec_ref(v_m_1253_);
return v_res_1255_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__0(void){
_start:
{
lean_object* v___x_1256_; 
v___x_1256_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3(lean_object* v_declName_1259_, uint8_t v_isMeta_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v_env_1269_; lean_object* v___y_1271_; lean_object* v___x_1284_; 
v___x_1264_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__0);
v___x_1265_ = lean_st_ref_get(v___y_1262_);
v_env_1269_ = lean_ctor_get(v___x_1265_, 0);
lean_inc_ref(v_env_1269_);
lean_dec(v___x_1265_);
v___x_1284_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1269_, v_declName_1259_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_dec_ref(v_env_1269_);
lean_dec(v_declName_1259_);
goto v___jp_1266_;
}
else
{
lean_object* v_val_1285_; lean_object* v___x_1286_; lean_object* v_modules_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; 
v_val_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_val_1285_);
lean_dec_ref_known(v___x_1284_, 1);
v___x_1286_ = l_Lean_Environment_header(v_env_1269_);
v_modules_1287_ = lean_ctor_get(v___x_1286_, 3);
lean_inc_ref(v_modules_1287_);
lean_dec_ref(v___x_1286_);
v___x_1288_ = lean_array_get_size(v_modules_1287_);
v___x_1289_ = lean_nat_dec_lt(v_val_1285_, v___x_1288_);
if (v___x_1289_ == 0)
{
lean_dec_ref(v_modules_1287_);
lean_dec(v_val_1285_);
lean_dec_ref(v_env_1269_);
lean_dec(v_declName_1259_);
goto v___jp_1266_;
}
else
{
lean_object* v___x_1290_; lean_object* v___x_1291_; uint8_t v___y_1293_; 
v___x_1290_ = lean_array_fget(v_modules_1287_, v_val_1285_);
lean_dec(v_val_1285_);
lean_dec_ref(v_modules_1287_);
v___x_1291_ = lean_st_ref_get(v___y_1262_);
if (v_isMeta_1260_ == 0)
{
lean_dec(v___x_1291_);
v___y_1293_ = v_isMeta_1260_;
goto v___jp_1292_;
}
else
{
lean_object* v_env_1304_; uint8_t v___x_1305_; 
v_env_1304_ = lean_ctor_get(v___x_1291_, 0);
lean_inc_ref(v_env_1304_);
lean_dec(v___x_1291_);
lean_inc(v_declName_1259_);
v___x_1305_ = l_Lean_isMarkedMeta(v_env_1304_, v_declName_1259_);
if (v___x_1305_ == 0)
{
v___y_1293_ = v_isMeta_1260_;
goto v___jp_1292_;
}
else
{
uint8_t v___x_1306_; 
v___x_1306_ = 0;
v___y_1293_ = v___x_1306_;
goto v___jp_1292_;
}
}
v___jp_1292_:
{
lean_object* v_toImport_1294_; lean_object* v_module_1295_; lean_object* v___x_1296_; 
v_toImport_1294_ = lean_ctor_get(v___x_1290_, 0);
lean_inc_ref(v_toImport_1294_);
lean_dec(v___x_1290_);
v_module_1295_ = lean_ctor_get(v_toImport_1294_, 0);
lean_inc(v_module_1295_);
lean_dec_ref(v_toImport_1294_);
lean_inc(v_declName_1259_);
v___x_1296_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5(v_module_1295_, v___y_1293_, v_declName_1259_, v___y_1261_, v___y_1262_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
lean_dec_ref_known(v___x_1296_, 1);
v___x_1297_ = l_Lean_indirectModUseExt;
v___x_1298_ = lean_box(1);
v___x_1299_ = lean_box(0);
lean_inc_ref(v_env_1269_);
v___x_1300_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1264_, v___x_1297_, v_env_1269_, v___x_1298_, v___x_1299_);
v___x_1301_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___redArg(v___x_1300_, v_declName_1259_);
lean_dec(v___x_1300_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v___x_1302_; 
v___x_1302_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__1));
v___y_1271_ = v___x_1302_;
goto v___jp_1270_;
}
else
{
lean_object* v_val_1303_; 
v_val_1303_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_val_1303_);
lean_dec_ref_known(v___x_1301_, 1);
v___y_1271_ = v_val_1303_;
goto v___jp_1270_;
}
}
else
{
lean_dec_ref(v_env_1269_);
lean_dec(v_declName_1259_);
return v___x_1296_;
}
}
}
}
v___jp_1266_:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = lean_box(0);
v___x_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1267_);
return v___x_1268_;
}
v___jp_1270_:
{
lean_object* v___x_1272_; size_t v_sz_1273_; size_t v___x_1274_; lean_object* v___x_1275_; 
v___x_1272_ = lean_box(0);
v_sz_1273_ = lean_array_size(v___y_1271_);
v___x_1274_ = ((size_t)0ULL);
v___x_1275_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__6(v_env_1269_, v_declName_1259_, v___y_1271_, v_sz_1273_, v___x_1274_, v___x_1272_, v___y_1261_, v___y_1262_);
lean_dec_ref(v___y_1271_);
lean_dec_ref(v_env_1269_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1282_ == 0)
{
lean_object* v_unused_1283_; 
v_unused_1283_ = lean_ctor_get(v___x_1275_, 0);
lean_dec(v_unused_1283_);
v___x_1277_ = v___x_1275_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_dec(v___x_1275_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 0, v___x_1272_);
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1272_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
else
{
return v___x_1275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___boxed(lean_object* v_declName_1307_, lean_object* v_isMeta_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_){
_start:
{
uint8_t v_isMeta_boxed_1312_; lean_object* v_res_1313_; 
v_isMeta_boxed_1312_ = lean_unbox(v_isMeta_1308_);
v_res_1313_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3(v_declName_1307_, v_isMeta_boxed_1312_, v___y_1309_, v___y_1310_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
return v_res_1313_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___x_1318_ = l_Lean_stringToMessageData(v___x_1317_);
return v___x_1318_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__5_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__4_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___x_1321_ = l_Lean_stringToMessageData(v___x_1320_);
return v___x_1321_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__7_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1323_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__6_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___x_1324_ = l_Lean_stringToMessageData(v___x_1323_);
return v___x_1324_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__9_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__8_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___x_1327_ = l_Lean_stringToMessageData(v___x_1326_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(lean_object* v___x_1328_, lean_object* v___x_1329_, lean_object* v___x_1330_, uint8_t v_builtin_1331_, lean_object* v___x_1332_, lean_object* v_name_1333_, lean_object* v_declName_1334_, lean_object* v_stx_1335_, uint8_t v_kind_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; uint8_t v___y_1409_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1481_; lean_object* v___y_1482_; uint8_t v___x_1490_; uint8_t v___x_1491_; 
v___x_1490_ = 0;
v___x_1491_ = l_Lean_instBEqAttributeKind_beq(v_kind_1336_, v___x_1490_);
if (v___x_1491_ == 0)
{
lean_object* v___x_1492_; 
lean_dec(v_stx_1335_);
lean_dec(v_declName_1334_);
lean_dec(v___x_1332_);
lean_dec_ref(v___x_1330_);
lean_dec_ref(v___x_1329_);
lean_dec_ref(v___x_1328_);
v___x_1492_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg(v_name_1333_, v_kind_1336_, v___y_1337_, v___y_1338_);
return v___x_1492_;
}
else
{
goto v___jp_1488_;
}
v___jp_1340_:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1346_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___x_1347_ = l_Lean_Name_mkStr4(v___x_1328_, v___x_1329_, v___x_1330_, v___x_1346_);
v___x_1348_ = l_Lean_mkConst(v___x_1347_, v___y_1342_);
v___x_1349_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v___y_1341_);
v___x_1350_ = l_Lean_mkAppB(v___x_1348_, v___x_1349_, v___y_1345_);
v___x_1351_ = l_Lean_declareBuiltin(v_declName_1334_, v___x_1350_, v___y_1344_, v___y_1343_);
return v___x_1351_;
}
v___jp_1352_:
{
if (v_builtin_1331_ == 0)
{
lean_object* v___x_1358_; lean_object* v_env_1359_; lean_object* v_ref_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
lean_dec_ref(v___y_1354_);
lean_dec_ref(v___x_1330_);
lean_dec_ref(v___x_1329_);
lean_dec_ref(v___x_1328_);
v___x_1358_ = lean_st_ref_get(v___y_1357_);
v_env_1359_ = lean_ctor_get(v___x_1358_, 0);
lean_inc_ref(v_env_1359_);
lean_dec(v___x_1358_);
v_ref_1360_ = lean_ctor_get(v___y_1356_, 2);
v___x_1361_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1356_);
v___x_1362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1362_, 0, v_env_1359_);
lean_ctor_set(v___x_1362_, 1, v___x_1361_);
lean_inc(v_declName_1334_);
v___x_1363_ = l_Lean_Linter_MissingDocs_mkHandlerUnsafe(v_declName_1334_, v___x_1362_);
lean_dec_ref_known(v___x_1362_, 2);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v___x_1365_; lean_object* v_toEnvExtension_1366_; lean_object* v_addEntryFn_1367_; lean_object* v_asyncMode_1368_; uint8_t v_logWrites_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___f_1372_; uint8_t v___x_1373_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_a_1364_);
lean_dec_ref_known(v___x_1363_, 1);
v___x_1365_ = l_Lean_Linter_MissingDocs_missingDocsExt;
v_toEnvExtension_1366_ = lean_ctor_get(v___x_1365_, 0);
v_addEntryFn_1367_ = lean_ctor_get(v___x_1365_, 3);
v_asyncMode_1368_ = lean_ctor_get(v_toEnvExtension_1366_, 2);
v_logWrites_1369_ = lean_ctor_get_uint8(v_toEnvExtension_1366_, sizeof(void*)*6);
v___x_1370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1370_, 0, v___y_1353_);
lean_ctor_set(v___x_1370_, 1, v_a_1364_);
v___x_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1371_, 0, v_declName_1334_);
lean_ctor_set(v___x_1371_, 1, v___x_1370_);
lean_inc(v_addEntryFn_1367_);
v___f_1372_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_addHandler___lam__0), 3, 2);
lean_closure_set(v___f_1372_, 0, v_addEntryFn_1367_);
lean_closure_set(v___f_1372_, 1, v___x_1371_);
v___x_1373_ = 1;
if (v_logWrites_1369_ == 0)
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
lean_inc_ref(v_toEnvExtension_1366_);
v___x_1374_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1366_, v___y_1355_, v___f_1372_, v_asyncMode_1368_, v___x_1332_, v___x_1373_);
v___x_1375_ = l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg(v___x_1374_, v___y_1357_);
return v___x_1375_;
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
lean_inc_ref_n(v_toEnvExtension_1366_, 2);
v___x_1376_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_1366_, v___y_1355_);
lean_dec_ref(v___y_1355_);
v___x_1377_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_1366_, v___x_1376_, v___f_1372_, v_asyncMode_1368_, v___x_1332_, v___x_1373_);
v___x_1378_ = l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg(v___x_1377_, v___y_1357_);
return v___x_1378_;
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1390_; 
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1353_);
lean_dec(v_declName_1334_);
lean_dec(v___x_1332_);
v_a_1379_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1381_ = v___x_1363_;
v_isShared_1382_ = v_isSharedCheck_1390_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1363_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1390_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1388_; 
v___x_1383_ = lean_io_error_to_string(v_a_1379_);
v___x_1384_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
v___x_1385_ = l_Lean_MessageData_ofFormat(v___x_1384_);
lean_inc(v_ref_1360_);
v___x_1386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1386_, 0, v_ref_1360_);
lean_ctor_set(v___x_1386_, 1, v___x_1385_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 0, v___x_1386_);
v___x_1388_ = v___x_1381_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1386_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
else
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; 
lean_dec_ref(v___y_1355_);
lean_dec(v___x_1332_);
v___x_1391_ = l_Lean_ConstantInfo_type(v___y_1354_);
lean_dec_ref(v___y_1354_);
v___x_1392_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__5));
lean_inc_ref(v___x_1330_);
lean_inc_ref(v___x_1329_);
lean_inc_ref(v___x_1328_);
v___x_1393_ = l_Lean_Name_mkStr4(v___x_1328_, v___x_1329_, v___x_1330_, v___x_1392_);
v___x_1394_ = lean_box(0);
v___x_1395_ = l_Lean_Expr_const___override(v___x_1393_, v___x_1394_);
v___x_1396_ = lean_expr_eqv(v___x_1391_, v___x_1395_);
lean_dec_ref(v___x_1395_);
lean_dec_ref(v___x_1391_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; 
lean_inc(v_declName_1334_);
v___x_1397_ = l_Lean_mkConst(v_declName_1334_, v___x_1394_);
v___y_1341_ = v___y_1353_;
v___y_1342_ = v___x_1394_;
v___y_1343_ = v___y_1357_;
v___y_1344_ = v___y_1356_;
v___y_1345_ = v___x_1397_;
goto v___jp_1340_;
}
else
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1398_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
lean_inc_ref(v___x_1330_);
lean_inc_ref(v___x_1329_);
lean_inc_ref(v___x_1328_);
v___x_1399_ = l_Lean_Name_mkStr5(v___x_1328_, v___x_1329_, v___x_1330_, v___x_1392_, v___x_1398_);
v___x_1400_ = l_Lean_mkConst(v___x_1399_, v___x_1394_);
lean_inc(v_declName_1334_);
v___x_1401_ = l_Lean_mkConst(v_declName_1334_, v___x_1394_);
v___x_1402_ = l_Lean_Expr_app___override(v___x_1400_, v___x_1401_);
v___y_1341_ = v___y_1353_;
v___y_1342_ = v___x_1394_;
v___y_1343_ = v___y_1357_;
v___y_1344_ = v___y_1356_;
v___y_1345_ = v___x_1402_;
goto v___jp_1340_;
}
}
}
v___jp_1403_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1405_);
v___x_1410_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_);
v___x_1411_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__6));
lean_inc_ref(v___x_1330_);
lean_inc_ref(v___x_1329_);
lean_inc_ref(v___x_1328_);
v___x_1412_ = l_Lean_Name_mkStr4(v___x_1328_, v___x_1329_, v___x_1330_, v___x_1411_);
v___x_1413_ = l_Lean_MessageData_ofConstName(v___x_1412_, v___y_1409_);
v___x_1414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1410_);
lean_ctor_set(v___x_1414_, 1, v___x_1413_);
v___x_1415_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__5_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__5_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__5_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_);
v___x_1416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1414_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
v___x_1417_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__5));
v___x_1418_ = l_Lean_Name_mkStr4(v___x_1328_, v___x_1329_, v___x_1330_, v___x_1417_);
v___x_1419_ = l_Lean_MessageData_ofConstName(v___x_1418_, v___y_1409_);
v___x_1420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1416_);
lean_ctor_set(v___x_1420_, 1, v___x_1419_);
v___x_1421_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__7_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__7_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__7_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_);
v___x_1422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1420_);
lean_ctor_set(v___x_1422_, 1, v___x_1421_);
v___x_1423_ = l_Lean_MessageData_ofName(v_declName_1334_);
v___x_1424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1422_);
lean_ctor_set(v___x_1424_, 1, v___x_1423_);
v___x_1425_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__9_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__9_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__9_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_);
v___x_1426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1424_);
lean_ctor_set(v___x_1426_, 1, v___x_1425_);
v___x_1427_ = l_Lean_ConstantInfo_type(v___y_1406_);
lean_dec_ref(v___y_1406_);
v___x_1428_ = l_Lean_indentExpr(v___x_1427_);
v___x_1429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1426_);
lean_ctor_set(v___x_1429_, 1, v___x_1428_);
v___x_1430_ = l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0___redArg(v___x_1429_, v___y_1404_, v___y_1407_);
return v___x_1430_;
}
v___jp_1431_:
{
lean_object* v___x_1435_; 
lean_inc(v_declName_1334_);
v___x_1435_ = l_Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1(v_declName_1334_, v___y_1433_, v___y_1434_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; lean_object* v___x_1437_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_a_1436_);
lean_dec_ref_known(v___x_1435_, 1);
v___x_1437_ = l_Lean_Attribute_Builtin_getIdent(v_stx_1335_, v___y_1433_, v___y_1434_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_a_1438_);
lean_dec_ref_known(v___x_1437_, 1);
v___x_1439_ = lean_box(0);
v___x_1440_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_a_1438_, v___x_1439_, v___y_1433_, v___y_1434_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; uint8_t v___x_1442_; lean_object* v___x_1443_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc_n(v_a_1441_, 2);
lean_dec_ref_known(v___x_1440_, 1);
v___x_1442_ = 0;
v___x_1443_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3(v_a_1441_, v___x_1442_, v___y_1433_, v___y_1434_);
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v___x_1444_; uint8_t v___x_1445_; 
lean_dec_ref_known(v___x_1443_, 1);
v___x_1444_ = l_Lean_ConstantInfo_levelParams(v_a_1436_);
v___x_1445_ = l_List_isEmpty___redArg(v___x_1444_);
lean_dec(v___x_1444_);
if (v___x_1445_ == 0)
{
lean_dec(v___x_1332_);
v___y_1404_ = v___y_1433_;
v___y_1405_ = v_a_1441_;
v___y_1406_ = v_a_1436_;
v___y_1407_ = v___y_1434_;
v___y_1408_ = v___y_1432_;
v___y_1409_ = v___x_1442_;
goto v___jp_1403_;
}
else
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; 
v___x_1446_ = l_Lean_ConstantInfo_type(v_a_1436_);
v___x_1447_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__6));
lean_inc_ref(v___x_1330_);
lean_inc_ref(v___x_1329_);
lean_inc_ref(v___x_1328_);
v___x_1448_ = l_Lean_Name_mkStr4(v___x_1328_, v___x_1329_, v___x_1330_, v___x_1447_);
v___x_1449_ = lean_box(0);
v___x_1450_ = l_Lean_Expr_const___override(v___x_1448_, v___x_1449_);
v___x_1451_ = lean_expr_eqv(v___x_1446_, v___x_1450_);
lean_dec_ref(v___x_1450_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; uint8_t v___x_1455_; 
v___x_1452_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__5));
lean_inc_ref(v___x_1330_);
lean_inc_ref(v___x_1329_);
lean_inc_ref(v___x_1328_);
v___x_1453_ = l_Lean_Name_mkStr4(v___x_1328_, v___x_1329_, v___x_1330_, v___x_1452_);
v___x_1454_ = l_Lean_Expr_const___override(v___x_1453_, v___x_1449_);
v___x_1455_ = lean_expr_eqv(v___x_1446_, v___x_1454_);
lean_dec_ref(v___x_1454_);
lean_dec_ref(v___x_1446_);
if (v___x_1455_ == 0)
{
lean_dec(v___x_1332_);
v___y_1404_ = v___y_1433_;
v___y_1405_ = v_a_1441_;
v___y_1406_ = v_a_1436_;
v___y_1407_ = v___y_1434_;
v___y_1408_ = v___y_1432_;
v___y_1409_ = v___x_1442_;
goto v___jp_1403_;
}
else
{
v___y_1353_ = v_a_1441_;
v___y_1354_ = v_a_1436_;
v___y_1355_ = v___y_1432_;
v___y_1356_ = v___y_1433_;
v___y_1357_ = v___y_1434_;
goto v___jp_1352_;
}
}
else
{
lean_dec_ref(v___x_1446_);
v___y_1353_ = v_a_1441_;
v___y_1354_ = v_a_1436_;
v___y_1355_ = v___y_1432_;
v___y_1356_ = v___y_1433_;
v___y_1357_ = v___y_1434_;
goto v___jp_1352_;
}
}
}
else
{
lean_dec(v_a_1441_);
lean_dec(v_a_1436_);
lean_dec_ref(v___y_1432_);
lean_dec(v_declName_1334_);
lean_dec(v___x_1332_);
lean_dec_ref(v___x_1330_);
lean_dec_ref(v___x_1329_);
lean_dec_ref(v___x_1328_);
return v___x_1443_;
}
}
else
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
lean_dec(v_a_1436_);
lean_dec_ref(v___y_1432_);
lean_dec(v_declName_1334_);
lean_dec(v___x_1332_);
lean_dec_ref(v___x_1330_);
lean_dec_ref(v___x_1329_);
lean_dec_ref(v___x_1328_);
v_a_1456_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1440_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1440_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
lean_dec(v_a_1436_);
lean_dec_ref(v___y_1432_);
lean_dec(v_declName_1334_);
lean_dec(v___x_1332_);
lean_dec_ref(v___x_1330_);
lean_dec_ref(v___x_1329_);
lean_dec_ref(v___x_1328_);
v_a_1464_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1437_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1437_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
lean_dec_ref(v___y_1432_);
lean_dec(v_stx_1335_);
lean_dec(v_declName_1334_);
lean_dec(v___x_1332_);
lean_dec_ref(v___x_1330_);
lean_dec_ref(v___x_1329_);
lean_dec_ref(v___x_1328_);
v_a_1472_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1435_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1435_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
v___jp_1480_:
{
lean_object* v___x_1483_; 
v___x_1483_ = lean_st_ref_get(v___y_1482_);
if (v_builtin_1331_ == 0)
{
lean_object* v_env_1484_; lean_object* v___x_1485_; 
v_env_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc_ref(v_env_1484_);
lean_dec(v___x_1483_);
v___x_1485_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1484_, v_declName_1334_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_dec(v_name_1333_);
v___y_1432_ = v_env_1484_;
v___y_1433_ = v___y_1481_;
v___y_1434_ = v___y_1482_;
goto v___jp_1431_;
}
else
{
lean_object* v___x_1486_; 
lean_dec_ref_known(v___x_1485_, 1);
lean_dec_ref(v_env_1484_);
lean_dec(v_stx_1335_);
lean_dec(v___x_1332_);
lean_dec_ref(v___x_1330_);
lean_dec_ref(v___x_1329_);
lean_dec_ref(v___x_1328_);
v___x_1486_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg(v_name_1333_, v_declName_1334_, v___y_1481_, v___y_1482_);
return v___x_1486_;
}
}
else
{
lean_object* v_env_1487_; 
lean_dec(v_name_1333_);
v_env_1487_ = lean_ctor_get(v___x_1483_, 0);
lean_inc_ref(v_env_1487_);
lean_dec(v___x_1483_);
v___y_1432_ = v_env_1487_;
v___y_1433_ = v___y_1481_;
v___y_1434_ = v___y_1482_;
goto v___jp_1431_;
}
}
v___jp_1488_:
{
if (v_builtin_1331_ == 0)
{
lean_object* v___x_1489_; 
lean_inc(v_declName_1334_);
lean_inc(v_name_1333_);
v___x_1489_ = l_Lean_ensureAttrDeclIsMeta(v_name_1333_, v_declName_1334_, v_kind_1336_, v___y_1337_, v___y_1338_);
if (lean_obj_tag(v___x_1489_) == 0)
{
lean_dec_ref_known(v___x_1489_, 1);
v___y_1481_ = v___y_1337_;
v___y_1482_ = v___y_1338_;
goto v___jp_1480_;
}
else
{
lean_dec(v_stx_1335_);
lean_dec(v_declName_1334_);
lean_dec(v_name_1333_);
lean_dec(v___x_1332_);
lean_dec_ref(v___x_1330_);
lean_dec_ref(v___x_1329_);
lean_dec_ref(v___x_1328_);
return v___x_1489_;
}
}
else
{
v___y_1481_ = v___y_1337_;
v___y_1482_ = v___y_1338_;
goto v___jp_1480_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2____boxed(lean_object* v___x_1493_, lean_object* v___x_1494_, lean_object* v___x_1495_, lean_object* v_builtin_1496_, lean_object* v___x_1497_, lean_object* v_name_1498_, lean_object* v_declName_1499_, lean_object* v_stx_1500_, lean_object* v_kind_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
uint8_t v_builtin_boxed_1505_; uint8_t v_kind_boxed_1506_; lean_object* v_res_1507_; 
v_builtin_boxed_1505_ = lean_unbox(v_builtin_1496_);
v_kind_boxed_1506_ = lean_unbox(v_kind_1501_);
v_res_1507_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(v___x_1493_, v___x_1494_, v___x_1495_, v_builtin_boxed_1505_, v___x_1497_, v_name_1498_, v_declName_1499_, v_stx_1500_, v_kind_boxed_1506_, v___y_1502_, v___y_1503_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(uint8_t v_builtin_1566_, lean_object* v_name_1567_){
_start:
{
lean_object* v___f_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___f_1575_; lean_object* v___x_1576_; lean_object* v___y_1578_; 
lean_inc_n(v_name_1567_, 2);
v___f_1569_ = lean_alloc_closure((void*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_1569_, 0, v_name_1567_);
v___x_1570_ = lean_box(0);
v___x_1571_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_));
v___x_1572_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_));
v___x_1573_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__4));
v___x_1574_ = lean_box(v_builtin_1566_);
v___f_1575_ = lean_alloc_closure((void*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2____boxed), 12, 6);
lean_closure_set(v___f_1575_, 0, v___x_1571_);
lean_closure_set(v___f_1575_, 1, v___x_1572_);
lean_closure_set(v___f_1575_, 2, v___x_1573_);
lean_closure_set(v___f_1575_, 3, v___x_1574_);
lean_closure_set(v___f_1575_, 4, v___x_1570_);
lean_closure_set(v___f_1575_, 5, v_name_1567_);
v___x_1576_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__21_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
if (v_builtin_1566_ == 0)
{
lean_object* v___x_1585_; 
v___x_1585_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__1));
v___y_1578_ = v___x_1585_;
goto v___jp_1577_;
}
else
{
lean_object* v___x_1586_; 
v___x_1586_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__23_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___y_1578_ = v___x_1586_;
goto v___jp_1577_;
}
v___jp_1577_:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; uint8_t v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1579_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__22_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
lean_inc_ref(v___y_1578_);
v___x_1580_ = lean_string_append(v___y_1578_, v___x_1579_);
v___x_1581_ = 1;
v___x_1582_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1582_, 0, v___x_1576_);
lean_ctor_set(v___x_1582_, 1, v_name_1567_);
lean_ctor_set(v___x_1582_, 2, v___x_1580_);
lean_ctor_set_uint8(v___x_1582_, sizeof(void*)*3, v___x_1581_);
v___x_1583_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1582_);
lean_ctor_set(v___x_1583_, 1, v___f_1575_);
lean_ctor_set(v___x_1583_, 2, v___f_1569_);
v___x_1584_ = l_Lean_registerBuiltinAttribute(v___x_1583_);
return v___x_1584_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2____boxed(lean_object* v_builtin_1587_, lean_object* v_name_1588_, lean_object* v___y_1589_){
_start:
{
uint8_t v_builtin_boxed_1590_; lean_object* v_res_1591_; 
v_builtin_boxed_1590_ = lean_unbox(v_builtin_1587_);
v_res_1591_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(v_builtin_boxed_1590_, v_name_1588_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(){
_start:
{
uint8_t v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1599_ = 1;
v___x_1600_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___x_1601_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(v___x_1599_, v___x_1600_);
if (lean_obj_tag(v___x_1601_) == 0)
{
uint8_t v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
lean_dec_ref_known(v___x_1601_, 1);
v___x_1602_ = 0;
v___x_1603_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___x_1604_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(v___x_1602_, v___x_1603_);
return v___x_1604_;
}
else
{
return v___x_1601_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2____boxed(lean_object* v_a_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_();
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1607_, lean_object* v_msg_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0___redArg(v_msg_1608_, v___y_1609_, v___y_1610_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1613_, lean_object* v_msg_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0(v_00_u03b1_1613_, v_msg_1614_, v___y_1615_, v___y_1616_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b1_1619_, lean_object* v_attrName_1620_, lean_object* v_declName_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg(v_attrName_1620_, v_declName_1621_, v___y_1622_, v___y_1623_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___boxed(lean_object* v_00_u03b1_1626_, lean_object* v_attrName_1627_, lean_object* v_declName_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4(v_00_u03b1_1626_, v_attrName_1627_, v_declName_1628_, v___y_1629_, v___y_1630_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5(lean_object* v_00_u03b1_1633_, lean_object* v_name_1634_, uint8_t v_kind_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg(v_name_1634_, v_kind_1635_, v___y_1636_, v___y_1637_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___boxed(lean_object* v_00_u03b1_1640_, lean_object* v_name_1641_, lean_object* v_kind_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
uint8_t v_kind_boxed_1646_; lean_object* v_res_1647_; 
v_kind_boxed_1646_ = lean_unbox(v_kind_1642_);
v_res_1647_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5(v_00_u03b1_1640_, v_name_1641_, v_kind_boxed_1646_, v___y_1643_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b1_1648_, lean_object* v_constName_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2___redArg(v_constName_1649_, v___y_1650_, v___y_1651_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b1_1654_, lean_object* v_constName_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b1_1654_, v_constName_1655_, v___y_1656_, v___y_1657_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7(lean_object* v_00_u03b2_1660_, lean_object* v_m_1661_, lean_object* v_a_1662_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___redArg(v_m_1661_, v_a_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___boxed(lean_object* v_00_u03b2_1664_, lean_object* v_m_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7(v_00_u03b2_1664_, v_m_1665_, v_a_1666_);
lean_dec(v_a_1666_);
lean_dec_ref(v_m_1665_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1668_, lean_object* v_ref_1669_, lean_object* v_constName_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_ref_1669_, v_constName_1670_, v___y_1671_, v___y_1672_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1675_, lean_object* v_ref_1676_, lean_object* v_constName_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_00_u03b1_1675_, v_ref_1676_, v_constName_1677_, v___y_1678_, v___y_1679_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v_ref_1676_);
return v_res_1681_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7(lean_object* v_00_u03b2_1682_, lean_object* v_x_1683_, lean_object* v_x_1684_){
_start:
{
uint8_t v___x_1685_; 
v___x_1685_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(v_x_1683_, v_x_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b2_1686_, lean_object* v_x_1687_, lean_object* v_x_1688_){
_start:
{
uint8_t v_res_1689_; lean_object* v_r_1690_; 
v_res_1689_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7(v_00_u03b2_1686_, v_x_1687_, v_x_1688_);
lean_dec_ref(v_x_1688_);
lean_dec_ref(v_x_1687_);
v_r_1690_ = lean_box(v_res_1689_);
return v_r_1690_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11(lean_object* v_00_u03b2_1691_, lean_object* v_a_1692_, lean_object* v_x_1693_){
_start:
{
lean_object* v___x_1694_; 
v___x_1694_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11___redArg(v_a_1692_, v_x_1693_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11___boxed(lean_object* v_00_u03b2_1695_, lean_object* v_a_1696_, lean_object* v_x_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11(v_00_u03b2_1695_, v_a_1696_, v_x_1697_);
lean_dec(v_x_1697_);
lean_dec(v_a_1696_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b1_1699_, lean_object* v_ref_1700_, lean_object* v_msg_1701_, lean_object* v_declHint_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v___x_1706_; 
v___x_1706_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8___redArg(v_ref_1700_, v_msg_1701_, v_declHint_1702_, v___y_1703_, v___y_1704_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b1_1707_, lean_object* v_ref_1708_, lean_object* v_msg_1709_, lean_object* v_declHint_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(v_00_u03b1_1707_, v_ref_1708_, v_msg_1709_, v_declHint_1710_, v___y_1711_, v___y_1712_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v_ref_1708_);
return v_res_1714_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11(lean_object* v_00_u03b2_1715_, lean_object* v_x_1716_, size_t v_x_1717_, lean_object* v_x_1718_){
_start:
{
uint8_t v___x_1719_; 
v___x_1719_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg(v_x_1716_, v_x_1717_, v_x_1718_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___boxed(lean_object* v_00_u03b2_1720_, lean_object* v_x_1721_, lean_object* v_x_1722_, lean_object* v_x_1723_){
_start:
{
size_t v_x_10404__boxed_1724_; uint8_t v_res_1725_; lean_object* v_r_1726_; 
v_x_10404__boxed_1724_ = lean_unbox_usize(v_x_1722_);
lean_dec(v_x_1722_);
v_res_1725_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11(v_00_u03b2_1720_, v_x_1721_, v_x_10404__boxed_1724_, v_x_1723_);
lean_dec_ref(v_x_1723_);
lean_dec_ref(v_x_1721_);
v_r_1726_ = lean_box(v_res_1725_);
return v_r_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16(lean_object* v_msg_1727_, lean_object* v_declHint_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg(v_msg_1727_, v_declHint_1728_, v___y_1730_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___boxed(lean_object* v_msg_1733_, lean_object* v_declHint_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16(v_msg_1733_, v_declHint_1734_, v___y_1735_, v___y_1736_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__13(lean_object* v_00_u03b1_1739_, lean_object* v_ref_1740_, lean_object* v_msg_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__13___redArg(v_ref_1740_, v_msg_1741_, v___y_1742_, v___y_1743_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__13___boxed(lean_object* v_00_u03b1_1746_, lean_object* v_ref_1747_, lean_object* v_msg_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__13(v_00_u03b1_1746_, v_ref_1747_, v_msg_1748_, v___y_1749_, v___y_1750_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v_ref_1747_);
return v_res_1752_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16(lean_object* v_00_u03b2_1753_, lean_object* v_keys_1754_, lean_object* v_vals_1755_, lean_object* v_heq_1756_, lean_object* v_i_1757_, lean_object* v_k_1758_){
_start:
{
uint8_t v___x_1759_; 
v___x_1759_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16___redArg(v_keys_1754_, v_i_1757_, v_k_1758_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16___boxed(lean_object* v_00_u03b2_1760_, lean_object* v_keys_1761_, lean_object* v_vals_1762_, lean_object* v_heq_1763_, lean_object* v_i_1764_, lean_object* v_k_1765_){
_start:
{
uint8_t v_res_1766_; lean_object* v_r_1767_; 
v_res_1766_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16(v_00_u03b2_1760_, v_keys_1761_, v_vals_1762_, v_heq_1763_, v_i_1764_, v_k_1765_);
lean_dec_ref(v_k_1765_);
lean_dec_ref(v_vals_1762_);
lean_dec_ref(v_keys_1761_);
v_r_1767_ = lean_box(v_res_1766_);
return v_r_1767_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__3(lean_object* v_opts_1768_, lean_object* v_opt_1769_){
_start:
{
lean_object* v_name_1770_; lean_object* v_defValue_1771_; lean_object* v_map_1772_; lean_object* v___x_1773_; 
v_name_1770_ = lean_ctor_get(v_opt_1769_, 0);
v_defValue_1771_ = lean_ctor_get(v_opt_1769_, 1);
v_map_1772_ = lean_ctor_get(v_opts_1768_, 0);
v___x_1773_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1772_, v_name_1770_);
if (lean_obj_tag(v___x_1773_) == 0)
{
uint8_t v___x_1774_; 
v___x_1774_ = lean_unbox(v_defValue_1771_);
return v___x_1774_;
}
else
{
lean_object* v_val_1775_; 
v_val_1775_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_val_1775_);
lean_dec_ref_known(v___x_1773_, 1);
if (lean_obj_tag(v_val_1775_) == 1)
{
uint8_t v_v_1776_; 
v_v_1776_ = lean_ctor_get_uint8(v_val_1775_, 0);
lean_dec_ref_known(v_val_1775_, 0);
return v_v_1776_;
}
else
{
uint8_t v___x_1777_; 
lean_dec(v_val_1775_);
v___x_1777_ = lean_unbox(v_defValue_1771_);
return v___x_1777_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_opts_1778_, lean_object* v_opt_1779_){
_start:
{
uint8_t v_res_1780_; lean_object* v_r_1781_; 
v_res_1780_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__3(v_opts_1778_, v_opt_1779_);
lean_dec_ref(v_opt_1779_);
lean_dec_ref(v_opts_1778_);
v_r_1781_ = lean_box(v_res_1780_);
return v_r_1781_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_1782_, lean_object* v_x_1783_){
_start:
{
if (lean_obj_tag(v_x_1783_) == 1)
{
lean_object* v_pre_1784_; 
v_pre_1784_ = lean_ctor_get(v_x_1783_, 0);
if (lean_obj_tag(v_pre_1784_) == 0)
{
lean_object* v_str_1785_; lean_object* v___x_1786_; uint8_t v___x_1787_; 
v_str_1785_ = lean_ctor_get(v_x_1783_, 1);
v___x_1786_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__8));
v___x_1787_ = lean_string_dec_eq(v_str_1785_, v___x_1786_);
if (v___x_1787_ == 0)
{
return v___x_1787_;
}
else
{
return v_suppressElabErrors_1782_;
}
}
else
{
uint8_t v___x_1788_; 
v___x_1788_ = 0;
return v___x_1788_;
}
}
else
{
uint8_t v___x_1789_; 
v___x_1789_ = 0;
return v___x_1789_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_1790_, lean_object* v_x_1791_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1792_; uint8_t v_res_1793_; lean_object* v_r_1794_; 
v_suppressElabErrors_boxed_1792_ = lean_unbox(v_suppressElabErrors_1790_);
v_res_1793_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_1792_, v_x_1791_);
lean_dec(v_x_1791_);
v_r_1794_ = lean_box(v_res_1793_);
return v_r_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_msgData_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v___x_1798_; lean_object* v_env_1799_; uint8_t v___x_1800_; lean_object* v_env_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v_scopes_1804_; lean_object* v___x_1805_; lean_object* v_opts_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1798_ = lean_st_ref_get(v___y_1796_);
v_env_1799_ = lean_ctor_get(v___x_1798_, 0);
lean_inc_ref(v_env_1799_);
lean_dec(v___x_1798_);
v___x_1800_ = 0;
v_env_1801_ = l_Lean_Environment_setRecordingDeps(v_env_1799_, v___x_1800_);
v___x_1802_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1803_ = lean_st_ref_get(v___y_1796_);
v_scopes_1804_ = lean_ctor_get(v___x_1803_, 2);
lean_inc(v_scopes_1804_);
lean_dec(v___x_1803_);
v___x_1805_ = l_List_head_x21___redArg(v___x_1802_, v_scopes_1804_);
lean_dec(v_scopes_1804_);
v_opts_1806_ = lean_ctor_get(v___x_1805_, 1);
lean_inc_ref(v_opts_1806_);
lean_dec(v___x_1805_);
v___x_1807_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_1808_ = lean_unsigned_to_nat(32u);
v___x_1809_ = lean_mk_empty_array_with_capacity(v___x_1808_);
lean_dec_ref(v___x_1809_);
v___x_1810_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_1811_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1811_, 0, v_env_1801_);
lean_ctor_set(v___x_1811_, 1, v___x_1807_);
lean_ctor_set(v___x_1811_, 2, v___x_1810_);
lean_ctor_set(v___x_1811_, 3, v_opts_1806_);
v___x_1812_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1811_);
lean_ctor_set(v___x_1812_, 1, v_msgData_1795_);
v___x_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2___redArg(v_msgData_1814_, v___y_1815_);
lean_dec(v___y_1815_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1(lean_object* v_ref_1818_, lean_object* v_msgData_1819_, uint8_t v_severity_1820_, uint8_t v_isSilent_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; uint8_t v___y_1830_; lean_object* v___y_1831_; uint8_t v___y_1832_; lean_object* v___y_1833_; uint8_t v___y_1891_; lean_object* v___y_1892_; uint8_t v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1917_; uint8_t v___y_1918_; uint8_t v___y_1919_; lean_object* v___y_1920_; uint8_t v___y_1924_; uint8_t v___y_1925_; uint8_t v___x_1940_; uint8_t v___y_1942_; uint8_t v___x_1952_; 
v___x_1940_ = 2;
v___x_1952_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1820_, v___x_1940_);
if (v___x_1952_ == 0)
{
v___y_1942_ = v___x_1952_;
goto v___jp_1941_;
}
else
{
uint8_t v___x_1953_; 
lean_inc_ref(v_msgData_1819_);
v___x_1953_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1819_);
if (v___x_1953_ == 0)
{
v___y_1942_ = v___x_1953_;
goto v___jp_1941_;
}
else
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
lean_dec_ref(v_msgData_1819_);
v___x_1954_ = lean_box(0);
v___x_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1954_);
return v___x_1955_;
}
}
v___jp_1825_:
{
lean_object* v___x_1834_; 
v___x_1834_ = l_Lean_Elab_Command_getScope___redArg(v___y_1833_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v_currNamespace_1836_; lean_object* v___x_1837_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_a_1835_);
lean_dec_ref_known(v___x_1834_, 1);
v_currNamespace_1836_ = lean_ctor_get(v_a_1835_, 2);
lean_inc(v_currNamespace_1836_);
lean_dec(v_a_1835_);
v___x_1837_ = l_Lean_Elab_Command_getScope___redArg(v___y_1833_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1873_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1840_ = v___x_1837_;
v_isShared_1841_ = v_isSharedCheck_1873_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1837_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1873_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v_openDecls_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v_env_1847_; lean_object* v_messages_1848_; lean_object* v_scopes_1849_; lean_object* v_usedQuotCtxts_1850_; lean_object* v_nextMacroScope_1851_; lean_object* v_maxRecDepth_1852_; lean_object* v_ngen_1853_; lean_object* v_auxDeclNGen_1854_; lean_object* v_infoState_1855_; lean_object* v_traceState_1856_; lean_object* v_snapshotTasks_1857_; lean_object* v_prevLinterStates_1858_; lean_object* v_codeQualityEntryTasks_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1872_; 
v_openDecls_1842_ = lean_ctor_get(v_a_1838_, 3);
lean_inc(v_openDecls_1842_);
lean_dec(v_a_1838_);
v___x_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1843_, 0, v_currNamespace_1836_);
lean_ctor_set(v___x_1843_, 1, v_openDecls_1842_);
v___x_1844_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
lean_ctor_set(v___x_1844_, 1, v___y_1826_);
lean_inc_ref(v___y_1828_);
lean_inc_ref(v___y_1829_);
v___x_1845_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1845_, 0, v___y_1829_);
lean_ctor_set(v___x_1845_, 1, v___y_1831_);
lean_ctor_set(v___x_1845_, 2, v___y_1827_);
lean_ctor_set(v___x_1845_, 3, v___y_1828_);
lean_ctor_set(v___x_1845_, 4, v___x_1844_);
lean_ctor_set_uint8(v___x_1845_, sizeof(void*)*5, v___y_1830_);
lean_ctor_set_uint8(v___x_1845_, sizeof(void*)*5 + 1, v___y_1832_);
lean_ctor_set_uint8(v___x_1845_, sizeof(void*)*5 + 2, v_isSilent_1821_);
v___x_1846_ = lean_st_ref_take(v___y_1833_);
v_env_1847_ = lean_ctor_get(v___x_1846_, 0);
v_messages_1848_ = lean_ctor_get(v___x_1846_, 1);
v_scopes_1849_ = lean_ctor_get(v___x_1846_, 2);
v_usedQuotCtxts_1850_ = lean_ctor_get(v___x_1846_, 3);
v_nextMacroScope_1851_ = lean_ctor_get(v___x_1846_, 4);
v_maxRecDepth_1852_ = lean_ctor_get(v___x_1846_, 5);
v_ngen_1853_ = lean_ctor_get(v___x_1846_, 6);
v_auxDeclNGen_1854_ = lean_ctor_get(v___x_1846_, 7);
v_infoState_1855_ = lean_ctor_get(v___x_1846_, 8);
v_traceState_1856_ = lean_ctor_get(v___x_1846_, 9);
v_snapshotTasks_1857_ = lean_ctor_get(v___x_1846_, 10);
v_prevLinterStates_1858_ = lean_ctor_get(v___x_1846_, 11);
v_codeQualityEntryTasks_1859_ = lean_ctor_get(v___x_1846_, 12);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1861_ = v___x_1846_;
v_isShared_1862_ = v_isSharedCheck_1872_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1859_);
lean_inc(v_prevLinterStates_1858_);
lean_inc(v_snapshotTasks_1857_);
lean_inc(v_traceState_1856_);
lean_inc(v_infoState_1855_);
lean_inc(v_auxDeclNGen_1854_);
lean_inc(v_ngen_1853_);
lean_inc(v_maxRecDepth_1852_);
lean_inc(v_nextMacroScope_1851_);
lean_inc(v_usedQuotCtxts_1850_);
lean_inc(v_scopes_1849_);
lean_inc(v_messages_1848_);
lean_inc(v_env_1847_);
lean_dec(v___x_1846_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1872_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1866_; 
v___x_1863_ = lean_box(0);
v___x_1864_ = l_Lean_MessageLog_add(v___x_1845_, v_messages_1848_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 1, v___x_1864_);
v___x_1866_ = v___x_1861_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_env_1847_);
lean_ctor_set(v_reuseFailAlloc_1871_, 1, v___x_1864_);
lean_ctor_set(v_reuseFailAlloc_1871_, 2, v_scopes_1849_);
lean_ctor_set(v_reuseFailAlloc_1871_, 3, v_usedQuotCtxts_1850_);
lean_ctor_set(v_reuseFailAlloc_1871_, 4, v_nextMacroScope_1851_);
lean_ctor_set(v_reuseFailAlloc_1871_, 5, v_maxRecDepth_1852_);
lean_ctor_set(v_reuseFailAlloc_1871_, 6, v_ngen_1853_);
lean_ctor_set(v_reuseFailAlloc_1871_, 7, v_auxDeclNGen_1854_);
lean_ctor_set(v_reuseFailAlloc_1871_, 8, v_infoState_1855_);
lean_ctor_set(v_reuseFailAlloc_1871_, 9, v_traceState_1856_);
lean_ctor_set(v_reuseFailAlloc_1871_, 10, v_snapshotTasks_1857_);
lean_ctor_set(v_reuseFailAlloc_1871_, 11, v_prevLinterStates_1858_);
lean_ctor_set(v_reuseFailAlloc_1871_, 12, v_codeQualityEntryTasks_1859_);
v___x_1866_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
lean_object* v___x_1867_; lean_object* v___x_1869_; 
v___x_1867_ = lean_st_ref_put(v___y_1833_, v___x_1866_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v___x_1863_);
v___x_1869_ = v___x_1840_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1863_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_dec(v_currNamespace_1836_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
v_a_1874_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1837_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1837_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
v_a_1882_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1834_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1834_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
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
v___jp_1890_:
{
lean_object* v_fileName_1895_; lean_object* v_fileMap_1896_; uint8_t v_suppressElabErrors_1897_; lean_object* v___x_1898_; lean_object* v___f_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1915_; 
v_fileName_1895_ = lean_ctor_get(v___y_1822_, 0);
v_fileMap_1896_ = lean_ctor_get(v___y_1822_, 1);
v_suppressElabErrors_1897_ = lean_ctor_get_uint8(v___y_1822_, sizeof(void*)*10);
v___x_1898_ = lean_box(v_suppressElabErrors_1897_);
v___f_1899_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1899_, 0, v___x_1898_);
v___x_1900_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1819_);
v___x_1901_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1900_, v___y_1823_);
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1904_ = v___x_1901_;
v_isShared_1905_ = v_isSharedCheck_1915_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1901_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1915_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
lean_inc_ref_n(v_fileMap_1896_, 2);
v___x_1906_ = l_Lean_FileMap_toPosition(v_fileMap_1896_, v___y_1892_);
lean_dec(v___y_1892_);
v___x_1907_ = l_Lean_FileMap_toPosition(v_fileMap_1896_, v___y_1894_);
lean_dec(v___y_1894_);
v___x_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
v___x_1909_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__1));
if (v_suppressElabErrors_1897_ == 0)
{
lean_del_object(v___x_1904_);
lean_dec_ref(v___f_1899_);
v___y_1826_ = v_a_1902_;
v___y_1827_ = v___x_1908_;
v___y_1828_ = v___x_1909_;
v___y_1829_ = v_fileName_1895_;
v___y_1830_ = v___y_1891_;
v___y_1831_ = v___x_1906_;
v___y_1832_ = v___y_1893_;
v___y_1833_ = v___y_1823_;
goto v___jp_1825_;
}
else
{
uint8_t v___x_1910_; 
lean_inc(v_a_1902_);
v___x_1910_ = l_Lean_MessageData_hasTag(v___f_1899_, v_a_1902_);
if (v___x_1910_ == 0)
{
lean_object* v___x_1911_; lean_object* v___x_1913_; 
lean_dec_ref_known(v___x_1908_, 1);
lean_dec_ref(v___x_1906_);
lean_dec(v_a_1902_);
v___x_1911_ = lean_box(0);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v___x_1911_);
v___x_1913_ = v___x_1904_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
else
{
lean_del_object(v___x_1904_);
v___y_1826_ = v_a_1902_;
v___y_1827_ = v___x_1908_;
v___y_1828_ = v___x_1909_;
v___y_1829_ = v_fileName_1895_;
v___y_1830_ = v___y_1891_;
v___y_1831_ = v___x_1906_;
v___y_1832_ = v___y_1893_;
v___y_1833_ = v___y_1823_;
goto v___jp_1825_;
}
}
}
}
v___jp_1916_:
{
lean_object* v___x_1921_; 
v___x_1921_ = l_Lean_Syntax_getTailPos_x3f(v___y_1917_, v___y_1918_);
lean_dec(v___y_1917_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_inc(v___y_1920_);
v___y_1891_ = v___y_1918_;
v___y_1892_ = v___y_1920_;
v___y_1893_ = v___y_1919_;
v___y_1894_ = v___y_1920_;
goto v___jp_1890_;
}
else
{
lean_object* v_val_1922_; 
v_val_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_val_1922_);
lean_dec_ref_known(v___x_1921_, 1);
v___y_1891_ = v___y_1918_;
v___y_1892_ = v___y_1920_;
v___y_1893_ = v___y_1919_;
v___y_1894_ = v_val_1922_;
goto v___jp_1890_;
}
}
v___jp_1923_:
{
lean_object* v___x_1926_; 
v___x_1926_ = l_Lean_Elab_Command_getRef___redArg(v___y_1822_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_a_1927_; lean_object* v_ref_1928_; lean_object* v___x_1929_; 
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
lean_inc(v_a_1927_);
lean_dec_ref_known(v___x_1926_, 1);
v_ref_1928_ = l_Lean_replaceRef(v_ref_1818_, v_a_1927_);
lean_dec(v_a_1927_);
v___x_1929_ = l_Lean_Syntax_getPos_x3f(v_ref_1928_, v___y_1924_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v___x_1930_; 
v___x_1930_ = lean_unsigned_to_nat(0u);
v___y_1917_ = v_ref_1928_;
v___y_1918_ = v___y_1924_;
v___y_1919_ = v___y_1925_;
v___y_1920_ = v___x_1930_;
goto v___jp_1916_;
}
else
{
lean_object* v_val_1931_; 
v_val_1931_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_val_1931_);
lean_dec_ref_known(v___x_1929_, 1);
v___y_1917_ = v_ref_1928_;
v___y_1918_ = v___y_1924_;
v___y_1919_ = v___y_1925_;
v___y_1920_ = v_val_1931_;
goto v___jp_1916_;
}
}
else
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
lean_dec_ref(v_msgData_1819_);
v_a_1932_ = lean_ctor_get(v___x_1926_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v___x_1926_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1926_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1932_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
v___jp_1941_:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v_scopes_1945_; lean_object* v___x_1946_; lean_object* v_opts_1947_; uint8_t v___x_1948_; uint8_t v___x_1949_; 
v___x_1943_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1944_ = lean_st_ref_get(v___y_1823_);
v_scopes_1945_ = lean_ctor_get(v___x_1944_, 2);
lean_inc(v_scopes_1945_);
lean_dec(v___x_1944_);
v___x_1946_ = l_List_head_x21___redArg(v___x_1943_, v_scopes_1945_);
lean_dec(v_scopes_1945_);
v_opts_1947_ = lean_ctor_get(v___x_1946_, 1);
lean_inc_ref(v_opts_1947_);
lean_dec(v___x_1946_);
v___x_1948_ = 1;
v___x_1949_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1820_, v___x_1948_);
if (v___x_1949_ == 0)
{
lean_dec_ref(v_opts_1947_);
v___y_1924_ = v___y_1942_;
v___y_1925_ = v_severity_1820_;
goto v___jp_1923_;
}
else
{
lean_object* v___x_1950_; uint8_t v___x_1951_; 
v___x_1950_ = l_Lean_warningAsError;
v___x_1951_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__3(v_opts_1947_, v___x_1950_);
lean_dec_ref(v_opts_1947_);
if (v___x_1951_ == 0)
{
v___y_1924_ = v___y_1942_;
v___y_1925_ = v_severity_1820_;
goto v___jp_1923_;
}
else
{
v___y_1924_ = v___y_1942_;
v___y_1925_ = v___x_1940_;
goto v___jp_1923_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_1956_, lean_object* v_msgData_1957_, lean_object* v_severity_1958_, lean_object* v_isSilent_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
uint8_t v_severity_boxed_1963_; uint8_t v_isSilent_boxed_1964_; lean_object* v_res_1965_; 
v_severity_boxed_1963_ = lean_unbox(v_severity_1958_);
v_isSilent_boxed_1964_ = lean_unbox(v_isSilent_1959_);
v_res_1965_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1(v_ref_1956_, v_msgData_1957_, v_severity_boxed_1963_, v_isSilent_boxed_1964_, v___y_1960_, v___y_1961_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v_ref_1956_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0(lean_object* v_ref_1966_, lean_object* v_msgData_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
uint8_t v___x_1971_; uint8_t v___x_1972_; lean_object* v___x_1973_; 
v___x_1971_ = 1;
v___x_1972_ = 0;
v___x_1973_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1(v_ref_1966_, v_msgData_1967_, v___x_1971_, v___x_1972_, v___y_1968_, v___y_1969_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0___boxed(lean_object* v_ref_1974_, lean_object* v_msgData_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0(v_ref_1974_, v_msgData_1975_, v___y_1976_, v___y_1977_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v_ref_1974_);
return v_res_1979_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1981_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__0));
v___x_1982_ = l_Lean_stringToMessageData(v___x_1981_);
return v___x_1982_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1984_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__2));
v___x_1985_ = l_Lean_stringToMessageData(v___x_1984_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0(lean_object* v_linterOption_1986_, lean_object* v_stx_1987_, lean_object* v_msg_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
lean_object* v_name_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2010_; 
v_name_1992_ = lean_ctor_get(v_linterOption_1986_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v_linterOption_1986_);
if (v_isSharedCheck_2010_ == 0)
{
lean_object* v_unused_2011_; 
v_unused_2011_ = lean_ctor_get(v_linterOption_1986_, 1);
lean_dec(v_unused_2011_);
v___x_1994_ = v_linterOption_1986_;
v_isShared_1995_ = v_isSharedCheck_2010_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_name_1992_);
lean_dec(v_linterOption_1986_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2010_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1999_; 
v___x_1996_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__1);
lean_inc(v_name_1992_);
v___x_1997_ = l_Lean_MessageData_ofName(v_name_1992_);
if (v_isShared_1995_ == 0)
{
lean_ctor_set_tag(v___x_1994_, 7);
lean_ctor_set(v___x_1994_, 1, v___x_1997_);
lean_ctor_set(v___x_1994_, 0, v___x_1996_);
v___x_1999_ = v___x_1994_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_1996_);
lean_ctor_set(v_reuseFailAlloc_2009_, 1, v___x_1997_);
v___x_1999_ = v_reuseFailAlloc_2009_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v_disable_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2000_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__3);
v___x_2001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_1999_);
lean_ctor_set(v___x_2001_, 1, v___x_2000_);
v_disable_2002_ = l_Lean_MessageData_note(v___x_2001_);
v___x_2003_ = l_Lean_Linter_linterMessageTag;
v___x_2004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2004_, 0, v_msg_1988_);
lean_ctor_set(v___x_2004_, 1, v_disable_2002_);
v___x_2005_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2005_, 0, v___x_2003_);
lean_ctor_set(v___x_2005_, 1, v___x_2004_);
v___x_2006_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2006_, 0, v_name_1992_);
lean_ctor_set(v___x_2006_, 1, v___x_2005_);
lean_inc(v_stx_1987_);
v___x_2007_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2007_, 0, v_stx_1987_);
lean_ctor_set(v___x_2007_, 1, v___x_2006_);
v___x_2008_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0(v_stx_1987_, v___x_2007_, v___y_1989_, v___y_1990_);
lean_dec(v_stx_1987_);
return v___x_2008_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___boxed(lean_object* v_linterOption_2012_, lean_object* v_stx_2013_, lean_object* v_msg_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0(v_linterOption_2012_, v_stx_2013_, v_msg_2014_, v___y_2015_, v___y_2016_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
return v_res_2018_;
}
}
static lean_object* _init_l_Lean_Linter_MissingDocs_lint___closed__1(void){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lint___closed__0));
v___x_2021_ = l_Lean_stringToMessageData(v___x_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lint(lean_object* v_stx_2022_, lean_object* v_msg_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_){
_start:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2027_ = l_Lean_Linter_linter_missingDocs;
v___x_2028_ = lean_obj_once(&l_Lean_Linter_MissingDocs_lint___closed__1, &l_Lean_Linter_MissingDocs_lint___closed__1_once, _init_l_Lean_Linter_MissingDocs_lint___closed__1);
v___x_2029_ = l_Lean_stringToMessageData(v_msg_2023_);
v___x_2030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2028_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
v___x_2031_ = l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0(v___x_2027_, v_stx_2022_, v___x_2030_, v_a_2024_, v_a_2025_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lint___boxed(lean_object* v_stx_2032_, lean_object* v_msg_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l_Lean_Linter_MissingDocs_lint(v_stx_2032_, v_msg_2033_, v_a_2034_, v_a_2035_);
lean_dec(v_a_2035_);
lean_dec_ref(v_a_2034_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v___x_2042_; 
v___x_2042_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2___redArg(v_msgData_2038_, v___y_2040_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2(v_msgData_2043_, v___y_2044_, v___y_2045_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
return v_res_2047_;
}
}
static lean_object* _init_l_Lean_Linter_MissingDocs_lintEmpty___closed__1(void){
_start:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2049_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintEmpty___closed__0));
v___x_2050_ = l_Lean_stringToMessageData(v___x_2049_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintEmpty(lean_object* v_stx_2051_, lean_object* v_msg_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2056_ = l_Lean_Linter_linter_missingDocs;
v___x_2057_ = lean_obj_once(&l_Lean_Linter_MissingDocs_lintEmpty___closed__1, &l_Lean_Linter_MissingDocs_lintEmpty___closed__1_once, _init_l_Lean_Linter_MissingDocs_lintEmpty___closed__1);
v___x_2058_ = l_Lean_stringToMessageData(v_msg_2052_);
v___x_2059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2057_);
lean_ctor_set(v___x_2059_, 1, v___x_2058_);
v___x_2060_ = l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0(v___x_2056_, v_stx_2051_, v___x_2059_, v_a_2053_, v_a_2054_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintEmpty___boxed(lean_object* v_stx_2061_, lean_object* v_msg_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Lean_Linter_MissingDocs_lintEmpty(v_stx_2061_, v_msg_2062_, v_a_2063_, v_a_2064_);
lean_dec(v_a_2064_);
lean_dec_ref(v_a_2063_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintNamed(lean_object* v_stx_2067_, lean_object* v_msg_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_){
_start:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2072_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__13));
v___x_2073_ = lean_string_append(v_msg_2068_, v___x_2072_);
v___x_2074_ = l_Lean_Syntax_getId(v_stx_2067_);
v___x_2075_ = 1;
v___x_2076_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2074_, v___x_2075_);
v___x_2077_ = lean_string_append(v___x_2073_, v___x_2076_);
lean_dec_ref(v___x_2076_);
v___x_2078_ = l_Lean_Linter_MissingDocs_lint(v_stx_2067_, v___x_2077_, v_a_2069_, v_a_2070_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintNamed___boxed(lean_object* v_stx_2079_, lean_object* v_msg_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_Lean_Linter_MissingDocs_lintNamed(v_stx_2079_, v_msg_2080_, v_a_2081_, v_a_2082_);
lean_dec(v_a_2082_);
lean_dec_ref(v_a_2081_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintEmptyNamed(lean_object* v_stx_2085_, lean_object* v_msg_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_){
_start:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; uint8_t v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2090_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__13));
v___x_2091_ = lean_string_append(v_msg_2086_, v___x_2090_);
v___x_2092_ = l_Lean_Syntax_getId(v_stx_2085_);
v___x_2093_ = 1;
v___x_2094_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2092_, v___x_2093_);
v___x_2095_ = lean_string_append(v___x_2091_, v___x_2094_);
lean_dec_ref(v___x_2094_);
v___x_2096_ = l_Lean_Linter_MissingDocs_lintEmpty(v_stx_2085_, v___x_2095_, v_a_2087_, v_a_2088_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintEmptyNamed___boxed(lean_object* v_stx_2097_, lean_object* v_msg_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l_Lean_Linter_MissingDocs_lintEmptyNamed(v_stx_2097_, v_msg_2098_, v_a_2099_, v_a_2100_);
lean_dec(v_a_2100_);
lean_dec_ref(v_a_2099_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintField(lean_object* v_parent_2104_, lean_object* v_stx_2105_, lean_object* v_msg_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2110_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__13));
v___x_2111_ = lean_string_append(v_msg_2106_, v___x_2110_);
v___x_2112_ = l_Lean_Syntax_getId(v_parent_2104_);
v___x_2113_ = 1;
v___x_2114_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2112_, v___x_2113_);
v___x_2115_ = lean_string_append(v___x_2111_, v___x_2114_);
lean_dec_ref(v___x_2114_);
v___x_2116_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintField___closed__0));
v___x_2117_ = lean_string_append(v___x_2115_, v___x_2116_);
v___x_2118_ = l_Lean_Syntax_getId(v_stx_2105_);
v___x_2119_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2118_, v___x_2113_);
v___x_2120_ = lean_string_append(v___x_2117_, v___x_2119_);
lean_dec_ref(v___x_2119_);
v___x_2121_ = l_Lean_Linter_MissingDocs_lint(v_stx_2105_, v___x_2120_, v_a_2107_, v_a_2108_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintField___boxed(lean_object* v_parent_2122_, lean_object* v_stx_2123_, lean_object* v_msg_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_Lean_Linter_MissingDocs_lintField(v_parent_2122_, v_stx_2123_, v_msg_2124_, v_a_2125_, v_a_2126_);
lean_dec(v_a_2126_);
lean_dec_ref(v_a_2125_);
lean_dec(v_parent_2122_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintEmptyField(lean_object* v_parent_2129_, lean_object* v_stx_2130_, lean_object* v_msg_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_){
_start:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; uint8_t v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2135_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__13));
v___x_2136_ = lean_string_append(v_msg_2131_, v___x_2135_);
v___x_2137_ = l_Lean_Syntax_getId(v_parent_2129_);
v___x_2138_ = 1;
v___x_2139_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2137_, v___x_2138_);
v___x_2140_ = lean_string_append(v___x_2136_, v___x_2139_);
lean_dec_ref(v___x_2139_);
v___x_2141_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintField___closed__0));
v___x_2142_ = lean_string_append(v___x_2140_, v___x_2141_);
v___x_2143_ = l_Lean_Syntax_getId(v_stx_2130_);
v___x_2144_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2143_, v___x_2138_);
v___x_2145_ = lean_string_append(v___x_2142_, v___x_2144_);
lean_dec_ref(v___x_2144_);
v___x_2146_ = l_Lean_Linter_MissingDocs_lintEmpty(v_stx_2130_, v___x_2145_, v_a_2132_, v_a_2133_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintEmptyField___boxed(lean_object* v_parent_2147_, lean_object* v_stx_2148_, lean_object* v_msg_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_Lean_Linter_MissingDocs_lintEmptyField(v_parent_2147_, v_stx_2148_, v_msg_2149_, v_a_2150_, v_a_2151_);
lean_dec(v_a_2151_);
lean_dec_ref(v_a_2150_);
lean_dec(v_parent_2147_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintStructField(lean_object* v_parent_2154_, lean_object* v_stx_2155_, lean_object* v_msg_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; uint8_t v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2160_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__13));
v___x_2161_ = lean_string_append(v_msg_2156_, v___x_2160_);
v___x_2162_ = l_Lean_Syntax_getId(v_parent_2154_);
v___x_2163_ = 1;
v___x_2164_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2162_, v___x_2163_);
v___x_2165_ = lean_string_append(v___x_2161_, v___x_2164_);
lean_dec_ref(v___x_2164_);
v___x_2166_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintField___closed__0));
v___x_2167_ = lean_string_append(v___x_2165_, v___x_2166_);
v___x_2168_ = l_Lean_Syntax_getId(v_stx_2155_);
v___x_2169_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2168_, v___x_2163_);
v___x_2170_ = lean_string_append(v___x_2167_, v___x_2169_);
lean_dec_ref(v___x_2169_);
v___x_2171_ = l_Lean_Linter_MissingDocs_lint(v_stx_2155_, v___x_2170_, v_a_2157_, v_a_2158_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintStructField___boxed(lean_object* v_parent_2172_, lean_object* v_stx_2173_, lean_object* v_msg_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Lean_Linter_MissingDocs_lintStructField(v_parent_2172_, v_stx_2173_, v_msg_2174_, v_a_2175_, v_a_2176_);
lean_dec(v_a_2176_);
lean_dec_ref(v_a_2175_);
lean_dec(v_parent_2172_);
return v_res_2178_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2179_ = lean_box(1);
v___x_2180_ = l_Lean_MessageData_ofFormat(v___x_2179_);
return v___x_2180_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2184_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__2));
v___x_2185_ = l_Lean_MessageData_ofFormat(v___x_2184_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_x_2186_, lean_object* v_x_2187_){
_start:
{
if (lean_obj_tag(v_x_2187_) == 0)
{
return v_x_2186_;
}
else
{
lean_object* v_head_2188_; lean_object* v_tail_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2211_; 
v_head_2188_ = lean_ctor_get(v_x_2187_, 0);
v_tail_2189_ = lean_ctor_get(v_x_2187_, 1);
v_isSharedCheck_2211_ = !lean_is_exclusive(v_x_2187_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2191_ = v_x_2187_;
v_isShared_2192_ = v_isSharedCheck_2211_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_tail_2189_);
lean_inc(v_head_2188_);
lean_dec(v_x_2187_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2211_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v_before_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2209_; 
v_before_2193_ = lean_ctor_get(v_head_2188_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v_head_2188_);
if (v_isSharedCheck_2209_ == 0)
{
lean_object* v_unused_2210_; 
v_unused_2210_ = lean_ctor_get(v_head_2188_, 1);
lean_dec(v_unused_2210_);
v___x_2195_ = v_head_2188_;
v_isShared_2196_ = v_isSharedCheck_2209_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_before_2193_);
lean_dec(v_head_2188_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2209_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2197_; lean_object* v___x_2199_; 
v___x_2197_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__0);
if (v_isShared_2196_ == 0)
{
lean_ctor_set_tag(v___x_2195_, 7);
lean_ctor_set(v___x_2195_, 1, v___x_2197_);
lean_ctor_set(v___x_2195_, 0, v_x_2186_);
v___x_2199_ = v___x_2195_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_x_2186_);
lean_ctor_set(v_reuseFailAlloc_2208_, 1, v___x_2197_);
v___x_2199_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
lean_object* v___x_2200_; lean_object* v___x_2202_; 
v___x_2200_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__3);
if (v_isShared_2192_ == 0)
{
lean_ctor_set_tag(v___x_2191_, 7);
lean_ctor_set(v___x_2191_, 1, v___x_2200_);
lean_ctor_set(v___x_2191_, 0, v___x_2199_);
v___x_2202_ = v___x_2191_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v___x_2199_);
lean_ctor_set(v_reuseFailAlloc_2207_, 1, v___x_2200_);
v___x_2202_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2203_ = l_Lean_MessageData_ofSyntax(v_before_2193_);
v___x_2204_ = l_Lean_indentD(v___x_2203_);
v___x_2205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2202_);
lean_ctor_set(v___x_2205_, 1, v___x_2204_);
v_x_2186_ = v___x_2205_;
v_x_2187_ = v_tail_2189_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2215_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg___closed__1));
v___x_2216_ = l_Lean_MessageData_ofFormat(v___x_2215_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_msgData_2217_, lean_object* v_macroStack_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v_scopes_2223_; lean_object* v___x_2224_; lean_object* v_opts_2225_; lean_object* v___x_2226_; uint8_t v___x_2227_; 
v___x_2221_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2222_ = lean_st_ref_get(v___y_2219_);
v_scopes_2223_ = lean_ctor_get(v___x_2222_, 2);
lean_inc(v_scopes_2223_);
lean_dec(v___x_2222_);
v___x_2224_ = l_List_head_x21___redArg(v___x_2221_, v_scopes_2223_);
lean_dec(v_scopes_2223_);
v_opts_2225_ = lean_ctor_get(v___x_2224_, 1);
lean_inc_ref(v_opts_2225_);
lean_dec(v___x_2224_);
v___x_2226_ = l_Lean_Elab_pp_macroStack;
v___x_2227_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__3(v_opts_2225_, v___x_2226_);
lean_dec_ref(v_opts_2225_);
if (v___x_2227_ == 0)
{
lean_object* v___x_2228_; 
lean_dec(v_macroStack_2218_);
v___x_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2228_, 0, v_msgData_2217_);
return v___x_2228_;
}
else
{
if (lean_obj_tag(v_macroStack_2218_) == 0)
{
lean_object* v___x_2229_; 
v___x_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2229_, 0, v_msgData_2217_);
return v___x_2229_;
}
else
{
lean_object* v_head_2230_; lean_object* v_after_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2246_; 
v_head_2230_ = lean_ctor_get(v_macroStack_2218_, 0);
lean_inc(v_head_2230_);
v_after_2231_ = lean_ctor_get(v_head_2230_, 1);
v_isSharedCheck_2246_ = !lean_is_exclusive(v_head_2230_);
if (v_isSharedCheck_2246_ == 0)
{
lean_object* v_unused_2247_; 
v_unused_2247_ = lean_ctor_get(v_head_2230_, 0);
lean_dec(v_unused_2247_);
v___x_2233_ = v_head_2230_;
v_isShared_2234_ = v_isSharedCheck_2246_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_after_2231_);
lean_dec(v_head_2230_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2246_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2235_; lean_object* v___x_2237_; 
v___x_2235_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__0);
if (v_isShared_2234_ == 0)
{
lean_ctor_set_tag(v___x_2233_, 7);
lean_ctor_set(v___x_2233_, 1, v___x_2235_);
lean_ctor_set(v___x_2233_, 0, v_msgData_2217_);
v___x_2237_ = v___x_2233_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_msgData_2217_);
lean_ctor_set(v_reuseFailAlloc_2245_, 1, v___x_2235_);
v___x_2237_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v_msgData_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2238_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg___closed__2);
v___x_2239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2237_);
lean_ctor_set(v___x_2239_, 1, v___x_2238_);
v___x_2240_ = l_Lean_MessageData_ofSyntax(v_after_2231_);
v___x_2241_ = l_Lean_indentD(v___x_2240_);
v_msgData_2242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2242_, 0, v___x_2239_);
lean_ctor_set(v_msgData_2242_, 1, v___x_2241_);
v___x_2243_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3(v_msgData_2242_, v_macroStack_2218_);
v___x_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2243_);
return v___x_2244_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_2248_, lean_object* v_macroStack_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg(v_msgData_2248_, v_macroStack_2249_, v___y_2250_);
lean_dec(v___y_2250_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v___x_2257_; 
v___x_2257_ = l_Lean_Elab_Command_getRef___redArg(v___y_2254_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_a_2258_; lean_object* v_macroStack_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v_a_2262_; lean_object* v___x_2263_; lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2272_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_a_2258_);
lean_dec_ref_known(v___x_2257_, 1);
v_macroStack_2259_ = lean_ctor_get(v___y_2254_, 4);
v___x_2260_ = l_Lean_Elab_getBetterRef(v_a_2258_, v_macroStack_2259_);
lean_dec(v_a_2258_);
v___x_2261_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_2253_, v___y_2255_);
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
lean_inc(v_a_2262_);
lean_dec_ref(v___x_2261_);
lean_inc(v_macroStack_2259_);
v___x_2263_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg(v_a_2262_, v_macroStack_2259_, v___y_2255_);
v_a_2264_ = lean_ctor_get(v___x_2263_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2266_ = v___x_2263_;
v_isShared_2267_ = v_isSharedCheck_2272_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2263_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2272_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2268_; lean_object* v___x_2270_; 
v___x_2268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2260_);
lean_ctor_set(v___x_2268_, 1, v_a_2264_);
if (v_isShared_2267_ == 0)
{
lean_ctor_set_tag(v___x_2266_, 1);
lean_ctor_set(v___x_2266_, 0, v___x_2268_);
v___x_2270_ = v___x_2266_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v___x_2268_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
else
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
lean_dec_ref(v_msg_2253_);
v_a_2273_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2257_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2257_);
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
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg(v_msg_2281_, v___y_2282_, v___y_2283_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0___redArg(lean_object* v_ref_2286_, lean_object* v_msg_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v___x_2291_; 
v___x_2291_ = l_Lean_Elab_Command_getRef___redArg(v___y_2288_);
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_object* v_a_2292_; lean_object* v_fileName_2293_; lean_object* v_fileMap_2294_; lean_object* v_currRecDepth_2295_; lean_object* v_cmdPos_2296_; lean_object* v_macroStack_2297_; lean_object* v_quotContext_x3f_2298_; lean_object* v_currMacroScope_2299_; lean_object* v_snap_x3f_2300_; lean_object* v_cancelTk_x3f_2301_; uint8_t v_suppressElabErrors_2302_; lean_object* v_ref_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
lean_inc(v_a_2292_);
lean_dec_ref_known(v___x_2291_, 1);
v_fileName_2293_ = lean_ctor_get(v___y_2288_, 0);
v_fileMap_2294_ = lean_ctor_get(v___y_2288_, 1);
v_currRecDepth_2295_ = lean_ctor_get(v___y_2288_, 2);
v_cmdPos_2296_ = lean_ctor_get(v___y_2288_, 3);
v_macroStack_2297_ = lean_ctor_get(v___y_2288_, 4);
v_quotContext_x3f_2298_ = lean_ctor_get(v___y_2288_, 5);
v_currMacroScope_2299_ = lean_ctor_get(v___y_2288_, 6);
v_snap_x3f_2300_ = lean_ctor_get(v___y_2288_, 8);
v_cancelTk_x3f_2301_ = lean_ctor_get(v___y_2288_, 9);
v_suppressElabErrors_2302_ = lean_ctor_get_uint8(v___y_2288_, sizeof(void*)*10);
v_ref_2303_ = l_Lean_replaceRef(v_ref_2286_, v_a_2292_);
lean_dec(v_a_2292_);
lean_inc(v_cancelTk_x3f_2301_);
lean_inc(v_snap_x3f_2300_);
lean_inc(v_currMacroScope_2299_);
lean_inc(v_quotContext_x3f_2298_);
lean_inc(v_macroStack_2297_);
lean_inc(v_cmdPos_2296_);
lean_inc(v_currRecDepth_2295_);
lean_inc_ref(v_fileMap_2294_);
lean_inc_ref(v_fileName_2293_);
v___x_2304_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_2304_, 0, v_fileName_2293_);
lean_ctor_set(v___x_2304_, 1, v_fileMap_2294_);
lean_ctor_set(v___x_2304_, 2, v_currRecDepth_2295_);
lean_ctor_set(v___x_2304_, 3, v_cmdPos_2296_);
lean_ctor_set(v___x_2304_, 4, v_macroStack_2297_);
lean_ctor_set(v___x_2304_, 5, v_quotContext_x3f_2298_);
lean_ctor_set(v___x_2304_, 6, v_currMacroScope_2299_);
lean_ctor_set(v___x_2304_, 7, v_ref_2303_);
lean_ctor_set(v___x_2304_, 8, v_snap_x3f_2300_);
lean_ctor_set(v___x_2304_, 9, v_cancelTk_x3f_2301_);
lean_ctor_set_uint8(v___x_2304_, sizeof(void*)*10, v_suppressElabErrors_2302_);
v___x_2305_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg(v_msg_2287_, v___x_2304_, v___y_2289_);
lean_dec_ref_known(v___x_2304_, 10);
return v___x_2305_;
}
else
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2313_; 
lean_dec_ref(v_msg_2287_);
v_a_2306_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2308_ = v___x_2291_;
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2291_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_a_2306_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0___redArg___boxed(lean_object* v_ref_2314_, lean_object* v_msg_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0___redArg(v_ref_2314_, v_msg_2315_, v___y_2316_, v___y_2317_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec(v_ref_2314_);
return v_res_2319_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2321_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__0));
v___x_2322_ = l_Lean_stringToMessageData(v___x_2321_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0(lean_object* v_stx_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2336_ = lean_unsigned_to_nat(1u);
v___x_2337_ = l_Lean_Syntax_getArg(v_stx_2326_, v___x_2336_);
if (lean_obj_tag(v___x_2337_) == 1)
{
lean_object* v_kind_2338_; 
v_kind_2338_ = lean_ctor_get(v___x_2337_, 1);
lean_inc(v_kind_2338_);
if (lean_obj_tag(v_kind_2338_) == 1)
{
lean_object* v_pre_2339_; 
v_pre_2339_ = lean_ctor_get(v_kind_2338_, 0);
lean_inc(v_pre_2339_);
if (lean_obj_tag(v_pre_2339_) == 1)
{
lean_object* v_pre_2340_; 
v_pre_2340_ = lean_ctor_get(v_pre_2339_, 0);
lean_inc(v_pre_2340_);
if (lean_obj_tag(v_pre_2340_) == 1)
{
lean_object* v_pre_2341_; 
v_pre_2341_ = lean_ctor_get(v_pre_2340_, 0);
lean_inc(v_pre_2341_);
if (lean_obj_tag(v_pre_2341_) == 1)
{
lean_object* v_pre_2342_; 
v_pre_2342_ = lean_ctor_get(v_pre_2341_, 0);
if (lean_obj_tag(v_pre_2342_) == 0)
{
lean_object* v_args_2343_; lean_object* v_str_2344_; lean_object* v_str_2345_; lean_object* v_str_2346_; lean_object* v_str_2347_; lean_object* v___x_2348_; uint8_t v___x_2349_; 
v_args_2343_ = lean_ctor_get(v___x_2337_, 2);
lean_inc_ref(v_args_2343_);
lean_dec_ref_known(v___x_2337_, 3);
v_str_2344_ = lean_ctor_get(v_kind_2338_, 1);
lean_inc_ref(v_str_2344_);
lean_dec_ref_known(v_kind_2338_, 2);
v_str_2345_ = lean_ctor_get(v_pre_2339_, 1);
lean_inc_ref(v_str_2345_);
lean_dec_ref_known(v_pre_2339_, 2);
v_str_2346_ = lean_ctor_get(v_pre_2340_, 1);
lean_inc_ref(v_str_2346_);
lean_dec_ref_known(v_pre_2340_, 2);
v_str_2347_ = lean_ctor_get(v_pre_2341_, 1);
lean_inc_ref(v_str_2347_);
lean_dec_ref_known(v_pre_2341_, 2);
v___x_2348_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_));
v___x_2349_ = lean_string_dec_eq(v_str_2347_, v___x_2348_);
lean_dec_ref(v_str_2347_);
if (v___x_2349_ == 0)
{
lean_dec_ref(v_str_2346_);
lean_dec_ref(v_str_2345_);
lean_dec_ref(v_str_2344_);
lean_dec_ref(v_args_2343_);
goto v___jp_2330_;
}
else
{
lean_object* v___x_2350_; uint8_t v___x_2351_; 
v___x_2350_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2));
v___x_2351_ = lean_string_dec_eq(v_str_2346_, v___x_2350_);
lean_dec_ref(v_str_2346_);
if (v___x_2351_ == 0)
{
lean_dec_ref(v_str_2345_);
lean_dec_ref(v_str_2344_);
lean_dec_ref(v_args_2343_);
goto v___jp_2330_;
}
else
{
lean_object* v___x_2352_; uint8_t v___x_2353_; 
v___x_2352_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3));
v___x_2353_ = lean_string_dec_eq(v_str_2345_, v___x_2352_);
lean_dec_ref(v_str_2345_);
if (v___x_2353_ == 0)
{
lean_dec_ref(v_str_2344_);
lean_dec_ref(v_args_2343_);
goto v___jp_2330_;
}
else
{
lean_object* v___x_2354_; uint8_t v___x_2355_; 
v___x_2354_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__4));
v___x_2355_ = lean_string_dec_eq(v_str_2344_, v___x_2354_);
lean_dec_ref(v_str_2344_);
if (v___x_2355_ == 0)
{
lean_dec_ref(v_args_2343_);
goto v___jp_2330_;
}
else
{
lean_object* v___x_2356_; lean_object* v___x_2357_; uint8_t v___x_2358_; 
v___x_2356_ = lean_array_get_size(v_args_2343_);
v___x_2357_ = lean_unsigned_to_nat(2u);
v___x_2358_ = lean_nat_dec_eq(v___x_2356_, v___x_2357_);
if (v___x_2358_ == 0)
{
lean_dec_ref(v_args_2343_);
goto v___jp_2330_;
}
else
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2359_ = lean_unsigned_to_nat(0u);
v___x_2360_ = lean_array_fget(v_args_2343_, v___x_2359_);
lean_dec_ref(v_args_2343_);
if (lean_obj_tag(v___x_2360_) == 2)
{
lean_object* v_val_2361_; lean_object* v___x_2362_; 
lean_dec(v_stx_2326_);
v_val_2361_ = lean_ctor_get(v___x_2360_, 1);
lean_inc_ref(v_val_2361_);
lean_dec_ref_known(v___x_2360_, 2);
v___x_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2362_, 0, v_val_2361_);
return v___x_2362_;
}
else
{
lean_dec(v___x_2360_);
goto v___jp_2330_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_2341_, 2);
lean_dec_ref_known(v_pre_2340_, 2);
lean_dec_ref_known(v_pre_2339_, 2);
lean_dec_ref_known(v_kind_2338_, 2);
lean_dec_ref_known(v___x_2337_, 3);
goto v___jp_2330_;
}
}
else
{
lean_dec_ref_known(v_pre_2340_, 2);
lean_dec(v_pre_2341_);
lean_dec_ref_known(v_pre_2339_, 2);
lean_dec_ref_known(v_kind_2338_, 2);
lean_dec_ref_known(v___x_2337_, 3);
goto v___jp_2330_;
}
}
else
{
lean_dec(v_pre_2340_);
lean_dec_ref_known(v_pre_2339_, 2);
lean_dec_ref_known(v_kind_2338_, 2);
lean_dec_ref_known(v___x_2337_, 3);
goto v___jp_2330_;
}
}
else
{
lean_dec_ref_known(v_kind_2338_, 2);
lean_dec(v_pre_2339_);
lean_dec_ref_known(v___x_2337_, 3);
goto v___jp_2330_;
}
}
else
{
lean_dec(v_kind_2338_);
lean_dec_ref_known(v___x_2337_, 3);
goto v___jp_2330_;
}
}
else
{
lean_dec(v___x_2337_);
goto v___jp_2330_;
}
v___jp_2330_:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2331_ = lean_obj_once(&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__1, &l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__1_once, _init_l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__1);
lean_inc(v_stx_2326_);
v___x_2332_ = l_Lean_MessageData_ofSyntax(v_stx_2326_);
v___x_2333_ = l_Lean_indentD(v___x_2332_);
v___x_2334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2331_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
v___x_2335_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0___redArg(v_stx_2326_, v___x_2334_, v___y_2327_, v___y_2328_);
lean_dec(v_stx_2326_);
return v___x_2335_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___boxed(lean_object* v_stx_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0(v_stx_2363_, v___y_2364_, v___y_2365_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString(lean_object* v_docOpt_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_){
_start:
{
uint8_t v___x_2373_; 
v___x_2373_ = l_Lean_Syntax_isNone(v_docOpt_2369_);
if (v___x_2373_ == 0)
{
lean_object* v___x_2374_; lean_object* v_docStx_2375_; lean_object* v___y_2377_; lean_object* v___y_2378_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2374_ = lean_unsigned_to_nat(0u);
v_docStx_2375_ = l_Lean_Syntax_getArg(v_docOpt_2369_, v___x_2374_);
v___x_2404_ = lean_unsigned_to_nat(1u);
v___x_2405_ = l_Lean_Syntax_getArg(v_docStx_2375_, v___x_2404_);
if (lean_obj_tag(v___x_2405_) == 1)
{
lean_object* v_kind_2406_; 
v_kind_2406_ = lean_ctor_get(v___x_2405_, 1);
if (lean_obj_tag(v_kind_2406_) == 1)
{
lean_object* v_pre_2407_; 
v_pre_2407_ = lean_ctor_get(v_kind_2406_, 0);
if (lean_obj_tag(v_pre_2407_) == 1)
{
lean_object* v_pre_2408_; 
v_pre_2408_ = lean_ctor_get(v_pre_2407_, 0);
if (lean_obj_tag(v_pre_2408_) == 1)
{
lean_object* v_pre_2409_; 
v_pre_2409_ = lean_ctor_get(v_pre_2408_, 0);
if (lean_obj_tag(v_pre_2409_) == 1)
{
lean_object* v_pre_2410_; 
v_pre_2410_ = lean_ctor_get(v_pre_2409_, 0);
if (lean_obj_tag(v_pre_2410_) == 0)
{
lean_object* v_str_2411_; lean_object* v_str_2412_; lean_object* v_str_2413_; lean_object* v_str_2414_; lean_object* v___x_2415_; uint8_t v___x_2416_; 
v_str_2411_ = lean_ctor_get(v_kind_2406_, 1);
v_str_2412_ = lean_ctor_get(v_pre_2407_, 1);
v_str_2413_ = lean_ctor_get(v_pre_2408_, 1);
v_str_2414_ = lean_ctor_get(v_pre_2409_, 1);
v___x_2415_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_));
v___x_2416_ = lean_string_dec_eq(v_str_2414_, v___x_2415_);
if (v___x_2416_ == 0)
{
lean_dec_ref_known(v___x_2405_, 3);
v___y_2377_ = v_a_2370_;
v___y_2378_ = v_a_2371_;
goto v___jp_2376_;
}
else
{
lean_object* v___x_2417_; uint8_t v___x_2418_; 
v___x_2417_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2));
v___x_2418_ = lean_string_dec_eq(v_str_2413_, v___x_2417_);
if (v___x_2418_ == 0)
{
lean_dec_ref_known(v___x_2405_, 3);
v___y_2377_ = v_a_2370_;
v___y_2378_ = v_a_2371_;
goto v___jp_2376_;
}
else
{
lean_object* v___x_2419_; uint8_t v___x_2420_; 
v___x_2419_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3));
v___x_2420_ = lean_string_dec_eq(v_str_2412_, v___x_2419_);
if (v___x_2420_ == 0)
{
lean_dec_ref_known(v___x_2405_, 3);
v___y_2377_ = v_a_2370_;
v___y_2378_ = v_a_2371_;
goto v___jp_2376_;
}
else
{
lean_object* v___x_2421_; uint8_t v___x_2422_; 
v___x_2421_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString___closed__0));
v___x_2422_ = lean_string_dec_eq(v_str_2411_, v___x_2421_);
if (v___x_2422_ == 0)
{
lean_dec_ref_known(v___x_2405_, 3);
v___y_2377_ = v_a_2370_;
v___y_2378_ = v_a_2371_;
goto v___jp_2376_;
}
else
{
lean_object* v___x_2423_; uint8_t v___x_2424_; 
v___x_2423_ = l_Lean_Syntax_getArg(v___x_2405_, v___x_2374_);
lean_dec_ref_known(v___x_2405_, 3);
v___x_2424_ = l_Lean_Syntax_isAtom(v___x_2423_);
lean_dec(v___x_2423_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
lean_dec(v_docStx_2375_);
v___x_2425_ = lean_box(v___x_2373_);
v___x_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2425_);
return v___x_2426_;
}
else
{
v___y_2377_ = v_a_2370_;
v___y_2378_ = v_a_2371_;
goto v___jp_2376_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_2405_, 3);
v___y_2377_ = v_a_2370_;
v___y_2378_ = v_a_2371_;
goto v___jp_2376_;
}
}
else
{
lean_dec_ref_known(v___x_2405_, 3);
v___y_2377_ = v_a_2370_;
v___y_2378_ = v_a_2371_;
goto v___jp_2376_;
}
}
else
{
lean_dec_ref_known(v___x_2405_, 3);
v___y_2377_ = v_a_2370_;
v___y_2378_ = v_a_2371_;
goto v___jp_2376_;
}
}
else
{
lean_dec_ref_known(v___x_2405_, 3);
v___y_2377_ = v_a_2370_;
v___y_2378_ = v_a_2371_;
goto v___jp_2376_;
}
}
else
{
lean_dec_ref_known(v___x_2405_, 3);
v___y_2377_ = v_a_2370_;
v___y_2378_ = v_a_2371_;
goto v___jp_2376_;
}
}
else
{
lean_dec(v___x_2405_);
v___y_2377_ = v_a_2370_;
v___y_2378_ = v_a_2371_;
goto v___jp_2376_;
}
v___jp_2376_:
{
lean_object* v___x_2379_; 
v___x_2379_ = l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0(v_docStx_2375_, v___y_2377_, v___y_2378_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2395_; 
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2382_ = v___x_2379_;
v_isShared_2383_ = v_isSharedCheck_2395_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2379_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2395_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v_startInclusive_2387_; lean_object* v_endExclusive_2388_; lean_object* v___x_2389_; uint8_t v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2393_; 
v___x_2384_ = lean_string_utf8_byte_size(v_a_2380_);
v___x_2385_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2385_, 0, v_a_2380_);
lean_ctor_set(v___x_2385_, 1, v___x_2374_);
lean_ctor_set(v___x_2385_, 2, v___x_2384_);
v___x_2386_ = l_String_Slice_trimAscii(v___x_2385_);
v_startInclusive_2387_ = lean_ctor_get(v___x_2386_, 1);
lean_inc(v_startInclusive_2387_);
v_endExclusive_2388_ = lean_ctor_get(v___x_2386_, 2);
lean_inc(v_endExclusive_2388_);
lean_dec_ref(v___x_2386_);
v___x_2389_ = lean_nat_sub(v_endExclusive_2388_, v_startInclusive_2387_);
lean_dec(v_startInclusive_2387_);
lean_dec(v_endExclusive_2388_);
v___x_2390_ = lean_nat_dec_eq(v___x_2389_, v___x_2374_);
lean_dec(v___x_2389_);
v___x_2391_ = lean_box(v___x_2390_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 0, v___x_2391_);
v___x_2393_ = v___x_2382_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v___x_2391_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
else
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2403_; 
v_a_2396_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2398_ = v___x_2379_;
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2379_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2399_ == 0)
{
v___x_2401_ = v___x_2398_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2396_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
}
else
{
uint8_t v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2427_ = 0;
v___x_2428_ = lean_box(v___x_2427_);
v___x_2429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2428_);
return v___x_2429_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString___boxed(lean_object* v_docOpt_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString(v_docOpt_2430_, v_a_2431_, v_a_2432_);
lean_dec(v_a_2432_);
lean_dec_ref(v_a_2431_);
lean_dec(v_docOpt_2430_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0(lean_object* v_00_u03b1_2435_, lean_object* v_ref_2436_, lean_object* v_msg_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v___x_2441_; 
v___x_2441_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0___redArg(v_ref_2436_, v_msg_2437_, v___y_2438_, v___y_2439_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2442_, lean_object* v_ref_2443_, lean_object* v_msg_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0(v_00_u03b1_2442_, v_ref_2443_, v_msg_2444_, v___y_2445_, v___y_2446_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v_ref_2443_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2449_, lean_object* v_msg_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg(v_msg_2450_, v___y_2451_, v___y_2452_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2455_, lean_object* v_msg_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1(v_00_u03b1_2455_, v_msg_2456_, v___y_2457_, v___y_2458_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_2461_, lean_object* v_macroStack_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v___x_2466_; 
v___x_2466_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg(v_msgData_2461_, v_macroStack_2462_, v___y_2464_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_2467_, lean_object* v_macroStack_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2(v_msgData_2467_, v_macroStack_2468_, v___y_2469_, v___y_2470_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_isMissingDoc(lean_object* v_docOpt_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_){
_start:
{
lean_object* v___x_2477_; 
v___x_2477_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString(v_docOpt_2473_, v_a_2474_, v_a_2475_);
if (lean_obj_tag(v___x_2477_) == 0)
{
uint8_t v___x_2478_; 
v___x_2478_ = l_Lean_Syntax_isNone(v_docOpt_2473_);
if (v___x_2478_ == 0)
{
return v___x_2477_;
}
else
{
lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2486_; 
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2486_ == 0)
{
lean_object* v_unused_2487_; 
v_unused_2487_ = lean_ctor_get(v___x_2477_, 0);
lean_dec(v_unused_2487_);
v___x_2480_ = v___x_2477_;
v_isShared_2481_ = v_isSharedCheck_2486_;
goto v_resetjp_2479_;
}
else
{
lean_dec(v___x_2477_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2486_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2482_; lean_object* v___x_2484_; 
v___x_2482_ = lean_box(v___x_2478_);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 0, v___x_2482_);
v___x_2484_ = v___x_2480_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v___x_2482_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
else
{
return v___x_2477_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_isMissingDoc___boxed(lean_object* v_docOpt_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l_Lean_Linter_MissingDocs_isMissingDoc(v_docOpt_2488_, v_a_2489_, v_a_2490_);
lean_dec(v_a_2490_);
lean_dec_ref(v_a_2489_);
lean_dec(v_docOpt_2488_);
return v_res_2492_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0(lean_object* v_as_2503_, size_t v_i_2504_, size_t v_stop_2505_){
_start:
{
uint8_t v___x_2510_; 
v___x_2510_ = lean_usize_dec_eq(v_i_2504_, v_stop_2505_);
if (v___x_2510_ == 0)
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; uint8_t v___x_2515_; 
v___x_2511_ = lean_unsigned_to_nat(1u);
v___x_2512_ = lean_array_uget_borrowed(v_as_2503_, v_i_2504_);
v___x_2513_ = l_Lean_Syntax_getArg(v___x_2512_, v___x_2511_);
v___x_2514_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__2));
lean_inc(v___x_2513_);
v___x_2515_ = l_Lean_Syntax_isOfKind(v___x_2513_, v___x_2514_);
if (v___x_2515_ == 0)
{
lean_dec(v___x_2513_);
goto v___jp_2506_;
}
else
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; uint8_t v___x_2521_; 
v___x_2516_ = lean_unsigned_to_nat(0u);
v___x_2517_ = l_Lean_Syntax_getArg(v___x_2513_, v___x_2516_);
lean_dec(v___x_2513_);
v___x_2518_ = l_Lean_Syntax_getId(v___x_2517_);
lean_dec(v___x_2517_);
v___x_2519_ = l_Lean_Name_eraseMacroScopes(v___x_2518_);
lean_dec(v___x_2518_);
v___x_2520_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__4));
v___x_2521_ = lean_name_eq(v___x_2519_, v___x_2520_);
lean_dec(v___x_2519_);
if (v___x_2521_ == 0)
{
goto v___jp_2506_;
}
else
{
return v___x_2521_;
}
}
}
else
{
uint8_t v___x_2522_; 
v___x_2522_ = 0;
return v___x_2522_;
}
v___jp_2506_:
{
size_t v___x_2507_; size_t v___x_2508_; 
v___x_2507_ = ((size_t)1ULL);
v___x_2508_ = lean_usize_add(v_i_2504_, v___x_2507_);
v_i_2504_ = v___x_2508_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___boxed(lean_object* v_as_2523_, lean_object* v_i_2524_, lean_object* v_stop_2525_){
_start:
{
size_t v_i_boxed_2526_; size_t v_stop_boxed_2527_; uint8_t v_res_2528_; lean_object* v_r_2529_; 
v_i_boxed_2526_ = lean_unbox_usize(v_i_2524_);
lean_dec(v_i_2524_);
v_stop_boxed_2527_ = lean_unbox_usize(v_stop_2525_);
lean_dec(v_stop_2525_);
v_res_2528_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0(v_as_2523_, v_i_boxed_2526_, v_stop_boxed_2527_);
lean_dec_ref(v_as_2523_);
v_r_2529_ = lean_box(v_res_2528_);
return v_r_2529_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_MissingDocs_hasInheritDoc(lean_object* v_attrs_2530_){
_start:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; uint8_t v___x_2537_; 
v___x_2531_ = lean_unsigned_to_nat(0u);
v___x_2532_ = l_Lean_Syntax_getArg(v_attrs_2530_, v___x_2531_);
v___x_2533_ = lean_unsigned_to_nat(1u);
v___x_2534_ = l_Lean_Syntax_getArg(v___x_2532_, v___x_2533_);
lean_dec(v___x_2532_);
v___x_2535_ = l_Lean_Syntax_getSepArgs(v___x_2534_);
lean_dec(v___x_2534_);
v___x_2536_ = lean_array_get_size(v___x_2535_);
v___x_2537_ = lean_nat_dec_lt(v___x_2531_, v___x_2536_);
if (v___x_2537_ == 0)
{
lean_dec_ref(v___x_2535_);
return v___x_2537_;
}
else
{
if (v___x_2537_ == 0)
{
lean_dec_ref(v___x_2535_);
return v___x_2537_;
}
else
{
size_t v___x_2538_; size_t v___x_2539_; uint8_t v___x_2540_; 
v___x_2538_ = ((size_t)0ULL);
v___x_2539_ = lean_usize_of_nat(v___x_2536_);
v___x_2540_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0(v___x_2535_, v___x_2538_, v___x_2539_);
lean_dec_ref(v___x_2535_);
return v___x_2540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_hasInheritDoc___boxed(lean_object* v_attrs_2541_){
_start:
{
uint8_t v_res_2542_; lean_object* v_r_2543_; 
v_res_2542_ = l_Lean_Linter_MissingDocs_hasInheritDoc(v_attrs_2541_);
lean_dec(v_attrs_2541_);
v_r_2543_ = lean_box(v_res_2542_);
return v_r_2543_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0(lean_object* v_as_2550_, size_t v_i_2551_, size_t v_stop_2552_){
_start:
{
uint8_t v___x_2553_; 
v___x_2553_ = lean_usize_dec_eq(v_i_2551_, v_stop_2552_);
if (v___x_2553_ == 0)
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; uint8_t v___x_2558_; 
v___x_2554_ = lean_unsigned_to_nat(1u);
v___x_2555_ = lean_array_uget_borrowed(v_as_2550_, v_i_2551_);
v___x_2556_ = l_Lean_Syntax_getArg(v___x_2555_, v___x_2554_);
v___x_2557_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0___closed__1));
v___x_2558_ = l_Lean_Syntax_isOfKind(v___x_2556_, v___x_2557_);
if (v___x_2558_ == 0)
{
size_t v___x_2559_; size_t v___x_2560_; 
v___x_2559_ = ((size_t)1ULL);
v___x_2560_ = lean_usize_add(v_i_2551_, v___x_2559_);
v_i_2551_ = v___x_2560_;
goto _start;
}
else
{
return v___x_2558_;
}
}
else
{
uint8_t v___x_2562_; 
v___x_2562_ = 0;
return v___x_2562_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0___boxed(lean_object* v_as_2563_, lean_object* v_i_2564_, lean_object* v_stop_2565_){
_start:
{
size_t v_i_boxed_2566_; size_t v_stop_boxed_2567_; uint8_t v_res_2568_; lean_object* v_r_2569_; 
v_i_boxed_2566_ = lean_unbox_usize(v_i_2564_);
lean_dec(v_i_2564_);
v_stop_boxed_2567_ = lean_unbox_usize(v_stop_2565_);
lean_dec(v_stop_2565_);
v_res_2568_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0(v_as_2563_, v_i_boxed_2566_, v_stop_boxed_2567_);
lean_dec_ref(v_as_2563_);
v_r_2569_ = lean_box(v_res_2568_);
return v_r_2569_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_MissingDocs_hasTacticAlt(lean_object* v_attrs_2570_){
_start:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; uint8_t v___x_2577_; 
v___x_2571_ = lean_unsigned_to_nat(0u);
v___x_2572_ = l_Lean_Syntax_getArg(v_attrs_2570_, v___x_2571_);
v___x_2573_ = lean_unsigned_to_nat(1u);
v___x_2574_ = l_Lean_Syntax_getArg(v___x_2572_, v___x_2573_);
lean_dec(v___x_2572_);
v___x_2575_ = l_Lean_Syntax_getSepArgs(v___x_2574_);
lean_dec(v___x_2574_);
v___x_2576_ = lean_array_get_size(v___x_2575_);
v___x_2577_ = lean_nat_dec_lt(v___x_2571_, v___x_2576_);
if (v___x_2577_ == 0)
{
lean_dec_ref(v___x_2575_);
return v___x_2577_;
}
else
{
if (v___x_2577_ == 0)
{
lean_dec_ref(v___x_2575_);
return v___x_2577_;
}
else
{
size_t v___x_2578_; size_t v___x_2579_; uint8_t v___x_2580_; 
v___x_2578_ = ((size_t)0ULL);
v___x_2579_ = lean_usize_of_nat(v___x_2576_);
v___x_2580_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0(v___x_2575_, v___x_2578_, v___x_2579_);
lean_dec_ref(v___x_2575_);
return v___x_2580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_hasTacticAlt___boxed(lean_object* v_attrs_2581_){
_start:
{
uint8_t v_res_2582_; lean_object* v_r_2583_; 
v_res_2582_ = l_Lean_Linter_MissingDocs_hasTacticAlt(v_attrs_2581_);
lean_dec(v_attrs_2581_);
v_r_2583_ = lean_box(v_res_2582_);
return v_r_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_declModifiersDocStatus(lean_object* v_mods_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_){
_start:
{
lean_object* v___x_2598_; lean_object* v_env_2599_; lean_object* v___x_2600_; 
v___x_2598_ = lean_st_ref_get(v_a_2596_);
v_env_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc_ref(v_env_2599_);
lean_dec(v___x_2598_);
v___x_2600_ = l_Lean_Elab_Command_getScope___redArg(v_a_2596_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2664_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2603_ = v___x_2600_;
v_isShared_2604_ = v_isSharedCheck_2664_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_a_2601_);
lean_dec(v___x_2600_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2664_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
uint8_t v___y_2611_; lean_object* v___x_2654_; uint8_t v_isModule_2655_; 
v___x_2654_ = l_Lean_Environment_header(v_env_2599_);
lean_dec_ref(v_env_2599_);
v_isModule_2655_ = lean_ctor_get_uint8(v___x_2654_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_2654_);
if (v_isModule_2655_ == 0)
{
lean_dec(v_a_2601_);
goto v___jp_2645_;
}
else
{
uint8_t v_isPublic_2656_; 
v_isPublic_2656_ = lean_ctor_get_uint8(v_a_2601_, sizeof(void*)*10 + 1);
lean_dec(v_a_2601_);
if (v_isPublic_2656_ == 0)
{
lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; uint8_t v___x_2663_; 
v___x_2657_ = lean_unsigned_to_nat(2u);
v___x_2658_ = l_Lean_Syntax_getArg(v_mods_2594_, v___x_2657_);
v___x_2659_ = lean_unsigned_to_nat(0u);
v___x_2660_ = l_Lean_Syntax_getArg(v___x_2658_, v___x_2659_);
lean_dec(v___x_2658_);
v___x_2661_ = l_Lean_Syntax_getKind(v___x_2660_);
v___x_2662_ = ((lean_object*)(l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__1));
v___x_2663_ = lean_name_eq(v___x_2661_, v___x_2662_);
lean_dec(v___x_2661_);
if (v___x_2663_ == 0)
{
goto v___jp_2605_;
}
else
{
v___y_2611_ = v_isModule_2655_;
goto v___jp_2610_;
}
}
else
{
goto v___jp_2645_;
}
}
v___jp_2605_:
{
lean_object* v___x_2606_; lean_object* v___x_2608_; 
v___x_2606_ = lean_box(0);
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 0, v___x_2606_);
v___x_2608_ = v___x_2603_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v___x_2606_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
v___jp_2610_:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; uint8_t v___x_2614_; 
v___x_2612_ = lean_unsigned_to_nat(1u);
v___x_2613_ = l_Lean_Syntax_getArg(v_mods_2594_, v___x_2612_);
v___x_2614_ = l_Lean_Linter_MissingDocs_hasInheritDoc(v___x_2613_);
lean_dec(v___x_2613_);
if (v___x_2614_ == 0)
{
lean_object* v___x_2615_; lean_object* v___x_2616_; uint8_t v___x_2617_; 
lean_del_object(v___x_2603_);
v___x_2615_ = lean_unsigned_to_nat(0u);
v___x_2616_ = l_Lean_Syntax_getArg(v_mods_2594_, v___x_2615_);
v___x_2617_ = l_Lean_Syntax_isNone(v___x_2616_);
if (v___x_2617_ == 0)
{
lean_object* v___x_2618_; 
v___x_2618_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString(v___x_2616_, v_a_2595_, v_a_2596_);
lean_dec(v___x_2616_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2633_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2621_ = v___x_2618_;
v_isShared_2622_ = v_isSharedCheck_2633_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2618_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2633_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
uint8_t v___x_2623_; 
v___x_2623_ = lean_unbox(v_a_2619_);
lean_dec(v_a_2619_);
if (v___x_2623_ == 0)
{
lean_object* v___x_2624_; lean_object* v___x_2626_; 
v___x_2624_ = lean_box(0);
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 0, v___x_2624_);
v___x_2626_ = v___x_2621_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2624_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
else
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2631_; 
v___x_2628_ = lean_box(v___y_2611_);
v___x_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2628_);
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 0, v___x_2629_);
v___x_2631_ = v___x_2621_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v___x_2629_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
}
else
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2641_; 
v_a_2634_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2636_ = v___x_2618_;
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2618_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2639_; 
if (v_isShared_2637_ == 0)
{
v___x_2639_ = v___x_2636_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_a_2634_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
}
else
{
lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; 
lean_dec(v___x_2616_);
v___x_2642_ = lean_box(v___x_2614_);
v___x_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2643_, 0, v___x_2642_);
v___x_2644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2643_);
return v___x_2644_;
}
}
else
{
goto v___jp_2605_;
}
}
v___jp_2645_:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; uint8_t v___x_2652_; 
v___x_2646_ = lean_unsigned_to_nat(2u);
v___x_2647_ = l_Lean_Syntax_getArg(v_mods_2594_, v___x_2646_);
v___x_2648_ = lean_unsigned_to_nat(0u);
v___x_2649_ = l_Lean_Syntax_getArg(v___x_2647_, v___x_2648_);
lean_dec(v___x_2647_);
v___x_2650_ = l_Lean_Syntax_getKind(v___x_2649_);
v___x_2651_ = ((lean_object*)(l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__0));
v___x_2652_ = lean_name_eq(v___x_2650_, v___x_2651_);
lean_dec(v___x_2650_);
if (v___x_2652_ == 0)
{
uint8_t v___x_2653_; 
v___x_2653_ = 1;
v___y_2611_ = v___x_2653_;
goto v___jp_2610_;
}
else
{
goto v___jp_2605_;
}
}
}
}
else
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2672_; 
lean_dec_ref(v_env_2599_);
v_a_2665_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2667_ = v___x_2600_;
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2600_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2670_; 
if (v_isShared_2668_ == 0)
{
v___x_2670_ = v___x_2667_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_declModifiersDocStatus___boxed(lean_object* v_mods_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_){
_start:
{
lean_object* v_res_2677_; 
v_res_2677_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v_mods_2673_, v_a_2674_, v_a_2675_);
lean_dec(v_a_2675_);
lean_dec_ref(v_a_2674_);
lean_dec(v_mods_2673_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_declModifiersPubNoDoc(lean_object* v_mods_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_){
_start:
{
lean_object* v___x_2682_; 
v___x_2682_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v_mods_2678_, v_a_2679_, v_a_2680_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2697_; 
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2685_ = v___x_2682_;
v_isShared_2686_ = v_isSharedCheck_2697_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2682_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2697_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
if (lean_obj_tag(v_a_2683_) == 0)
{
uint8_t v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2690_; 
v___x_2687_ = 0;
v___x_2688_ = lean_box(v___x_2687_);
if (v_isShared_2686_ == 0)
{
lean_ctor_set(v___x_2685_, 0, v___x_2688_);
v___x_2690_ = v___x_2685_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2688_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
else
{
uint8_t v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2695_; 
lean_dec_ref_known(v_a_2683_, 1);
v___x_2692_ = 1;
v___x_2693_ = lean_box(v___x_2692_);
if (v_isShared_2686_ == 0)
{
lean_ctor_set(v___x_2685_, 0, v___x_2693_);
v___x_2695_ = v___x_2685_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2693_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
}
else
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2705_; 
v_a_2698_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2700_ = v___x_2682_;
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2682_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2703_; 
if (v_isShared_2701_ == 0)
{
v___x_2703_ = v___x_2700_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2698_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_declModifiersPubNoDoc___boxed(lean_object* v_mods_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l_Lean_Linter_MissingDocs_declModifiersPubNoDoc(v_mods_2706_, v_a_2707_, v_a_2708_);
lean_dec(v_a_2708_);
lean_dec_ref(v_a_2707_);
lean_dec(v_mods_2706_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus(uint8_t v_isEmpty_2711_, lean_object* v_stx_2712_, lean_object* v_msg_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_){
_start:
{
if (v_isEmpty_2711_ == 0)
{
lean_object* v___x_2717_; 
v___x_2717_ = l_Lean_Linter_MissingDocs_lint(v_stx_2712_, v_msg_2713_, v_a_2714_, v_a_2715_);
return v___x_2717_;
}
else
{
lean_object* v___x_2718_; 
v___x_2718_ = l_Lean_Linter_MissingDocs_lintEmpty(v_stx_2712_, v_msg_2713_, v_a_2714_, v_a_2715_);
return v___x_2718_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus___boxed(lean_object* v_isEmpty_2719_, lean_object* v_stx_2720_, lean_object* v_msg_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_){
_start:
{
uint8_t v_isEmpty_boxed_2725_; lean_object* v_res_2726_; 
v_isEmpty_boxed_2725_ = lean_unbox(v_isEmpty_2719_);
v_res_2726_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus(v_isEmpty_boxed_2725_, v_stx_2720_, v_msg_2721_, v_a_2722_, v_a_2723_);
lean_dec(v_a_2723_);
lean_dec_ref(v_a_2722_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(uint8_t v_isEmpty_2727_, lean_object* v_stx_2728_, lean_object* v_msg_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_){
_start:
{
if (v_isEmpty_2727_ == 0)
{
lean_object* v___x_2733_; 
v___x_2733_ = l_Lean_Linter_MissingDocs_lintNamed(v_stx_2728_, v_msg_2729_, v_a_2730_, v_a_2731_);
return v___x_2733_;
}
else
{
lean_object* v___x_2734_; 
v___x_2734_ = l_Lean_Linter_MissingDocs_lintEmptyNamed(v_stx_2728_, v_msg_2729_, v_a_2730_, v_a_2731_);
return v___x_2734_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed___boxed(lean_object* v_isEmpty_2735_, lean_object* v_stx_2736_, lean_object* v_msg_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_){
_start:
{
uint8_t v_isEmpty_boxed_2741_; lean_object* v_res_2742_; 
v_isEmpty_boxed_2741_ = lean_unbox(v_isEmpty_2735_);
v_res_2742_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v_isEmpty_boxed_2741_, v_stx_2736_, v_msg_2737_, v_a_2738_, v_a_2739_);
lean_dec(v_a_2739_);
lean_dec_ref(v_a_2738_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(uint8_t v_isEmpty_2743_, lean_object* v_parent_2744_, lean_object* v_stx_2745_, lean_object* v_msg_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_){
_start:
{
if (v_isEmpty_2743_ == 0)
{
lean_object* v___x_2750_; 
v___x_2750_ = l_Lean_Linter_MissingDocs_lintField(v_parent_2744_, v_stx_2745_, v_msg_2746_, v_a_2747_, v_a_2748_);
return v___x_2750_;
}
else
{
lean_object* v___x_2751_; 
v___x_2751_ = l_Lean_Linter_MissingDocs_lintEmptyField(v_parent_2744_, v_stx_2745_, v_msg_2746_, v_a_2747_, v_a_2748_);
return v___x_2751_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField___boxed(lean_object* v_isEmpty_2752_, lean_object* v_parent_2753_, lean_object* v_stx_2754_, lean_object* v_msg_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_){
_start:
{
uint8_t v_isEmpty_boxed_2759_; lean_object* v_res_2760_; 
v_isEmpty_boxed_2759_ = lean_unbox(v_isEmpty_2752_);
v_res_2760_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(v_isEmpty_boxed_2759_, v_parent_2753_, v_stx_2754_, v_msg_2755_, v_a_2756_, v_a_2757_);
lean_dec(v_a_2757_);
lean_dec_ref(v_a_2756_);
lean_dec(v_parent_2753_);
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintDeclHead(lean_object* v_k_2809_, lean_object* v_id_2810_, uint8_t v_isEmpty_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_){
_start:
{
lean_object* v___x_2815_; uint8_t v___x_2816_; 
v___x_2815_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__1));
v___x_2816_ = lean_name_eq(v_k_2809_, v___x_2815_);
if (v___x_2816_ == 0)
{
lean_object* v___x_2817_; uint8_t v___x_2818_; 
v___x_2817_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__3));
v___x_2818_ = lean_name_eq(v_k_2809_, v___x_2817_);
if (v___x_2818_ == 0)
{
lean_object* v___x_2819_; uint8_t v___x_2820_; 
v___x_2819_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__5));
v___x_2820_ = lean_name_eq(v_k_2809_, v___x_2819_);
if (v___x_2820_ == 0)
{
lean_object* v___x_2821_; uint8_t v___x_2822_; 
v___x_2821_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__7));
v___x_2822_ = lean_name_eq(v_k_2809_, v___x_2821_);
if (v___x_2822_ == 0)
{
lean_object* v___x_2823_; uint8_t v___x_2824_; 
v___x_2823_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__9));
v___x_2824_ = lean_name_eq(v_k_2809_, v___x_2823_);
if (v___x_2824_ == 0)
{
lean_object* v___x_2825_; uint8_t v___x_2826_; 
v___x_2825_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__11));
v___x_2826_ = lean_name_eq(v_k_2809_, v___x_2825_);
if (v___x_2826_ == 0)
{
lean_object* v___x_2827_; uint8_t v___x_2828_; 
v___x_2827_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__13));
v___x_2828_ = lean_name_eq(v_k_2809_, v___x_2827_);
if (v___x_2828_ == 0)
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
lean_dec(v_id_2810_);
v___x_2829_ = lean_box(0);
v___x_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2829_);
return v___x_2830_;
}
else
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2831_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__14));
v___x_2832_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v_isEmpty_2811_, v_id_2810_, v___x_2831_, v_a_2812_, v_a_2813_);
return v___x_2832_;
}
}
else
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2833_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__15));
v___x_2834_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v_isEmpty_2811_, v_id_2810_, v___x_2833_, v_a_2812_, v_a_2813_);
return v___x_2834_;
}
}
else
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2835_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__15));
v___x_2836_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v_isEmpty_2811_, v_id_2810_, v___x_2835_, v_a_2812_, v_a_2813_);
return v___x_2836_;
}
}
else
{
lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2837_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__16));
v___x_2838_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v_isEmpty_2811_, v_id_2810_, v___x_2837_, v_a_2812_, v_a_2813_);
return v___x_2838_;
}
}
else
{
lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2839_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__17));
v___x_2840_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v_isEmpty_2811_, v_id_2810_, v___x_2839_, v_a_2812_, v_a_2813_);
return v___x_2840_;
}
}
else
{
lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2841_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__18));
v___x_2842_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v_isEmpty_2811_, v_id_2810_, v___x_2841_, v_a_2812_, v_a_2813_);
return v___x_2842_;
}
}
else
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2843_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__19));
v___x_2844_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v_isEmpty_2811_, v_id_2810_, v___x_2843_, v_a_2812_, v_a_2813_);
return v___x_2844_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintDeclHead___boxed(lean_object* v_k_2845_, lean_object* v_id_2846_, lean_object* v_isEmpty_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_){
_start:
{
uint8_t v_isEmpty_boxed_2851_; lean_object* v_res_2852_; 
v_isEmpty_boxed_2851_ = lean_unbox(v_isEmpty_2847_);
v_res_2852_ = l_Lean_Linter_MissingDocs_lintDeclHead(v_k_2845_, v_id_2846_, v_isEmpty_boxed_2851_, v_a_2848_, v_a_2849_);
lean_dec(v_a_2849_);
lean_dec_ref(v_a_2848_);
lean_dec(v_k_2845_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus(lean_object* v_docOpt_2856_, lean_object* v_attrs_2857_, uint8_t v_checkTacticAlt_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_){
_start:
{
uint8_t v___x_2862_; 
v___x_2862_ = l_Lean_Linter_MissingDocs_hasInheritDoc(v_attrs_2857_);
if (v___x_2862_ == 0)
{
uint8_t v___y_2864_; 
if (v_checkTacticAlt_2858_ == 0)
{
v___y_2864_ = v___x_2862_;
goto v___jp_2863_;
}
else
{
uint8_t v___x_2892_; 
v___x_2892_ = l_Lean_Linter_MissingDocs_hasTacticAlt(v_attrs_2857_);
if (v___x_2892_ == 0)
{
v___y_2864_ = v___x_2892_;
goto v___jp_2863_;
}
else
{
lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___x_2893_ = lean_box(0);
v___x_2894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2893_);
return v___x_2894_;
}
}
v___jp_2863_:
{
uint8_t v___x_2865_; 
v___x_2865_ = l_Lean_Syntax_isNone(v_docOpt_2856_);
if (v___x_2865_ == 0)
{
lean_object* v___x_2866_; 
v___x_2866_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString(v_docOpt_2856_, v_a_2859_, v_a_2860_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2880_; 
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2869_ = v___x_2866_;
v_isShared_2870_ = v_isSharedCheck_2880_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___x_2866_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2880_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
uint8_t v___x_2871_; 
v___x_2871_ = lean_unbox(v_a_2867_);
lean_dec(v_a_2867_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2872_; lean_object* v___x_2874_; 
v___x_2872_ = lean_box(0);
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 0, v___x_2872_);
v___x_2874_ = v___x_2869_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v___x_2872_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
else
{
lean_object* v___x_2876_; lean_object* v___x_2878_; 
v___x_2876_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus___closed__0));
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 0, v___x_2876_);
v___x_2878_ = v___x_2869_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2876_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
}
else
{
lean_object* v_a_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2888_; 
v_a_2881_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2883_ = v___x_2866_;
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_a_2881_);
lean_dec(v___x_2866_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v___x_2886_; 
if (v_isShared_2884_ == 0)
{
v___x_2886_ = v___x_2883_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2881_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
}
}
else
{
lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2889_ = lean_box(v___y_2864_);
v___x_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2889_);
v___x_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2890_);
return v___x_2891_;
}
}
}
else
{
lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2895_ = lean_box(0);
v___x_2896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2895_);
return v___x_2896_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus___boxed(lean_object* v_docOpt_2897_, lean_object* v_attrs_2898_, lean_object* v_checkTacticAlt_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_){
_start:
{
uint8_t v_checkTacticAlt_boxed_2903_; lean_object* v_res_2904_; 
v_checkTacticAlt_boxed_2903_ = lean_unbox(v_checkTacticAlt_2899_);
v_res_2904_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus(v_docOpt_2897_, v_attrs_2898_, v_checkTacticAlt_boxed_2903_, v_a_2900_, v_a_2901_);
lean_dec(v_a_2901_);
lean_dec_ref(v_a_2900_);
lean_dec(v_attrs_2898_);
lean_dec(v_docOpt_2897_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__1(lean_object* v_rest_2906_, lean_object* v_as_2907_, size_t v_sz_2908_, size_t v_i_2909_, lean_object* v_b_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
lean_object* v_a_2915_; uint8_t v___x_2919_; 
v___x_2919_ = lean_usize_dec_lt(v_i_2909_, v_sz_2908_);
if (v___x_2919_ == 0)
{
lean_object* v___x_2920_; 
v___x_2920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2920_, 0, v_b_2910_);
return v___x_2920_;
}
else
{
lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v_a_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2921_ = lean_unsigned_to_nat(0u);
v___x_2922_ = lean_unsigned_to_nat(1u);
v___x_2923_ = lean_box(0);
v_a_2924_ = lean_array_uget_borrowed(v_as_2907_, v_i_2909_);
v___x_2925_ = l_Lean_Syntax_getArg(v_a_2924_, v___x_2921_);
v___x_2926_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v___x_2925_, v___y_2911_, v___y_2912_);
lean_dec(v___x_2925_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v_a_2927_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_a_2927_);
lean_dec_ref_known(v___x_2926_, 1);
if (lean_obj_tag(v_a_2927_) == 1)
{
lean_object* v_val_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; uint8_t v___x_2933_; lean_object* v___x_2934_; 
v_val_2928_ = lean_ctor_get(v_a_2927_, 0);
lean_inc(v_val_2928_);
lean_dec_ref_known(v_a_2927_, 1);
v___x_2929_ = l_Lean_Syntax_getArg(v_rest_2906_, v___x_2922_);
v___x_2930_ = l_Lean_Syntax_getArg(v___x_2929_, v___x_2921_);
lean_dec(v___x_2929_);
v___x_2931_ = l_Lean_Syntax_getArg(v_a_2924_, v___x_2922_);
v___x_2932_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__1___closed__0));
v___x_2933_ = lean_unbox(v_val_2928_);
lean_dec(v_val_2928_);
v___x_2934_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(v___x_2933_, v___x_2930_, v___x_2931_, v___x_2932_, v___y_2911_, v___y_2912_);
lean_dec(v___x_2930_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_dec_ref_known(v___x_2934_, 1);
v_a_2915_ = v___x_2923_;
goto v___jp_2914_;
}
else
{
return v___x_2934_;
}
}
else
{
lean_dec(v_a_2927_);
v_a_2915_ = v___x_2923_;
goto v___jp_2914_;
}
}
else
{
lean_object* v_a_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2942_; 
v_a_2935_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2937_ = v___x_2926_;
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_a_2935_);
lean_dec(v___x_2926_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2940_; 
if (v_isShared_2938_ == 0)
{
v___x_2940_ = v___x_2937_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_a_2935_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
return v___x_2940_;
}
}
}
}
v___jp_2914_:
{
size_t v___x_2916_; size_t v___x_2917_; 
v___x_2916_ = ((size_t)1ULL);
v___x_2917_ = lean_usize_add(v_i_2909_, v___x_2916_);
v_i_2909_ = v___x_2917_;
v_b_2910_ = v_a_2915_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__1___boxed(lean_object* v_rest_2943_, lean_object* v_as_2944_, lean_object* v_sz_2945_, lean_object* v_i_2946_, lean_object* v_b_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
size_t v_sz_boxed_2951_; size_t v_i_boxed_2952_; lean_object* v_res_2953_; 
v_sz_boxed_2951_ = lean_unbox_usize(v_sz_2945_);
lean_dec(v_sz_2945_);
v_i_boxed_2952_ = lean_unbox_usize(v_i_2946_);
lean_dec(v_i_2946_);
v_res_2953_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__1(v_rest_2943_, v_as_2944_, v_sz_boxed_2951_, v_i_boxed_2952_, v_b_2947_, v___y_2948_, v___y_2949_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec_ref(v_as_2944_);
lean_dec(v_rest_2943_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4_spec__9___redArg(lean_object* v_x_2954_, lean_object* v_x_2955_){
_start:
{
if (lean_obj_tag(v_x_2955_) == 0)
{
return v_x_2954_;
}
else
{
lean_object* v_key_2956_; lean_object* v_value_2957_; lean_object* v_tail_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2981_; 
v_key_2956_ = lean_ctor_get(v_x_2955_, 0);
v_value_2957_ = lean_ctor_get(v_x_2955_, 1);
v_tail_2958_ = lean_ctor_get(v_x_2955_, 2);
v_isSharedCheck_2981_ = !lean_is_exclusive(v_x_2955_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2960_ = v_x_2955_;
v_isShared_2961_ = v_isSharedCheck_2981_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_tail_2958_);
lean_inc(v_value_2957_);
lean_inc(v_key_2956_);
lean_dec(v_x_2955_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2981_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2962_; uint64_t v___x_2963_; uint64_t v___x_2964_; uint64_t v___x_2965_; uint64_t v_fold_2966_; uint64_t v___x_2967_; uint64_t v___x_2968_; uint64_t v___x_2969_; size_t v___x_2970_; size_t v___x_2971_; size_t v___x_2972_; size_t v___x_2973_; size_t v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2977_; 
v___x_2962_ = lean_array_get_size(v_x_2954_);
v___x_2963_ = l_String_instHashableRaw_hash(v_key_2956_);
v___x_2964_ = 32ULL;
v___x_2965_ = lean_uint64_shift_right(v___x_2963_, v___x_2964_);
v_fold_2966_ = lean_uint64_xor(v___x_2963_, v___x_2965_);
v___x_2967_ = 16ULL;
v___x_2968_ = lean_uint64_shift_right(v_fold_2966_, v___x_2967_);
v___x_2969_ = lean_uint64_xor(v_fold_2966_, v___x_2968_);
v___x_2970_ = lean_uint64_to_usize(v___x_2969_);
v___x_2971_ = lean_usize_of_nat(v___x_2962_);
v___x_2972_ = ((size_t)1ULL);
v___x_2973_ = lean_usize_sub(v___x_2971_, v___x_2972_);
v___x_2974_ = lean_usize_land(v___x_2970_, v___x_2973_);
v___x_2975_ = lean_array_uget_borrowed(v_x_2954_, v___x_2974_);
lean_inc(v___x_2975_);
if (v_isShared_2961_ == 0)
{
lean_ctor_set(v___x_2960_, 2, v___x_2975_);
v___x_2977_ = v___x_2960_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_key_2956_);
lean_ctor_set(v_reuseFailAlloc_2980_, 1, v_value_2957_);
lean_ctor_set(v_reuseFailAlloc_2980_, 2, v___x_2975_);
v___x_2977_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
lean_object* v___x_2978_; 
v___x_2978_ = lean_array_uset(v_x_2954_, v___x_2974_, v___x_2977_);
v_x_2954_ = v___x_2978_;
v_x_2955_ = v_tail_2958_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4___redArg(lean_object* v_i_2982_, lean_object* v_source_2983_, lean_object* v_target_2984_){
_start:
{
lean_object* v___x_2985_; uint8_t v___x_2986_; 
v___x_2985_ = lean_array_get_size(v_source_2983_);
v___x_2986_ = lean_nat_dec_lt(v_i_2982_, v___x_2985_);
if (v___x_2986_ == 0)
{
lean_dec_ref(v_source_2983_);
lean_dec(v_i_2982_);
return v_target_2984_;
}
else
{
lean_object* v_es_2987_; lean_object* v___x_2988_; lean_object* v_source_2989_; lean_object* v_target_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v_es_2987_ = lean_array_fget(v_source_2983_, v_i_2982_);
v___x_2988_ = lean_box(0);
v_source_2989_ = lean_array_fset(v_source_2983_, v_i_2982_, v___x_2988_);
v_target_2990_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4_spec__9___redArg(v_target_2984_, v_es_2987_);
v___x_2991_ = lean_unsigned_to_nat(1u);
v___x_2992_ = lean_nat_add(v_i_2982_, v___x_2991_);
lean_dec(v_i_2982_);
v_i_2982_ = v___x_2992_;
v_source_2983_ = v_source_2989_;
v_target_2984_ = v_target_2990_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3___redArg(lean_object* v_data_2994_){
_start:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v_nbuckets_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_2995_ = lean_array_get_size(v_data_2994_);
v___x_2996_ = lean_unsigned_to_nat(2u);
v_nbuckets_2997_ = lean_nat_mul(v___x_2995_, v___x_2996_);
v___x_2998_ = lean_unsigned_to_nat(0u);
v___x_2999_ = lean_box(0);
v___x_3000_ = lean_mk_array(v_nbuckets_2997_, v___x_2999_);
v___x_3001_ = lean_array_propagate_mark(v_data_2994_, v___x_3000_);
v___x_3002_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4___redArg(v___x_2998_, v_data_2994_, v___x_3001_);
return v___x_3002_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2___redArg(lean_object* v_a_3003_, lean_object* v_x_3004_){
_start:
{
if (lean_obj_tag(v_x_3004_) == 0)
{
uint8_t v___x_3005_; 
v___x_3005_ = 0;
return v___x_3005_;
}
else
{
lean_object* v_key_3006_; lean_object* v_tail_3007_; uint8_t v_decide_3008_; 
v_key_3006_ = lean_ctor_get(v_x_3004_, 0);
v_tail_3007_ = lean_ctor_get(v_x_3004_, 2);
v_decide_3008_ = lean_nat_dec_eq(v_key_3006_, v_a_3003_);
if (v_decide_3008_ == 0)
{
v_x_3004_ = v_tail_3007_;
goto _start;
}
else
{
return v_decide_3008_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2___redArg___boxed(lean_object* v_a_3010_, lean_object* v_x_3011_){
_start:
{
uint8_t v_res_3012_; lean_object* v_r_3013_; 
v_res_3012_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2___redArg(v_a_3010_, v_x_3011_);
lean_dec(v_x_3011_);
lean_dec(v_a_3010_);
v_r_3013_ = lean_box(v_res_3012_);
return v_r_3013_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2___redArg(lean_object* v_m_3014_, lean_object* v_a_3015_, lean_object* v_b_3016_){
_start:
{
lean_object* v_size_3017_; lean_object* v_buckets_3018_; lean_object* v___x_3019_; uint64_t v___x_3020_; uint64_t v___x_3021_; uint64_t v___x_3022_; uint64_t v_fold_3023_; uint64_t v___x_3024_; uint64_t v___x_3025_; uint64_t v___x_3026_; size_t v___x_3027_; size_t v___x_3028_; size_t v___x_3029_; size_t v___x_3030_; size_t v___x_3031_; lean_object* v_bkt_3032_; uint8_t v___x_3033_; 
v_size_3017_ = lean_ctor_get(v_m_3014_, 0);
v_buckets_3018_ = lean_ctor_get(v_m_3014_, 1);
v___x_3019_ = lean_array_get_size(v_buckets_3018_);
v___x_3020_ = l_String_instHashableRaw_hash(v_a_3015_);
v___x_3021_ = 32ULL;
v___x_3022_ = lean_uint64_shift_right(v___x_3020_, v___x_3021_);
v_fold_3023_ = lean_uint64_xor(v___x_3020_, v___x_3022_);
v___x_3024_ = 16ULL;
v___x_3025_ = lean_uint64_shift_right(v_fold_3023_, v___x_3024_);
v___x_3026_ = lean_uint64_xor(v_fold_3023_, v___x_3025_);
v___x_3027_ = lean_uint64_to_usize(v___x_3026_);
v___x_3028_ = lean_usize_of_nat(v___x_3019_);
v___x_3029_ = ((size_t)1ULL);
v___x_3030_ = lean_usize_sub(v___x_3028_, v___x_3029_);
v___x_3031_ = lean_usize_land(v___x_3027_, v___x_3030_);
v_bkt_3032_ = lean_array_uget_borrowed(v_buckets_3018_, v___x_3031_);
v___x_3033_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2___redArg(v_a_3015_, v_bkt_3032_);
if (v___x_3033_ == 0)
{
lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3054_; 
lean_inc_ref(v_buckets_3018_);
lean_inc(v_size_3017_);
v_isSharedCheck_3054_ = !lean_is_exclusive(v_m_3014_);
if (v_isSharedCheck_3054_ == 0)
{
lean_object* v_unused_3055_; lean_object* v_unused_3056_; 
v_unused_3055_ = lean_ctor_get(v_m_3014_, 1);
lean_dec(v_unused_3055_);
v_unused_3056_ = lean_ctor_get(v_m_3014_, 0);
lean_dec(v_unused_3056_);
v___x_3035_ = v_m_3014_;
v_isShared_3036_ = v_isSharedCheck_3054_;
goto v_resetjp_3034_;
}
else
{
lean_dec(v_m_3014_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3054_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3037_; lean_object* v_size_x27_3038_; lean_object* v___x_3039_; lean_object* v_buckets_x27_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; uint8_t v___x_3046_; 
v___x_3037_ = lean_unsigned_to_nat(1u);
v_size_x27_3038_ = lean_nat_add(v_size_3017_, v___x_3037_);
lean_dec(v_size_3017_);
lean_inc(v_bkt_3032_);
v___x_3039_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3039_, 0, v_a_3015_);
lean_ctor_set(v___x_3039_, 1, v_b_3016_);
lean_ctor_set(v___x_3039_, 2, v_bkt_3032_);
v_buckets_x27_3040_ = lean_array_uset(v_buckets_3018_, v___x_3031_, v___x_3039_);
v___x_3041_ = lean_unsigned_to_nat(4u);
v___x_3042_ = lean_nat_mul(v_size_x27_3038_, v___x_3041_);
v___x_3043_ = lean_unsigned_to_nat(3u);
v___x_3044_ = lean_nat_div(v___x_3042_, v___x_3043_);
lean_dec(v___x_3042_);
v___x_3045_ = lean_array_get_size(v_buckets_x27_3040_);
v___x_3046_ = lean_nat_dec_le(v___x_3044_, v___x_3045_);
lean_dec(v___x_3044_);
if (v___x_3046_ == 0)
{
lean_object* v_val_3047_; lean_object* v___x_3049_; 
v_val_3047_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3___redArg(v_buckets_x27_3040_);
if (v_isShared_3036_ == 0)
{
lean_ctor_set(v___x_3035_, 1, v_val_3047_);
lean_ctor_set(v___x_3035_, 0, v_size_x27_3038_);
v___x_3049_ = v___x_3035_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_size_x27_3038_);
lean_ctor_set(v_reuseFailAlloc_3050_, 1, v_val_3047_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
else
{
lean_object* v___x_3052_; 
if (v_isShared_3036_ == 0)
{
lean_ctor_set(v___x_3035_, 1, v_buckets_x27_3040_);
lean_ctor_set(v___x_3035_, 0, v_size_x27_3038_);
v___x_3052_ = v___x_3035_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_size_x27_3038_);
lean_ctor_set(v_reuseFailAlloc_3053_, 1, v_buckets_x27_3040_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
}
else
{
lean_dec(v_b_3016_);
lean_dec(v_a_3015_);
return v_m_3014_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6___lam__0(uint8_t v___x_3057_, lean_object* v_x_3058_, lean_object* v_info_3059_, lean_object* v_s_3060_){
_start:
{
if (lean_obj_tag(v_info_3059_) == 12)
{
lean_object* v_i_3061_; lean_object* v___x_3062_; 
v_i_3061_ = lean_ctor_get(v_info_3059_, 0);
v___x_3062_ = l_Lean_Syntax_getRange_x3f(v_i_3061_, v___x_3057_);
if (lean_obj_tag(v___x_3062_) == 1)
{
lean_object* v_val_3063_; lean_object* v_start_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v_val_3063_ = lean_ctor_get(v___x_3062_, 0);
lean_inc(v_val_3063_);
lean_dec_ref_known(v___x_3062_, 1);
v_start_3064_ = lean_ctor_get(v_val_3063_, 0);
lean_inc(v_start_3064_);
lean_dec(v_val_3063_);
v___x_3065_ = lean_box(0);
v___x_3066_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2___redArg(v_s_3060_, v_start_3064_, v___x_3065_);
return v___x_3066_;
}
else
{
lean_dec(v___x_3062_);
return v_s_3060_;
}
}
else
{
return v_s_3060_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6___lam__0___boxed(lean_object* v___x_3067_, lean_object* v_x_3068_, lean_object* v_info_3069_, lean_object* v_s_3070_){
_start:
{
uint8_t v___x_8572__boxed_3071_; lean_object* v_res_3072_; 
v___x_8572__boxed_3071_ = lean_unbox(v___x_3067_);
v_res_3072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6___lam__0(v___x_8572__boxed_3071_, v_x_3068_, v_info_3069_, v_s_3070_);
lean_dec_ref(v_info_3069_);
lean_dec_ref(v_x_3068_);
return v_res_3072_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(uint8_t v___x_3073_, lean_object* v_as_3074_, size_t v_i_3075_, size_t v_stop_3076_, lean_object* v_b_3077_){
_start:
{
uint8_t v___x_3078_; 
v___x_3078_ = lean_usize_dec_eq(v_i_3075_, v_stop_3076_);
if (v___x_3078_ == 0)
{
lean_object* v___x_3079_; lean_object* v___f_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; size_t v___x_3083_; size_t v___x_3084_; 
v___x_3079_ = lean_box(v___x_3073_);
v___f_3080_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3080_, 0, v___x_3079_);
v___x_3081_ = lean_array_uget_borrowed(v_as_3074_, v_i_3075_);
lean_inc(v___x_3081_);
v___x_3082_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_3080_, v_b_3077_, v___x_3081_);
v___x_3083_ = ((size_t)1ULL);
v___x_3084_ = lean_usize_add(v_i_3075_, v___x_3083_);
v_i_3075_ = v___x_3084_;
v_b_3077_ = v___x_3082_;
goto _start;
}
else
{
return v_b_3077_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6___boxed(lean_object* v___x_3086_, lean_object* v_as_3087_, lean_object* v_i_3088_, lean_object* v_stop_3089_, lean_object* v_b_3090_){
_start:
{
uint8_t v___x_8588__boxed_3091_; size_t v_i_boxed_3092_; size_t v_stop_boxed_3093_; lean_object* v_res_3094_; 
v___x_8588__boxed_3091_ = lean_unbox(v___x_3086_);
v_i_boxed_3092_ = lean_unbox_usize(v_i_3088_);
lean_dec(v_i_3088_);
v_stop_boxed_3093_ = lean_unbox_usize(v_stop_3089_);
lean_dec(v_stop_3089_);
v_res_3094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(v___x_8588__boxed_3091_, v_as_3087_, v_i_boxed_3092_, v_stop_boxed_3093_, v_b_3090_);
lean_dec_ref(v_as_3087_);
return v_res_3094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__7(uint8_t v___x_3095_, lean_object* v_x_3096_, lean_object* v_x_3097_){
_start:
{
if (lean_obj_tag(v_x_3096_) == 0)
{
lean_object* v_cs_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; uint8_t v___x_3101_; 
v_cs_3098_ = lean_ctor_get(v_x_3096_, 0);
v___x_3099_ = lean_unsigned_to_nat(0u);
v___x_3100_ = lean_array_get_size(v_cs_3098_);
v___x_3101_ = lean_nat_dec_lt(v___x_3099_, v___x_3100_);
if (v___x_3101_ == 0)
{
return v_x_3097_;
}
else
{
size_t v___x_3102_; size_t v___x_3103_; lean_object* v___x_3104_; 
v___x_3102_ = ((size_t)0ULL);
v___x_3103_ = lean_usize_of_nat(v___x_3100_);
v___x_3104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5_spec__7(v___x_3095_, v_cs_3098_, v___x_3102_, v___x_3103_, v_x_3097_);
return v___x_3104_;
}
}
else
{
lean_object* v_vs_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; uint8_t v___x_3108_; 
v_vs_3105_ = lean_ctor_get(v_x_3096_, 0);
v___x_3106_ = lean_unsigned_to_nat(0u);
v___x_3107_ = lean_array_get_size(v_vs_3105_);
v___x_3108_ = lean_nat_dec_lt(v___x_3106_, v___x_3107_);
if (v___x_3108_ == 0)
{
return v_x_3097_;
}
else
{
size_t v___x_3109_; size_t v___x_3110_; lean_object* v___x_3111_; 
v___x_3109_ = ((size_t)0ULL);
v___x_3110_ = lean_usize_of_nat(v___x_3107_);
v___x_3111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(v___x_3095_, v_vs_3105_, v___x_3109_, v___x_3110_, v_x_3097_);
return v___x_3111_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5_spec__7(uint8_t v___x_3112_, lean_object* v_as_3113_, size_t v_i_3114_, size_t v_stop_3115_, lean_object* v_b_3116_){
_start:
{
uint8_t v___x_3117_; 
v___x_3117_ = lean_usize_dec_eq(v_i_3114_, v_stop_3115_);
if (v___x_3117_ == 0)
{
lean_object* v___x_3118_; lean_object* v___x_3119_; size_t v___x_3120_; size_t v___x_3121_; 
v___x_3118_ = lean_array_uget_borrowed(v_as_3113_, v_i_3114_);
v___x_3119_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__7(v___x_3112_, v___x_3118_, v_b_3116_);
v___x_3120_ = ((size_t)1ULL);
v___x_3121_ = lean_usize_add(v_i_3114_, v___x_3120_);
v_i_3114_ = v___x_3121_;
v_b_3116_ = v___x_3119_;
goto _start;
}
else
{
return v_b_3116_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5_spec__7___boxed(lean_object* v___x_3123_, lean_object* v_as_3124_, lean_object* v_i_3125_, lean_object* v_stop_3126_, lean_object* v_b_3127_){
_start:
{
uint8_t v___x_8607__boxed_3128_; size_t v_i_boxed_3129_; size_t v_stop_boxed_3130_; lean_object* v_res_3131_; 
v___x_8607__boxed_3128_ = lean_unbox(v___x_3123_);
v_i_boxed_3129_ = lean_unbox_usize(v_i_3125_);
lean_dec(v_i_3125_);
v_stop_boxed_3130_ = lean_unbox_usize(v_stop_3126_);
lean_dec(v_stop_3126_);
v_res_3131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5_spec__7(v___x_8607__boxed_3128_, v_as_3124_, v_i_boxed_3129_, v_stop_boxed_3130_, v_b_3127_);
lean_dec_ref(v_as_3124_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__7___boxed(lean_object* v___x_3132_, lean_object* v_x_3133_, lean_object* v_x_3134_){
_start:
{
uint8_t v___x_8614__boxed_3135_; lean_object* v_res_3136_; 
v___x_8614__boxed_3135_ = lean_unbox(v___x_3132_);
v_res_3136_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__7(v___x_8614__boxed_3135_, v_x_3133_, v_x_3134_);
lean_dec_ref(v_x_3133_);
return v_res_3136_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_3137_; 
v___x_3137_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5(uint8_t v___x_3138_, lean_object* v_x_3139_, size_t v_x_3140_, size_t v_x_3141_, lean_object* v_x_3142_){
_start:
{
if (lean_obj_tag(v_x_3139_) == 0)
{
lean_object* v_cs_3143_; lean_object* v___x_3144_; size_t v___x_3145_; lean_object* v_j_3146_; lean_object* v___x_3147_; size_t v___x_3148_; size_t v___x_3149_; size_t v___x_3150_; size_t v___x_3151_; size_t v___x_3152_; size_t v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; uint8_t v___x_3158_; 
v_cs_3143_ = lean_ctor_get(v_x_3139_, 0);
v___x_3144_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5___closed__0);
v___x_3145_ = lean_usize_shift_right(v_x_3140_, v_x_3141_);
v_j_3146_ = lean_usize_to_nat(v___x_3145_);
v___x_3147_ = lean_array_get_borrowed(v___x_3144_, v_cs_3143_, v_j_3146_);
v___x_3148_ = ((size_t)1ULL);
v___x_3149_ = lean_usize_shift_left(v___x_3148_, v_x_3141_);
v___x_3150_ = lean_usize_sub(v___x_3149_, v___x_3148_);
v___x_3151_ = lean_usize_land(v_x_3140_, v___x_3150_);
v___x_3152_ = ((size_t)5ULL);
v___x_3153_ = lean_usize_sub(v_x_3141_, v___x_3152_);
v___x_3154_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5(v___x_3138_, v___x_3147_, v___x_3151_, v___x_3153_, v_x_3142_);
v___x_3155_ = lean_unsigned_to_nat(1u);
v___x_3156_ = lean_nat_add(v_j_3146_, v___x_3155_);
lean_dec(v_j_3146_);
v___x_3157_ = lean_array_get_size(v_cs_3143_);
v___x_3158_ = lean_nat_dec_lt(v___x_3156_, v___x_3157_);
if (v___x_3158_ == 0)
{
lean_dec(v___x_3156_);
return v___x_3154_;
}
else
{
size_t v___x_3159_; size_t v___x_3160_; lean_object* v___x_3161_; 
v___x_3159_ = lean_usize_of_nat(v___x_3156_);
lean_dec(v___x_3156_);
v___x_3160_ = lean_usize_of_nat(v___x_3157_);
v___x_3161_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5_spec__7(v___x_3138_, v_cs_3143_, v___x_3159_, v___x_3160_, v___x_3154_);
return v___x_3161_;
}
}
else
{
lean_object* v_vs_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; uint8_t v___x_3165_; 
v_vs_3162_ = lean_ctor_get(v_x_3139_, 0);
v___x_3163_ = lean_usize_to_nat(v_x_3140_);
v___x_3164_ = lean_array_get_size(v_vs_3162_);
v___x_3165_ = lean_nat_dec_lt(v___x_3163_, v___x_3164_);
if (v___x_3165_ == 0)
{
lean_dec(v___x_3163_);
return v_x_3142_;
}
else
{
size_t v___x_3166_; size_t v___x_3167_; lean_object* v___x_3168_; 
v___x_3166_ = lean_usize_of_nat(v___x_3163_);
lean_dec(v___x_3163_);
v___x_3167_ = lean_usize_of_nat(v___x_3164_);
v___x_3168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(v___x_3138_, v_vs_3162_, v___x_3166_, v___x_3167_, v_x_3142_);
return v___x_3168_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5___boxed(lean_object* v___x_3169_, lean_object* v_x_3170_, lean_object* v_x_3171_, lean_object* v_x_3172_, lean_object* v_x_3173_){
_start:
{
uint8_t v___x_8661__boxed_3174_; size_t v_x_8663__boxed_3175_; size_t v_x_8664__boxed_3176_; lean_object* v_res_3177_; 
v___x_8661__boxed_3174_ = lean_unbox(v___x_3169_);
v_x_8663__boxed_3175_ = lean_unbox_usize(v_x_3171_);
lean_dec(v_x_3171_);
v_x_8664__boxed_3176_ = lean_unbox_usize(v_x_3172_);
lean_dec(v_x_3172_);
v_res_3177_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5(v___x_8661__boxed_3174_, v_x_3170_, v_x_8663__boxed_3175_, v_x_8664__boxed_3176_, v_x_3173_);
lean_dec_ref(v_x_3170_);
return v_res_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3(uint8_t v___x_3178_, lean_object* v_t_3179_, lean_object* v_init_3180_, lean_object* v_start_3181_){
_start:
{
lean_object* v___x_3182_; uint8_t v___x_3183_; 
v___x_3182_ = lean_unsigned_to_nat(0u);
v___x_3183_ = lean_nat_dec_eq(v_start_3181_, v___x_3182_);
if (v___x_3183_ == 0)
{
lean_object* v_root_3184_; lean_object* v_tail_3185_; size_t v_shift_3186_; lean_object* v_tailOff_3187_; uint8_t v___x_3188_; 
v_root_3184_ = lean_ctor_get(v_t_3179_, 0);
v_tail_3185_ = lean_ctor_get(v_t_3179_, 1);
v_shift_3186_ = lean_ctor_get_usize(v_t_3179_, 4);
v_tailOff_3187_ = lean_ctor_get(v_t_3179_, 3);
v___x_3188_ = lean_nat_dec_le(v_tailOff_3187_, v_start_3181_);
if (v___x_3188_ == 0)
{
size_t v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; uint8_t v___x_3192_; 
v___x_3189_ = lean_usize_of_nat(v_start_3181_);
v___x_3190_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5(v___x_3178_, v_root_3184_, v___x_3189_, v_shift_3186_, v_init_3180_);
v___x_3191_ = lean_array_get_size(v_tail_3185_);
v___x_3192_ = lean_nat_dec_lt(v___x_3182_, v___x_3191_);
if (v___x_3192_ == 0)
{
return v___x_3190_;
}
else
{
size_t v___x_3193_; size_t v___x_3194_; lean_object* v___x_3195_; 
v___x_3193_ = ((size_t)0ULL);
v___x_3194_ = lean_usize_of_nat(v___x_3191_);
v___x_3195_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(v___x_3178_, v_tail_3185_, v___x_3193_, v___x_3194_, v___x_3190_);
return v___x_3195_;
}
}
else
{
lean_object* v___x_3196_; lean_object* v___x_3197_; uint8_t v___x_3198_; 
v___x_3196_ = lean_nat_sub(v_start_3181_, v_tailOff_3187_);
v___x_3197_ = lean_array_get_size(v_tail_3185_);
v___x_3198_ = lean_nat_dec_lt(v___x_3196_, v___x_3197_);
if (v___x_3198_ == 0)
{
lean_dec(v___x_3196_);
return v_init_3180_;
}
else
{
size_t v___x_3199_; size_t v___x_3200_; lean_object* v___x_3201_; 
v___x_3199_ = lean_usize_of_nat(v___x_3196_);
lean_dec(v___x_3196_);
v___x_3200_ = lean_usize_of_nat(v___x_3197_);
v___x_3201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(v___x_3178_, v_tail_3185_, v___x_3199_, v___x_3200_, v_init_3180_);
return v___x_3201_;
}
}
}
else
{
lean_object* v_root_3202_; lean_object* v_tail_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; uint8_t v___x_3206_; 
v_root_3202_ = lean_ctor_get(v_t_3179_, 0);
v_tail_3203_ = lean_ctor_get(v_t_3179_, 1);
v___x_3204_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__7(v___x_3178_, v_root_3202_, v_init_3180_);
v___x_3205_ = lean_array_get_size(v_tail_3203_);
v___x_3206_ = lean_nat_dec_lt(v___x_3182_, v___x_3205_);
if (v___x_3206_ == 0)
{
return v___x_3204_;
}
else
{
size_t v___x_3207_; size_t v___x_3208_; lean_object* v___x_3209_; 
v___x_3207_ = ((size_t)0ULL);
v___x_3208_ = lean_usize_of_nat(v___x_3205_);
v___x_3209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(v___x_3178_, v_tail_3203_, v___x_3207_, v___x_3208_, v___x_3204_);
return v___x_3209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3___boxed(lean_object* v___x_3210_, lean_object* v_t_3211_, lean_object* v_init_3212_, lean_object* v_start_3213_){
_start:
{
uint8_t v___x_8727__boxed_3214_; lean_object* v_res_3215_; 
v___x_8727__boxed_3214_ = lean_unbox(v___x_3210_);
v_res_3215_ = l_Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3(v___x_8727__boxed_3214_, v_t_3211_, v_init_3212_, v_start_3213_);
lean_dec(v_start_3213_);
lean_dec_ref(v_t_3211_);
return v_res_3215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__0(lean_object* v_rest_3217_, uint8_t v___y_3218_, lean_object* v_as_3219_, size_t v_sz_3220_, size_t v_i_3221_, lean_object* v_b_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_){
_start:
{
lean_object* v_a_3227_; uint8_t v___x_3231_; 
v___x_3231_ = lean_usize_dec_lt(v_i_3221_, v_sz_3220_);
if (v___x_3231_ == 0)
{
lean_object* v___x_3232_; 
v___x_3232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3232_, 0, v_b_3222_);
return v___x_3232_;
}
else
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v_a_3237_; uint8_t v___y_3239_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3233_ = lean_unsigned_to_nat(2u);
v___x_3234_ = lean_unsigned_to_nat(0u);
v___x_3235_ = lean_unsigned_to_nat(1u);
v___x_3236_ = lean_box(0);
v_a_3237_ = lean_array_uget_borrowed(v_as_3219_, v_i_3221_);
v___x_3246_ = l_Lean_Syntax_getArg(v_a_3237_, v___x_3233_);
v___x_3247_ = l_Lean_Syntax_getArg(v_a_3237_, v___x_3234_);
v___x_3248_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString(v___x_3247_, v___y_3223_, v___y_3224_);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_object* v_a_3249_; uint8_t v___x_3264_; 
v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_a_3249_);
lean_dec_ref_known(v___x_3248_, 1);
v___x_3264_ = l_Lean_Syntax_isNone(v___x_3247_);
lean_dec(v___x_3247_);
if (v___x_3264_ == 0)
{
if (v___y_3218_ == 0)
{
goto v___jp_3250_;
}
else
{
uint8_t v___x_3265_; 
v___x_3265_ = lean_unbox(v_a_3249_);
if (v___x_3265_ == 0)
{
lean_dec(v_a_3249_);
lean_dec(v___x_3246_);
v_a_3227_ = v___x_3236_;
goto v___jp_3226_;
}
else
{
goto v___jp_3250_;
}
}
}
else
{
goto v___jp_3250_;
}
v___jp_3250_:
{
lean_object* v___x_3251_; 
v___x_3251_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v___x_3246_, v___y_3223_, v___y_3224_);
lean_dec(v___x_3246_);
if (lean_obj_tag(v___x_3251_) == 0)
{
lean_object* v_a_3252_; 
v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
lean_inc(v_a_3252_);
lean_dec_ref_known(v___x_3251_, 1);
if (lean_obj_tag(v_a_3252_) == 1)
{
uint8_t v___x_3253_; 
v___x_3253_ = lean_unbox(v_a_3249_);
lean_dec(v_a_3249_);
if (v___x_3253_ == 0)
{
lean_object* v_val_3254_; uint8_t v___x_3255_; 
v_val_3254_ = lean_ctor_get(v_a_3252_, 0);
lean_inc(v_val_3254_);
lean_dec_ref_known(v_a_3252_, 1);
v___x_3255_ = lean_unbox(v_val_3254_);
lean_dec(v_val_3254_);
v___y_3239_ = v___x_3255_;
goto v___jp_3238_;
}
else
{
lean_dec_ref_known(v_a_3252_, 1);
v___y_3239_ = v___x_3231_;
goto v___jp_3238_;
}
}
else
{
lean_dec(v_a_3252_);
lean_dec(v_a_3249_);
v_a_3227_ = v___x_3236_;
goto v___jp_3226_;
}
}
else
{
lean_object* v_a_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3263_; 
lean_dec(v_a_3249_);
v_a_3256_ = lean_ctor_get(v___x_3251_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3251_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3258_ = v___x_3251_;
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
else
{
lean_inc(v_a_3256_);
lean_dec(v___x_3251_);
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
}
else
{
lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3273_; 
lean_dec(v___x_3247_);
lean_dec(v___x_3246_);
v_a_3266_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3268_ = v___x_3248_;
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3248_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3271_; 
if (v_isShared_3269_ == 0)
{
v___x_3271_ = v___x_3268_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_a_3266_);
v___x_3271_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
return v___x_3271_;
}
}
}
v___jp_3238_:
{
lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3240_ = l_Lean_Syntax_getArg(v_rest_3217_, v___x_3235_);
v___x_3241_ = l_Lean_Syntax_getArg(v___x_3240_, v___x_3234_);
lean_dec(v___x_3240_);
v___x_3242_ = lean_unsigned_to_nat(3u);
v___x_3243_ = l_Lean_Syntax_getArg(v_a_3237_, v___x_3242_);
v___x_3244_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__0___closed__0));
v___x_3245_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(v___y_3239_, v___x_3241_, v___x_3243_, v___x_3244_, v___y_3223_, v___y_3224_);
lean_dec(v___x_3241_);
if (lean_obj_tag(v___x_3245_) == 0)
{
lean_dec_ref_known(v___x_3245_, 1);
v_a_3227_ = v___x_3236_;
goto v___jp_3226_;
}
else
{
return v___x_3245_;
}
}
}
v___jp_3226_:
{
size_t v___x_3228_; size_t v___x_3229_; 
v___x_3228_ = ((size_t)1ULL);
v___x_3229_ = lean_usize_add(v_i_3221_, v___x_3228_);
v_i_3221_ = v___x_3229_;
v_b_3222_ = v_a_3227_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__0___boxed(lean_object* v_rest_3274_, lean_object* v___y_3275_, lean_object* v_as_3276_, lean_object* v_sz_3277_, lean_object* v_i_3278_, lean_object* v_b_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
uint8_t v___y_8776__boxed_3283_; size_t v_sz_boxed_3284_; size_t v_i_boxed_3285_; lean_object* v_res_3286_; 
v___y_8776__boxed_3283_ = lean_unbox(v___y_3275_);
v_sz_boxed_3284_ = lean_unbox_usize(v_sz_3277_);
lean_dec(v_sz_3277_);
v_i_boxed_3285_ = lean_unbox_usize(v_i_3278_);
lean_dec(v_i_3278_);
v_res_3286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__0(v_rest_3274_, v___y_8776__boxed_3283_, v_as_3276_, v_sz_boxed_3284_, v_i_boxed_3285_, v_b_3279_, v___y_3280_, v___y_3281_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec_ref(v_as_3276_);
lean_dec(v_rest_3274_);
return v_res_3286_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg(lean_object* v_m_3287_, lean_object* v_a_3288_){
_start:
{
lean_object* v_buckets_3289_; lean_object* v___x_3290_; uint64_t v___x_3291_; uint64_t v___x_3292_; uint64_t v___x_3293_; uint64_t v_fold_3294_; uint64_t v___x_3295_; uint64_t v___x_3296_; uint64_t v___x_3297_; size_t v___x_3298_; size_t v___x_3299_; size_t v___x_3300_; size_t v___x_3301_; size_t v___x_3302_; lean_object* v___x_3303_; uint8_t v___x_3304_; 
v_buckets_3289_ = lean_ctor_get(v_m_3287_, 1);
v___x_3290_ = lean_array_get_size(v_buckets_3289_);
v___x_3291_ = l_String_instHashableRaw_hash(v_a_3288_);
v___x_3292_ = 32ULL;
v___x_3293_ = lean_uint64_shift_right(v___x_3291_, v___x_3292_);
v_fold_3294_ = lean_uint64_xor(v___x_3291_, v___x_3293_);
v___x_3295_ = 16ULL;
v___x_3296_ = lean_uint64_shift_right(v_fold_3294_, v___x_3295_);
v___x_3297_ = lean_uint64_xor(v_fold_3294_, v___x_3296_);
v___x_3298_ = lean_uint64_to_usize(v___x_3297_);
v___x_3299_ = lean_usize_of_nat(v___x_3290_);
v___x_3300_ = ((size_t)1ULL);
v___x_3301_ = lean_usize_sub(v___x_3299_, v___x_3300_);
v___x_3302_ = lean_usize_land(v___x_3298_, v___x_3301_);
v___x_3303_ = lean_array_uget_borrowed(v_buckets_3289_, v___x_3302_);
v___x_3304_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2___redArg(v_a_3288_, v___x_3303_);
return v___x_3304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg___boxed(lean_object* v_m_3305_, lean_object* v_a_3306_){
_start:
{
uint8_t v_res_3307_; lean_object* v_r_3308_; 
v_res_3307_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg(v_m_3305_, v_a_3306_);
lean_dec(v_a_3306_);
lean_dec_ref(v_m_3305_);
v_r_3308_ = lean_box(v_res_3307_);
return v_r_3308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10(uint8_t v_val_3310_, lean_object* v___x_3311_, uint8_t v___x_3312_, lean_object* v___x_3313_, lean_object* v_as_3314_, size_t v_sz_3315_, size_t v_i_3316_, lean_object* v_b_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_){
_start:
{
lean_object* v_a_3322_; uint8_t v___x_3326_; 
v___x_3326_ = lean_usize_dec_lt(v_i_3316_, v_sz_3315_);
if (v___x_3326_ == 0)
{
lean_object* v___x_3327_; 
v___x_3327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3327_, 0, v_b_3317_);
return v___x_3327_;
}
else
{
lean_object* v___x_3328_; lean_object* v_a_3329_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___x_3335_; 
v___x_3328_ = lean_box(0);
v_a_3329_ = lean_array_uget_borrowed(v_as_3314_, v_i_3316_);
v___x_3335_ = l_Lean_Syntax_getRange_x3f(v_a_3329_, v___x_3312_);
if (lean_obj_tag(v___x_3335_) == 1)
{
lean_object* v_val_3336_; lean_object* v_start_3337_; uint8_t v___x_3338_; 
v_val_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_val_3336_);
lean_dec_ref_known(v___x_3335_, 1);
v_start_3337_ = lean_ctor_get(v_val_3336_, 0);
lean_inc(v_start_3337_);
lean_dec(v_val_3336_);
v___x_3338_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg(v___x_3313_, v_start_3337_);
lean_dec(v_start_3337_);
if (v___x_3338_ == 0)
{
v___y_3331_ = v___y_3318_;
v___y_3332_ = v___y_3319_;
goto v___jp_3330_;
}
else
{
v_a_3322_ = v___x_3328_;
goto v___jp_3321_;
}
}
else
{
lean_dec(v___x_3335_);
v___y_3331_ = v___y_3318_;
v___y_3332_ = v___y_3319_;
goto v___jp_3330_;
}
v___jp_3330_:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3333_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10___closed__0));
lean_inc(v_a_3329_);
v___x_3334_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(v_val_3310_, v___x_3311_, v_a_3329_, v___x_3333_, v___y_3331_, v___y_3332_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_dec_ref_known(v___x_3334_, 1);
v_a_3322_ = v___x_3328_;
goto v___jp_3321_;
}
else
{
return v___x_3334_;
}
}
}
v___jp_3321_:
{
size_t v___x_3323_; size_t v___x_3324_; 
v___x_3323_ = ((size_t)1ULL);
v___x_3324_ = lean_usize_add(v_i_3316_, v___x_3323_);
v_i_3316_ = v___x_3324_;
v_b_3317_ = v_a_3322_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10___boxed(lean_object* v_val_3339_, lean_object* v___x_3340_, lean_object* v___x_3341_, lean_object* v___x_3342_, lean_object* v_as_3343_, lean_object* v_sz_3344_, lean_object* v_i_3345_, lean_object* v_b_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
uint8_t v_val_8918__boxed_3350_; uint8_t v___x_8920__boxed_3351_; size_t v_sz_boxed_3352_; size_t v_i_boxed_3353_; lean_object* v_res_3354_; 
v_val_8918__boxed_3350_ = lean_unbox(v_val_3339_);
v___x_8920__boxed_3351_ = lean_unbox(v___x_3341_);
v_sz_boxed_3352_ = lean_unbox_usize(v_sz_3344_);
lean_dec(v_sz_3344_);
v_i_boxed_3353_ = lean_unbox_usize(v_i_3345_);
lean_dec(v_i_3345_);
v_res_3354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10(v_val_8918__boxed_3350_, v___x_3340_, v___x_8920__boxed_3351_, v___x_3342_, v_as_3343_, v_sz_boxed_3352_, v_i_boxed_3353_, v_b_3346_, v___y_3347_, v___y_3348_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec_ref(v_as_3343_);
lean_dec_ref(v___x_3342_);
lean_dec(v___x_3340_);
return v_res_3354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5(lean_object* v___x_3355_, uint8_t v___x_3356_, lean_object* v___x_3357_, uint8_t v_val_3358_, lean_object* v_as_3359_, size_t v_sz_3360_, size_t v_i_3361_, lean_object* v_b_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_){
_start:
{
lean_object* v_a_3367_; uint8_t v___x_3371_; 
v___x_3371_ = lean_usize_dec_lt(v_i_3361_, v_sz_3360_);
if (v___x_3371_ == 0)
{
lean_object* v___x_3372_; 
v___x_3372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3372_, 0, v_b_3362_);
return v___x_3372_;
}
else
{
lean_object* v___x_3373_; lean_object* v_a_3374_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___x_3380_; 
v___x_3373_ = lean_box(0);
v_a_3374_ = lean_array_uget_borrowed(v_as_3359_, v_i_3361_);
v___x_3380_ = l_Lean_Syntax_getRange_x3f(v_a_3374_, v___x_3356_);
if (lean_obj_tag(v___x_3380_) == 1)
{
lean_object* v_val_3381_; lean_object* v_start_3382_; uint8_t v___x_3383_; 
v_val_3381_ = lean_ctor_get(v___x_3380_, 0);
lean_inc(v_val_3381_);
lean_dec_ref_known(v___x_3380_, 1);
v_start_3382_ = lean_ctor_get(v_val_3381_, 0);
lean_inc(v_start_3382_);
lean_dec(v_val_3381_);
v___x_3383_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg(v___x_3357_, v_start_3382_);
lean_dec(v_start_3382_);
if (v___x_3383_ == 0)
{
v___y_3376_ = v___y_3363_;
v___y_3377_ = v___y_3364_;
goto v___jp_3375_;
}
else
{
v_a_3367_ = v___x_3373_;
goto v___jp_3366_;
}
}
else
{
lean_dec(v___x_3380_);
v___y_3376_ = v___y_3363_;
v___y_3377_ = v___y_3364_;
goto v___jp_3375_;
}
v___jp_3375_:
{
lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3378_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10___closed__0));
lean_inc(v_a_3374_);
v___x_3379_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(v_val_3358_, v___x_3355_, v_a_3374_, v___x_3378_, v___y_3376_, v___y_3377_);
if (lean_obj_tag(v___x_3379_) == 0)
{
lean_dec_ref_known(v___x_3379_, 1);
v_a_3367_ = v___x_3373_;
goto v___jp_3366_;
}
else
{
return v___x_3379_;
}
}
}
v___jp_3366_:
{
size_t v___x_3368_; size_t v___x_3369_; lean_object* v___x_3370_; 
v___x_3368_ = ((size_t)1ULL);
v___x_3369_ = lean_usize_add(v_i_3361_, v___x_3368_);
v___x_3370_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10(v_val_3358_, v___x_3355_, v___x_3356_, v___x_3357_, v_as_3359_, v_sz_3360_, v___x_3369_, v_a_3367_, v___y_3363_, v___y_3364_);
return v___x_3370_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5___boxed(lean_object* v___x_3384_, lean_object* v___x_3385_, lean_object* v___x_3386_, lean_object* v_val_3387_, lean_object* v_as_3388_, lean_object* v_sz_3389_, lean_object* v_i_3390_, lean_object* v_b_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
uint8_t v___x_8976__boxed_3395_; uint8_t v_val_8978__boxed_3396_; size_t v_sz_boxed_3397_; size_t v_i_boxed_3398_; lean_object* v_res_3399_; 
v___x_8976__boxed_3395_ = lean_unbox(v___x_3385_);
v_val_8978__boxed_3396_ = lean_unbox(v_val_3387_);
v_sz_boxed_3397_ = lean_unbox_usize(v_sz_3389_);
lean_dec(v_sz_3389_);
v_i_boxed_3398_ = lean_unbox_usize(v_i_3390_);
lean_dec(v_i_3390_);
v_res_3399_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5(v___x_3384_, v___x_8976__boxed_3395_, v___x_3386_, v_val_8978__boxed_3396_, v_as_3388_, v_sz_boxed_3397_, v_i_boxed_3398_, v_b_3391_, v___y_3392_, v___y_3393_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec_ref(v_as_3388_);
lean_dec_ref(v___x_3386_);
lean_dec(v___x_3384_);
return v_res_3399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12(lean_object* v___x_3406_, uint8_t v___x_3407_, lean_object* v___x_3408_, lean_object* v_as_3409_, size_t v_sz_3410_, size_t v_i_3411_, lean_object* v_b_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_){
_start:
{
lean_object* v_a_3417_; uint8_t v___x_3421_; 
v___x_3421_ = lean_usize_dec_lt(v_i_3411_, v_sz_3410_);
if (v___x_3421_ == 0)
{
lean_object* v___x_3422_; 
v___x_3422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3422_, 0, v_b_3412_);
return v___x_3422_;
}
else
{
lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v_a_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3423_ = lean_unsigned_to_nat(0u);
v___x_3424_ = lean_unsigned_to_nat(2u);
v___x_3425_ = lean_box(0);
v___x_3426_ = lean_unsigned_to_nat(1u);
v_a_3427_ = lean_array_uget_borrowed(v_as_3409_, v_i_3411_);
v___x_3428_ = l_Lean_Syntax_getArg(v_a_3427_, v___x_3423_);
v___x_3429_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v___x_3428_, v___y_3413_, v___y_3414_);
lean_dec(v___x_3428_);
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_object* v_a_3430_; 
v_a_3430_ = lean_ctor_get(v___x_3429_, 0);
lean_inc(v_a_3430_);
lean_dec_ref_known(v___x_3429_, 1);
if (lean_obj_tag(v_a_3430_) == 1)
{
lean_object* v_val_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; uint8_t v___x_3434_; 
v_val_3431_ = lean_ctor_get(v_a_3430_, 0);
lean_inc(v_val_3431_);
lean_dec_ref_known(v_a_3430_, 1);
lean_inc(v_a_3427_);
v___x_3432_ = l_Lean_Syntax_getKind(v_a_3427_);
v___x_3433_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12___closed__1));
v___x_3434_ = lean_name_eq(v___x_3432_, v___x_3433_);
lean_dec(v___x_3432_);
if (v___x_3434_ == 0)
{
lean_object* v___x_3435_; lean_object* v___x_3436_; size_t v_sz_3437_; size_t v___x_3438_; uint8_t v___x_3439_; lean_object* v___x_3440_; 
v___x_3435_ = l_Lean_Syntax_getArg(v_a_3427_, v___x_3424_);
v___x_3436_ = l_Lean_Syntax_getArgs(v___x_3435_);
lean_dec(v___x_3435_);
v_sz_3437_ = lean_array_size(v___x_3436_);
v___x_3438_ = ((size_t)0ULL);
v___x_3439_ = lean_unbox(v_val_3431_);
lean_dec(v_val_3431_);
v___x_3440_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5(v___x_3406_, v___x_3407_, v___x_3408_, v___x_3439_, v___x_3436_, v_sz_3437_, v___x_3438_, v___x_3425_, v___y_3413_, v___y_3414_);
lean_dec_ref(v___x_3436_);
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_dec_ref_known(v___x_3440_, 1);
v_a_3417_ = v___x_3425_;
goto v___jp_3416_;
}
else
{
return v___x_3440_;
}
}
else
{
lean_object* v___x_3441_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___x_3448_; 
v___x_3441_ = l_Lean_Syntax_getArg(v_a_3427_, v___x_3426_);
v___x_3448_ = l_Lean_Syntax_getRange_x3f(v___x_3441_, v___x_3407_);
if (lean_obj_tag(v___x_3448_) == 1)
{
lean_object* v_val_3449_; lean_object* v_start_3450_; uint8_t v___x_3451_; 
v_val_3449_ = lean_ctor_get(v___x_3448_, 0);
lean_inc(v_val_3449_);
lean_dec_ref_known(v___x_3448_, 1);
v_start_3450_ = lean_ctor_get(v_val_3449_, 0);
lean_inc(v_start_3450_);
lean_dec(v_val_3449_);
v___x_3451_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg(v___x_3408_, v_start_3450_);
lean_dec(v_start_3450_);
if (v___x_3451_ == 0)
{
v___y_3443_ = v___y_3413_;
v___y_3444_ = v___y_3414_;
goto v___jp_3442_;
}
else
{
lean_dec(v___x_3441_);
lean_dec(v_val_3431_);
v_a_3417_ = v___x_3425_;
goto v___jp_3416_;
}
}
else
{
lean_dec(v___x_3448_);
v___y_3443_ = v___y_3413_;
v___y_3444_ = v___y_3414_;
goto v___jp_3442_;
}
v___jp_3442_:
{
lean_object* v___x_3445_; uint8_t v___x_3446_; lean_object* v___x_3447_; 
v___x_3445_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10___closed__0));
v___x_3446_ = lean_unbox(v_val_3431_);
lean_dec(v_val_3431_);
v___x_3447_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(v___x_3446_, v___x_3406_, v___x_3441_, v___x_3445_, v___y_3443_, v___y_3444_);
if (lean_obj_tag(v___x_3447_) == 0)
{
lean_dec_ref_known(v___x_3447_, 1);
v_a_3417_ = v___x_3425_;
goto v___jp_3416_;
}
else
{
return v___x_3447_;
}
}
}
}
else
{
lean_dec(v_a_3430_);
v_a_3417_ = v___x_3425_;
goto v___jp_3416_;
}
}
else
{
lean_object* v_a_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3459_; 
v_a_3452_ = lean_ctor_get(v___x_3429_, 0);
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_3429_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3454_ = v___x_3429_;
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_a_3452_);
lean_dec(v___x_3429_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3457_; 
if (v_isShared_3455_ == 0)
{
v___x_3457_ = v___x_3454_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_a_3452_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
}
}
v___jp_3416_:
{
size_t v___x_3418_; size_t v___x_3419_; 
v___x_3418_ = ((size_t)1ULL);
v___x_3419_ = lean_usize_add(v_i_3411_, v___x_3418_);
v_i_3411_ = v___x_3419_;
v_b_3412_ = v_a_3417_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12___boxed(lean_object* v___x_3460_, lean_object* v___x_3461_, lean_object* v___x_3462_, lean_object* v_as_3463_, lean_object* v_sz_3464_, lean_object* v_i_3465_, lean_object* v_b_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_){
_start:
{
uint8_t v___x_9047__boxed_3470_; size_t v_sz_boxed_3471_; size_t v_i_boxed_3472_; lean_object* v_res_3473_; 
v___x_9047__boxed_3470_ = lean_unbox(v___x_3461_);
v_sz_boxed_3471_ = lean_unbox_usize(v_sz_3464_);
lean_dec(v_sz_3464_);
v_i_boxed_3472_ = lean_unbox_usize(v_i_3465_);
lean_dec(v_i_3465_);
v_res_3473_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12(v___x_3460_, v___x_9047__boxed_3470_, v___x_3462_, v_as_3463_, v_sz_boxed_3471_, v_i_boxed_3472_, v_b_3466_, v___y_3467_, v___y_3468_);
lean_dec(v___y_3468_);
lean_dec_ref(v___y_3467_);
lean_dec_ref(v_as_3463_);
lean_dec_ref(v___x_3462_);
lean_dec(v___x_3460_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6(lean_object* v___x_3474_, uint8_t v___x_3475_, lean_object* v___x_3476_, lean_object* v_as_3477_, size_t v_sz_3478_, size_t v_i_3479_, lean_object* v_b_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_){
_start:
{
lean_object* v_a_3485_; uint8_t v___x_3489_; 
v___x_3489_ = lean_usize_dec_lt(v_i_3479_, v_sz_3478_);
if (v___x_3489_ == 0)
{
lean_object* v___x_3490_; 
v___x_3490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3490_, 0, v_b_3480_);
return v___x_3490_;
}
else
{
lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v_a_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3491_ = lean_unsigned_to_nat(0u);
v___x_3492_ = lean_box(0);
v___x_3493_ = lean_unsigned_to_nat(2u);
v___x_3494_ = lean_unsigned_to_nat(1u);
v_a_3495_ = lean_array_uget_borrowed(v_as_3477_, v_i_3479_);
v___x_3496_ = l_Lean_Syntax_getArg(v_a_3495_, v___x_3491_);
v___x_3497_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v___x_3496_, v___y_3481_, v___y_3482_);
lean_dec(v___x_3496_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_a_3498_);
lean_dec_ref_known(v___x_3497_, 1);
if (lean_obj_tag(v_a_3498_) == 1)
{
lean_object* v_val_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; uint8_t v___x_3502_; 
v_val_3499_ = lean_ctor_get(v_a_3498_, 0);
lean_inc(v_val_3499_);
lean_dec_ref_known(v_a_3498_, 1);
lean_inc(v_a_3495_);
v___x_3500_ = l_Lean_Syntax_getKind(v_a_3495_);
v___x_3501_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12___closed__1));
v___x_3502_ = lean_name_eq(v___x_3500_, v___x_3501_);
lean_dec(v___x_3500_);
if (v___x_3502_ == 0)
{
lean_object* v___x_3503_; lean_object* v___x_3504_; size_t v_sz_3505_; size_t v___x_3506_; uint8_t v___x_3507_; lean_object* v___x_3508_; 
v___x_3503_ = l_Lean_Syntax_getArg(v_a_3495_, v___x_3493_);
v___x_3504_ = l_Lean_Syntax_getArgs(v___x_3503_);
lean_dec(v___x_3503_);
v_sz_3505_ = lean_array_size(v___x_3504_);
v___x_3506_ = ((size_t)0ULL);
v___x_3507_ = lean_unbox(v_val_3499_);
lean_dec(v_val_3499_);
v___x_3508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5(v___x_3474_, v___x_3475_, v___x_3476_, v___x_3507_, v___x_3504_, v_sz_3505_, v___x_3506_, v___x_3492_, v___y_3481_, v___y_3482_);
lean_dec_ref(v___x_3504_);
if (lean_obj_tag(v___x_3508_) == 0)
{
lean_dec_ref_known(v___x_3508_, 1);
v_a_3485_ = v___x_3492_;
goto v___jp_3484_;
}
else
{
return v___x_3508_;
}
}
else
{
lean_object* v___x_3509_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___x_3516_; 
v___x_3509_ = l_Lean_Syntax_getArg(v_a_3495_, v___x_3494_);
v___x_3516_ = l_Lean_Syntax_getRange_x3f(v___x_3509_, v___x_3475_);
if (lean_obj_tag(v___x_3516_) == 1)
{
lean_object* v_val_3517_; lean_object* v_start_3518_; uint8_t v___x_3519_; 
v_val_3517_ = lean_ctor_get(v___x_3516_, 0);
lean_inc(v_val_3517_);
lean_dec_ref_known(v___x_3516_, 1);
v_start_3518_ = lean_ctor_get(v_val_3517_, 0);
lean_inc(v_start_3518_);
lean_dec(v_val_3517_);
v___x_3519_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg(v___x_3476_, v_start_3518_);
lean_dec(v_start_3518_);
if (v___x_3519_ == 0)
{
v___y_3511_ = v___y_3481_;
v___y_3512_ = v___y_3482_;
goto v___jp_3510_;
}
else
{
lean_dec(v___x_3509_);
lean_dec(v_val_3499_);
v_a_3485_ = v___x_3492_;
goto v___jp_3484_;
}
}
else
{
lean_dec(v___x_3516_);
v___y_3511_ = v___y_3481_;
v___y_3512_ = v___y_3482_;
goto v___jp_3510_;
}
v___jp_3510_:
{
lean_object* v___x_3513_; uint8_t v___x_3514_; lean_object* v___x_3515_; 
v___x_3513_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10___closed__0));
v___x_3514_ = lean_unbox(v_val_3499_);
lean_dec(v_val_3499_);
v___x_3515_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(v___x_3514_, v___x_3474_, v___x_3509_, v___x_3513_, v___y_3511_, v___y_3512_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_dec_ref_known(v___x_3515_, 1);
v_a_3485_ = v___x_3492_;
goto v___jp_3484_;
}
else
{
return v___x_3515_;
}
}
}
}
else
{
lean_dec(v_a_3498_);
v_a_3485_ = v___x_3492_;
goto v___jp_3484_;
}
}
else
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
v_a_3520_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___x_3497_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3497_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3525_; 
if (v_isShared_3523_ == 0)
{
v___x_3525_ = v___x_3522_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3520_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
}
v___jp_3484_:
{
size_t v___x_3486_; size_t v___x_3487_; lean_object* v___x_3488_; 
v___x_3486_ = ((size_t)1ULL);
v___x_3487_ = lean_usize_add(v_i_3479_, v___x_3486_);
v___x_3488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12(v___x_3474_, v___x_3475_, v___x_3476_, v_as_3477_, v_sz_3478_, v___x_3487_, v_a_3485_, v___y_3481_, v___y_3482_);
return v___x_3488_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6___boxed(lean_object* v___x_3528_, lean_object* v___x_3529_, lean_object* v___x_3530_, lean_object* v_as_3531_, lean_object* v_sz_3532_, lean_object* v_i_3533_, lean_object* v_b_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_){
_start:
{
uint8_t v___x_9167__boxed_3538_; size_t v_sz_boxed_3539_; size_t v_i_boxed_3540_; lean_object* v_res_3541_; 
v___x_9167__boxed_3538_ = lean_unbox(v___x_3529_);
v_sz_boxed_3539_ = lean_unbox_usize(v_sz_3532_);
lean_dec(v_sz_3532_);
v_i_boxed_3540_ = lean_unbox_usize(v_i_3533_);
lean_dec(v_i_3533_);
v_res_3541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6(v___x_3528_, v___x_9167__boxed_3538_, v___x_3530_, v_as_3531_, v_sz_boxed_3539_, v_i_boxed_3540_, v_b_3534_, v___y_3535_, v___y_3536_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
lean_dec_ref(v_as_3531_);
lean_dec_ref(v___x_3530_);
lean_dec(v___x_3528_);
return v_res_3541_;
}
}
static lean_object* _init_l_Lean_Linter_MissingDocs_checkDecl___closed__0(void){
_start:
{
lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3542_ = lean_box(0);
v___x_3543_ = lean_unsigned_to_nat(16u);
v___x_3544_ = lean_mk_array(v___x_3543_, v___x_3542_);
return v___x_3544_;
}
}
static lean_object* _init_l_Lean_Linter_MissingDocs_checkDecl___closed__1(void){
_start:
{
lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3545_ = lean_obj_once(&l_Lean_Linter_MissingDocs_checkDecl___closed__0, &l_Lean_Linter_MissingDocs_checkDecl___closed__0_once, _init_l_Lean_Linter_MissingDocs_checkDecl___closed__0);
v___x_3546_ = lean_unsigned_to_nat(0u);
v___x_3547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3547_, 0, v___x_3546_);
lean_ctor_set(v___x_3547_, 1, v___x_3545_);
return v___x_3547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkDecl(lean_object* v_stx_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_){
_start:
{
lean_object* v___x_3552_; lean_object* v_head_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; uint8_t v___x_3559_; 
v___x_3552_ = lean_unsigned_to_nat(0u);
v_head_3553_ = l_Lean_Syntax_getArg(v_stx_3548_, v___x_3552_);
v___x_3554_ = lean_unsigned_to_nat(2u);
v___x_3555_ = l_Lean_Syntax_getArg(v_head_3553_, v___x_3554_);
v___x_3556_ = l_Lean_Syntax_getArg(v___x_3555_, v___x_3552_);
lean_dec(v___x_3555_);
v___x_3557_ = l_Lean_Syntax_getKind(v___x_3556_);
v___x_3558_ = ((lean_object*)(l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__0));
v___x_3559_ = lean_name_eq(v___x_3557_, v___x_3558_);
lean_dec(v___x_3557_);
if (v___x_3559_ == 0)
{
lean_object* v___x_3560_; lean_object* v_rest_3561_; lean_object* v___y_3563_; lean_object* v___y_3564_; uint8_t v___y_3565_; uint8_t v___x_3597_; lean_object* v_k_3598_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___x_3637_; 
v___x_3560_ = lean_unsigned_to_nat(1u);
v_rest_3561_ = l_Lean_Syntax_getArg(v_stx_3548_, v___x_3560_);
v___x_3597_ = 1;
lean_inc(v_rest_3561_);
v_k_3598_ = l_Lean_Syntax_getKind(v_rest_3561_);
v___x_3637_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v_head_3553_, v_a_3549_, v_a_3550_);
lean_dec(v_head_3553_);
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_object* v_a_3638_; 
v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
lean_inc(v_a_3638_);
lean_dec_ref_known(v___x_3637_, 1);
if (lean_obj_tag(v_a_3638_) == 1)
{
lean_object* v_val_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; uint8_t v___x_3642_; lean_object* v___x_3643_; 
v_val_3639_ = lean_ctor_get(v_a_3638_, 0);
lean_inc(v_val_3639_);
lean_dec_ref_known(v_a_3638_, 1);
v___x_3640_ = l_Lean_Syntax_getArg(v_rest_3561_, v___x_3560_);
v___x_3641_ = l_Lean_Syntax_getArg(v___x_3640_, v___x_3552_);
lean_dec(v___x_3640_);
v___x_3642_ = lean_unbox(v_val_3639_);
lean_dec(v_val_3639_);
v___x_3643_ = l_Lean_Linter_MissingDocs_lintDeclHead(v_k_3598_, v___x_3641_, v___x_3642_, v_a_3549_, v_a_3550_);
if (lean_obj_tag(v___x_3643_) == 0)
{
lean_dec_ref_known(v___x_3643_, 1);
v___y_3600_ = v_a_3549_;
v___y_3601_ = v_a_3550_;
goto v___jp_3599_;
}
else
{
lean_dec(v_k_3598_);
lean_dec(v_rest_3561_);
return v___x_3643_;
}
}
else
{
lean_dec(v_a_3638_);
v___y_3600_ = v_a_3549_;
v___y_3601_ = v_a_3550_;
goto v___jp_3599_;
}
}
else
{
lean_object* v_a_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3651_; 
lean_dec(v_k_3598_);
lean_dec(v_rest_3561_);
v_a_3644_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3651_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3646_ = v___x_3637_;
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_a_3644_);
lean_dec(v___x_3637_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3649_; 
if (v_isShared_3647_ == 0)
{
v___x_3649_ = v___x_3646_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_a_3644_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
}
v___jp_3562_:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; size_t v_sz_3570_; size_t v___x_3571_; lean_object* v___x_3572_; 
v___x_3566_ = lean_unsigned_to_nat(4u);
v___x_3567_ = l_Lean_Syntax_getArg(v_rest_3561_, v___x_3566_);
v___x_3568_ = l_Lean_Syntax_getArgs(v___x_3567_);
lean_dec(v___x_3567_);
v___x_3569_ = lean_box(0);
v_sz_3570_ = lean_array_size(v___x_3568_);
v___x_3571_ = ((size_t)0ULL);
v___x_3572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__0(v_rest_3561_, v___y_3565_, v___x_3568_, v_sz_3570_, v___x_3571_, v___x_3569_, v___y_3564_, v___y_3563_);
lean_dec_ref(v___x_3568_);
if (lean_obj_tag(v___x_3572_) == 0)
{
lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3595_; 
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3595_ == 0)
{
lean_object* v_unused_3596_; 
v_unused_3596_ = lean_ctor_get(v___x_3572_, 0);
lean_dec(v_unused_3596_);
v___x_3574_ = v___x_3572_;
v_isShared_3575_ = v_isSharedCheck_3595_;
goto v_resetjp_3573_;
}
else
{
lean_dec(v___x_3572_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3595_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3576_; lean_object* v___x_3577_; uint8_t v___x_3578_; 
v___x_3576_ = lean_unsigned_to_nat(5u);
v___x_3577_ = l_Lean_Syntax_getArg(v_rest_3561_, v___x_3576_);
v___x_3578_ = l_Lean_Syntax_isNone(v___x_3577_);
if (v___x_3578_ == 0)
{
lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; size_t v_sz_3582_; lean_object* v___x_3583_; 
lean_del_object(v___x_3574_);
v___x_3579_ = l_Lean_Syntax_getArg(v___x_3577_, v___x_3552_);
lean_dec(v___x_3577_);
v___x_3580_ = l_Lean_Syntax_getArg(v___x_3579_, v___x_3560_);
lean_dec(v___x_3579_);
v___x_3581_ = l_Lean_Syntax_getArgs(v___x_3580_);
lean_dec(v___x_3580_);
v_sz_3582_ = lean_array_size(v___x_3581_);
v___x_3583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__1(v_rest_3561_, v___x_3581_, v_sz_3582_, v___x_3571_, v___x_3569_, v___y_3564_, v___y_3563_);
lean_dec_ref(v___x_3581_);
lean_dec(v_rest_3561_);
if (lean_obj_tag(v___x_3583_) == 0)
{
lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3590_; 
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3583_);
if (v_isSharedCheck_3590_ == 0)
{
lean_object* v_unused_3591_; 
v_unused_3591_ = lean_ctor_get(v___x_3583_, 0);
lean_dec(v_unused_3591_);
v___x_3585_ = v___x_3583_;
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
else
{
lean_dec(v___x_3583_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3588_; 
if (v_isShared_3586_ == 0)
{
lean_ctor_set(v___x_3585_, 0, v___x_3569_);
v___x_3588_ = v___x_3585_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v___x_3569_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
else
{
return v___x_3583_;
}
}
else
{
lean_object* v___x_3593_; 
lean_dec(v___x_3577_);
lean_dec(v_rest_3561_);
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 0, v___x_3569_);
v___x_3593_ = v___x_3574_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v___x_3569_);
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
else
{
lean_dec(v_rest_3561_);
return v___x_3572_;
}
}
v___jp_3599_:
{
lean_object* v___x_3602_; uint8_t v___x_3603_; 
v___x_3602_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__9));
v___x_3603_ = lean_name_eq(v_k_3598_, v___x_3602_);
if (v___x_3603_ == 0)
{
lean_object* v___x_3604_; uint8_t v___x_3605_; 
v___x_3604_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__11));
v___x_3605_ = lean_name_eq(v_k_3598_, v___x_3604_);
if (v___x_3605_ == 0)
{
lean_object* v___x_3606_; uint8_t v___x_3607_; 
v___x_3606_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__13));
v___x_3607_ = lean_name_eq(v_k_3598_, v___x_3606_);
lean_dec(v_k_3598_);
if (v___x_3607_ == 0)
{
lean_object* v___x_3608_; lean_object* v___x_3609_; 
lean_dec(v_rest_3561_);
v___x_3608_ = lean_box(0);
v___x_3609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3608_);
return v___x_3609_;
}
else
{
lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; uint8_t v___x_3613_; 
v___x_3610_ = lean_unsigned_to_nat(4u);
v___x_3611_ = l_Lean_Syntax_getArg(v_rest_3561_, v___x_3610_);
v___x_3612_ = l_Lean_Syntax_getArg(v___x_3611_, v___x_3554_);
lean_dec(v___x_3611_);
v___x_3613_ = l_Lean_Syntax_isNone(v___x_3612_);
if (v___x_3613_ == 0)
{
lean_object* v___x_3614_; lean_object* v_infoState_3615_; lean_object* v_trees_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; size_t v_sz_3624_; size_t v___x_3625_; lean_object* v___x_3626_; 
v___x_3614_ = lean_st_ref_get(v___y_3601_);
v_infoState_3615_ = lean_ctor_get(v___x_3614_, 8);
lean_inc_ref(v_infoState_3615_);
lean_dec(v___x_3614_);
v_trees_3616_ = lean_ctor_get(v_infoState_3615_, 2);
lean_inc_ref(v_trees_3616_);
lean_dec_ref(v_infoState_3615_);
v___x_3617_ = lean_obj_once(&l_Lean_Linter_MissingDocs_checkDecl___closed__1, &l_Lean_Linter_MissingDocs_checkDecl___closed__1_once, _init_l_Lean_Linter_MissingDocs_checkDecl___closed__1);
v___x_3618_ = l_Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3(v___x_3613_, v_trees_3616_, v___x_3617_, v___x_3552_);
lean_dec_ref(v_trees_3616_);
v___x_3619_ = l_Lean_Syntax_getArg(v_rest_3561_, v___x_3560_);
lean_dec(v_rest_3561_);
v___x_3620_ = l_Lean_Syntax_getArg(v___x_3619_, v___x_3552_);
lean_dec(v___x_3619_);
v___x_3621_ = l_Lean_Syntax_getArg(v___x_3612_, v___x_3552_);
lean_dec(v___x_3612_);
v___x_3622_ = l_Lean_Syntax_getArgs(v___x_3621_);
lean_dec(v___x_3621_);
v___x_3623_ = lean_box(0);
v_sz_3624_ = lean_array_size(v___x_3622_);
v___x_3625_ = ((size_t)0ULL);
v___x_3626_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6(v___x_3620_, v___x_3613_, v___x_3618_, v___x_3622_, v_sz_3624_, v___x_3625_, v___x_3623_, v___y_3600_, v___y_3601_);
lean_dec_ref(v___x_3622_);
lean_dec_ref(v___x_3618_);
lean_dec(v___x_3620_);
if (lean_obj_tag(v___x_3626_) == 0)
{
lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3633_; 
v_isSharedCheck_3633_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3633_ == 0)
{
lean_object* v_unused_3634_; 
v_unused_3634_ = lean_ctor_get(v___x_3626_, 0);
lean_dec(v_unused_3634_);
v___x_3628_ = v___x_3626_;
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
else
{
lean_dec(v___x_3626_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3631_; 
if (v_isShared_3629_ == 0)
{
lean_ctor_set(v___x_3628_, 0, v___x_3623_);
v___x_3631_ = v___x_3628_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v___x_3623_);
v___x_3631_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
return v___x_3631_;
}
}
}
else
{
return v___x_3626_;
}
}
else
{
lean_object* v___x_3635_; lean_object* v___x_3636_; 
lean_dec(v___x_3612_);
lean_dec(v_rest_3561_);
v___x_3635_ = lean_box(0);
v___x_3636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3636_, 0, v___x_3635_);
return v___x_3636_;
}
}
}
else
{
lean_dec(v_k_3598_);
v___y_3563_ = v___y_3601_;
v___y_3564_ = v___y_3600_;
v___y_3565_ = v___x_3605_;
goto v___jp_3562_;
}
}
else
{
lean_dec(v_k_3598_);
v___y_3563_ = v___y_3601_;
v___y_3564_ = v___y_3600_;
v___y_3565_ = v___x_3597_;
goto v___jp_3562_;
}
}
}
else
{
lean_object* v___x_3652_; lean_object* v___x_3653_; 
lean_dec(v_head_3553_);
v___x_3652_ = lean_box(0);
v___x_3653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3652_);
return v___x_3653_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkDecl___boxed(lean_object* v_stx_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_){
_start:
{
lean_object* v_res_3658_; 
v_res_3658_ = l_Lean_Linter_MissingDocs_checkDecl(v_stx_3654_, v_a_3655_, v_a_3656_);
lean_dec(v_a_3656_);
lean_dec_ref(v_a_3655_);
lean_dec(v_stx_3654_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2(lean_object* v_00_u03b2_3659_, lean_object* v_m_3660_, lean_object* v_a_3661_, lean_object* v_b_3662_){
_start:
{
lean_object* v___x_3663_; 
v___x_3663_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2___redArg(v_m_3660_, v_a_3661_, v_b_3662_);
return v___x_3663_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4(lean_object* v_00_u03b2_3664_, lean_object* v_m_3665_, lean_object* v_a_3666_){
_start:
{
uint8_t v___x_3667_; 
v___x_3667_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg(v_m_3665_, v_a_3666_);
return v___x_3667_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___boxed(lean_object* v_00_u03b2_3668_, lean_object* v_m_3669_, lean_object* v_a_3670_){
_start:
{
uint8_t v_res_3671_; lean_object* v_r_3672_; 
v_res_3671_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4(v_00_u03b2_3668_, v_m_3669_, v_a_3670_);
lean_dec(v_a_3670_);
lean_dec_ref(v_m_3669_);
v_r_3672_ = lean_box(v_res_3671_);
return v_r_3672_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2(lean_object* v_00_u03b2_3673_, lean_object* v_a_3674_, lean_object* v_x_3675_){
_start:
{
uint8_t v___x_3676_; 
v___x_3676_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2___redArg(v_a_3674_, v_x_3675_);
return v___x_3676_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2___boxed(lean_object* v_00_u03b2_3677_, lean_object* v_a_3678_, lean_object* v_x_3679_){
_start:
{
uint8_t v_res_3680_; lean_object* v_r_3681_; 
v_res_3680_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2(v_00_u03b2_3677_, v_a_3678_, v_x_3679_);
lean_dec(v_x_3679_);
lean_dec(v_a_3678_);
v_r_3681_ = lean_box(v_res_3680_);
return v_r_3681_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3(lean_object* v_00_u03b2_3682_, lean_object* v_data_3683_){
_start:
{
lean_object* v___x_3684_; 
v___x_3684_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3___redArg(v_data_3683_);
return v___x_3684_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_3685_, lean_object* v_i_3686_, lean_object* v_source_3687_, lean_object* v_target_3688_){
_start:
{
lean_object* v___x_3689_; 
v___x_3689_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4___redArg(v_i_3686_, v_source_3687_, v_target_3688_);
return v___x_3689_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_3690_, lean_object* v_x_3691_, lean_object* v_x_3692_){
_start:
{
lean_object* v___x_3693_; 
v___x_3693_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4_spec__9___redArg(v_x_3691_, v_x_3692_);
return v___x_3693_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__2(void){
_start:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; 
v___x_3700_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkDecl___boxed), 4, 0);
v___x_3701_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_3701_, 0, v___x_3700_);
return v___x_3701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1(){
_start:
{
lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; 
v___x_3703_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__1));
v___x_3704_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__2, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__2_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__2);
v___x_3705_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_3703_, v___x_3704_);
return v___x_3705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___boxed(lean_object* v_a_3706_){
_start:
{
lean_object* v_res_3707_; 
v_res_3707_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1();
return v_res_3707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkInit(lean_object* v_stx_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_){
_start:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; uint8_t v___x_3715_; 
v___x_3713_ = lean_unsigned_to_nat(2u);
v___x_3714_ = l_Lean_Syntax_getArg(v_stx_3709_, v___x_3713_);
v___x_3715_ = l_Lean_Syntax_isNone(v___x_3714_);
if (v___x_3715_ == 0)
{
lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3716_ = lean_unsigned_to_nat(0u);
v___x_3717_ = l_Lean_Syntax_getArg(v_stx_3709_, v___x_3716_);
v___x_3718_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v___x_3717_, v_a_3710_, v_a_3711_);
lean_dec(v___x_3717_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_object* v_a_3719_; lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3732_; 
v_a_3719_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3721_ = v___x_3718_;
v_isShared_3722_ = v_isSharedCheck_3732_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_a_3719_);
lean_dec(v___x_3718_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3732_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
if (lean_obj_tag(v_a_3719_) == 1)
{
lean_object* v_val_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; uint8_t v___x_3726_; lean_object* v___x_3727_; 
lean_del_object(v___x_3721_);
v_val_3723_ = lean_ctor_get(v_a_3719_, 0);
lean_inc(v_val_3723_);
lean_dec_ref_known(v_a_3719_, 1);
v___x_3724_ = l_Lean_Syntax_getArg(v___x_3714_, v___x_3716_);
lean_dec(v___x_3714_);
v___x_3725_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkInit___closed__0));
v___x_3726_ = lean_unbox(v_val_3723_);
lean_dec(v_val_3723_);
v___x_3727_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v___x_3726_, v___x_3724_, v___x_3725_, v_a_3710_, v_a_3711_);
return v___x_3727_;
}
else
{
lean_object* v___x_3728_; lean_object* v___x_3730_; 
lean_dec(v_a_3719_);
lean_dec(v___x_3714_);
v___x_3728_ = lean_box(0);
if (v_isShared_3722_ == 0)
{
lean_ctor_set(v___x_3721_, 0, v___x_3728_);
v___x_3730_ = v___x_3721_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v___x_3728_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
}
}
else
{
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3740_; 
lean_dec(v___x_3714_);
v_a_3733_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3735_ = v___x_3718_;
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3718_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3738_; 
if (v_isShared_3736_ == 0)
{
v___x_3738_ = v___x_3735_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_a_3733_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
}
else
{
lean_object* v___x_3741_; lean_object* v___x_3742_; 
lean_dec(v___x_3714_);
v___x_3741_ = lean_box(0);
v___x_3742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3742_, 0, v___x_3741_);
return v___x_3742_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkInit___boxed(lean_object* v_stx_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_){
_start:
{
lean_object* v_res_3747_; 
v_res_3747_ = l_Lean_Linter_MissingDocs_checkInit(v_stx_3743_, v_a_3744_, v_a_3745_);
lean_dec(v_a_3745_);
lean_dec_ref(v_a_3744_);
lean_dec(v_stx_3743_);
return v_res_3747_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__2(void){
_start:
{
lean_object* v___x_3754_; lean_object* v___x_3755_; 
v___x_3754_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkInit___boxed), 4, 0);
v___x_3755_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_3755_, 0, v___x_3754_);
return v___x_3755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1(){
_start:
{
lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; 
v___x_3757_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__1));
v___x_3758_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__2, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__2_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__2);
v___x_3759_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_3757_, v___x_3758_);
return v___x_3759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___boxed(lean_object* v_a_3760_){
_start:
{
lean_object* v_res_3761_; 
v_res_3761_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1();
return v_res_3761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkNotation(lean_object* v_stx_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_){
_start:
{
lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; uint8_t v___x_3780_; 
v___x_3773_ = lean_unsigned_to_nat(2u);
v___x_3774_ = l_Lean_Syntax_getArg(v_stx_3769_, v___x_3773_);
v___x_3775_ = lean_unsigned_to_nat(0u);
v___x_3776_ = l_Lean_Syntax_getArg(v___x_3774_, v___x_3775_);
lean_dec(v___x_3774_);
v___x_3777_ = l_Lean_Syntax_getArg(v___x_3776_, v___x_3775_);
lean_dec(v___x_3776_);
v___x_3778_ = l_Lean_Syntax_getKind(v___x_3777_);
v___x_3779_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkNotation___closed__1));
v___x_3780_ = lean_name_eq(v___x_3778_, v___x_3779_);
lean_dec(v___x_3778_);
if (v___x_3780_ == 0)
{
lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; 
v___x_3781_ = l_Lean_Syntax_getArg(v_stx_3769_, v___x_3775_);
v___x_3782_ = lean_unsigned_to_nat(1u);
v___x_3783_ = l_Lean_Syntax_getArg(v_stx_3769_, v___x_3782_);
v___x_3784_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus(v___x_3781_, v___x_3783_, v___x_3780_, v_a_3770_, v_a_3771_);
lean_dec(v___x_3783_);
lean_dec(v___x_3781_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v_a_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3808_; 
v_a_3785_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3787_ = v___x_3784_;
v_isShared_3788_ = v_isSharedCheck_3808_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_a_3785_);
lean_dec(v___x_3784_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3808_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
if (lean_obj_tag(v_a_3785_) == 1)
{
lean_object* v_val_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; uint8_t v___x_3792_; 
lean_del_object(v___x_3787_);
v_val_3789_ = lean_ctor_get(v_a_3785_, 0);
lean_inc(v_val_3789_);
lean_dec_ref_known(v_a_3785_, 1);
v___x_3790_ = lean_unsigned_to_nat(5u);
v___x_3791_ = l_Lean_Syntax_getArg(v_stx_3769_, v___x_3790_);
v___x_3792_ = l_Lean_Syntax_isNone(v___x_3791_);
if (v___x_3792_ == 0)
{
lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; uint8_t v___x_3797_; lean_object* v___x_3798_; 
v___x_3793_ = l_Lean_Syntax_getArg(v___x_3791_, v___x_3775_);
lean_dec(v___x_3791_);
v___x_3794_ = lean_unsigned_to_nat(3u);
v___x_3795_ = l_Lean_Syntax_getArg(v___x_3793_, v___x_3794_);
lean_dec(v___x_3793_);
v___x_3796_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkNotation___closed__2));
v___x_3797_ = lean_unbox(v_val_3789_);
lean_dec(v_val_3789_);
v___x_3798_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v___x_3797_, v___x_3795_, v___x_3796_, v_a_3770_, v_a_3771_);
return v___x_3798_;
}
else
{
lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; uint8_t v___x_3802_; lean_object* v___x_3803_; 
lean_dec(v___x_3791_);
v___x_3799_ = lean_unsigned_to_nat(3u);
v___x_3800_ = l_Lean_Syntax_getArg(v_stx_3769_, v___x_3799_);
v___x_3801_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkNotation___closed__2));
v___x_3802_ = lean_unbox(v_val_3789_);
lean_dec(v_val_3789_);
v___x_3803_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus(v___x_3802_, v___x_3800_, v___x_3801_, v_a_3770_, v_a_3771_);
return v___x_3803_;
}
}
else
{
lean_object* v___x_3804_; lean_object* v___x_3806_; 
lean_dec(v_a_3785_);
v___x_3804_ = lean_box(0);
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 0, v___x_3804_);
v___x_3806_ = v___x_3787_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v___x_3804_);
v___x_3806_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
return v___x_3806_;
}
}
}
}
else
{
lean_object* v_a_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3816_; 
v_a_3809_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3816_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3811_ = v___x_3784_;
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_a_3809_);
lean_dec(v___x_3784_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3814_; 
if (v_isShared_3812_ == 0)
{
v___x_3814_ = v___x_3811_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_a_3809_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
}
else
{
lean_object* v___x_3817_; lean_object* v___x_3818_; 
v___x_3817_ = lean_box(0);
v___x_3818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3818_, 0, v___x_3817_);
return v___x_3818_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkNotation___boxed(lean_object* v_stx_3819_, lean_object* v_a_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_){
_start:
{
lean_object* v_res_3823_; 
v_res_3823_ = l_Lean_Linter_MissingDocs_checkNotation(v_stx_3819_, v_a_3820_, v_a_3821_);
lean_dec(v_a_3821_);
lean_dec_ref(v_a_3820_);
lean_dec(v_stx_3819_);
return v_res_3823_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___closed__1(void){
_start:
{
lean_object* v___x_3829_; lean_object* v___x_3830_; 
v___x_3829_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkNotation___boxed), 4, 0);
v___x_3830_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_3830_, 0, v___x_3829_);
return v___x_3830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1(){
_start:
{
lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; 
v___x_3832_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___closed__0));
v___x_3833_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___closed__1, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___closed__1_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___closed__1);
v___x_3834_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_3832_, v___x_3833_);
return v___x_3834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___boxed(lean_object* v_a_3835_){
_start:
{
lean_object* v_res_3836_; 
v_res_3836_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1();
return v_res_3836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkMixfix(lean_object* v_stx_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_){
_start:
{
lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; uint8_t v___x_3848_; 
v___x_3841_ = lean_unsigned_to_nat(2u);
v___x_3842_ = l_Lean_Syntax_getArg(v_stx_3837_, v___x_3841_);
v___x_3843_ = lean_unsigned_to_nat(0u);
v___x_3844_ = l_Lean_Syntax_getArg(v___x_3842_, v___x_3843_);
lean_dec(v___x_3842_);
v___x_3845_ = l_Lean_Syntax_getArg(v___x_3844_, v___x_3843_);
lean_dec(v___x_3844_);
v___x_3846_ = l_Lean_Syntax_getKind(v___x_3845_);
v___x_3847_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkNotation___closed__1));
v___x_3848_ = lean_name_eq(v___x_3846_, v___x_3847_);
lean_dec(v___x_3846_);
if (v___x_3848_ == 0)
{
lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; 
v___x_3849_ = l_Lean_Syntax_getArg(v_stx_3837_, v___x_3843_);
v___x_3850_ = lean_unsigned_to_nat(1u);
v___x_3851_ = l_Lean_Syntax_getArg(v_stx_3837_, v___x_3850_);
v___x_3852_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus(v___x_3849_, v___x_3851_, v___x_3848_, v_a_3838_, v_a_3839_);
lean_dec(v___x_3851_);
lean_dec(v___x_3849_);
if (lean_obj_tag(v___x_3852_) == 0)
{
lean_object* v_a_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3879_; 
v_a_3853_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_3879_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3855_ = v___x_3852_;
v_isShared_3856_ = v_isSharedCheck_3879_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_a_3853_);
lean_dec(v___x_3852_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3879_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
if (lean_obj_tag(v_a_3853_) == 1)
{
lean_object* v_val_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; uint8_t v___x_3860_; 
lean_del_object(v___x_3855_);
v_val_3857_ = lean_ctor_get(v_a_3853_, 0);
lean_inc(v_val_3857_);
lean_dec_ref_known(v_a_3853_, 1);
v___x_3858_ = lean_unsigned_to_nat(5u);
v___x_3859_ = l_Lean_Syntax_getArg(v_stx_3837_, v___x_3858_);
v___x_3860_ = l_Lean_Syntax_isNone(v___x_3859_);
if (v___x_3860_ == 0)
{
lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; uint8_t v___x_3867_; lean_object* v___x_3868_; 
v___x_3861_ = l_Lean_Syntax_getArg(v___x_3859_, v___x_3843_);
lean_dec(v___x_3859_);
v___x_3862_ = lean_unsigned_to_nat(3u);
v___x_3863_ = l_Lean_Syntax_getArg(v___x_3861_, v___x_3862_);
lean_dec(v___x_3861_);
v___x_3864_ = l_Lean_Syntax_getArg(v_stx_3837_, v___x_3862_);
v___x_3865_ = l_Lean_Syntax_getArg(v___x_3864_, v___x_3843_);
lean_dec(v___x_3864_);
v___x_3866_ = l_Lean_Syntax_getAtomVal(v___x_3865_);
lean_dec(v___x_3865_);
v___x_3867_ = lean_unbox(v_val_3857_);
lean_dec(v_val_3857_);
v___x_3868_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v___x_3867_, v___x_3863_, v___x_3866_, v_a_3838_, v_a_3839_);
return v___x_3868_;
}
else
{
lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; uint8_t v___x_3873_; lean_object* v___x_3874_; 
lean_dec(v___x_3859_);
v___x_3869_ = lean_unsigned_to_nat(3u);
v___x_3870_ = l_Lean_Syntax_getArg(v_stx_3837_, v___x_3869_);
v___x_3871_ = l_Lean_Syntax_getArg(v___x_3870_, v___x_3843_);
v___x_3872_ = l_Lean_Syntax_getAtomVal(v___x_3871_);
lean_dec(v___x_3871_);
v___x_3873_ = lean_unbox(v_val_3857_);
lean_dec(v_val_3857_);
v___x_3874_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus(v___x_3873_, v___x_3870_, v___x_3872_, v_a_3838_, v_a_3839_);
return v___x_3874_;
}
}
else
{
lean_object* v___x_3875_; lean_object* v___x_3877_; 
lean_dec(v_a_3853_);
v___x_3875_ = lean_box(0);
if (v_isShared_3856_ == 0)
{
lean_ctor_set(v___x_3855_, 0, v___x_3875_);
v___x_3877_ = v___x_3855_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v___x_3875_);
v___x_3877_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
return v___x_3877_;
}
}
}
}
else
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3887_; 
v_a_3880_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3882_ = v___x_3852_;
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3852_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3885_; 
if (v_isShared_3883_ == 0)
{
v___x_3885_ = v___x_3882_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_a_3880_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
}
}
else
{
lean_object* v___x_3888_; lean_object* v___x_3889_; 
v___x_3888_ = lean_box(0);
v___x_3889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3888_);
return v___x_3889_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkMixfix___boxed(lean_object* v_stx_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_){
_start:
{
lean_object* v_res_3894_; 
v_res_3894_ = l_Lean_Linter_MissingDocs_checkMixfix(v_stx_3890_, v_a_3891_, v_a_3892_);
lean_dec(v_a_3892_);
lean_dec_ref(v_a_3891_);
lean_dec(v_stx_3890_);
return v_res_3894_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__2(void){
_start:
{
lean_object* v___x_3901_; lean_object* v___x_3902_; 
v___x_3901_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkMixfix___boxed), 4, 0);
v___x_3902_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_3902_, 0, v___x_3901_);
return v___x_3902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1(){
_start:
{
lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; 
v___x_3904_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__1));
v___x_3905_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__2, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__2_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__2);
v___x_3906_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_3904_, v___x_3905_);
return v___x_3906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___boxed(lean_object* v_a_3907_){
_start:
{
lean_object* v_res_3908_; 
v_res_3908_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1();
return v_res_3908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntax(lean_object* v_stx_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_){
_start:
{
lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; uint8_t v___x_3921_; 
v___x_3914_ = lean_unsigned_to_nat(2u);
v___x_3915_ = l_Lean_Syntax_getArg(v_stx_3910_, v___x_3914_);
v___x_3916_ = lean_unsigned_to_nat(0u);
v___x_3917_ = l_Lean_Syntax_getArg(v___x_3915_, v___x_3916_);
lean_dec(v___x_3915_);
v___x_3918_ = l_Lean_Syntax_getArg(v___x_3917_, v___x_3916_);
lean_dec(v___x_3917_);
v___x_3919_ = l_Lean_Syntax_getKind(v___x_3918_);
v___x_3920_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkNotation___closed__1));
v___x_3921_ = lean_name_eq(v___x_3919_, v___x_3920_);
lean_dec(v___x_3919_);
if (v___x_3921_ == 0)
{
uint8_t v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
v___x_3922_ = 1;
v___x_3923_ = l_Lean_Syntax_getArg(v_stx_3910_, v___x_3916_);
v___x_3924_ = lean_unsigned_to_nat(1u);
v___x_3925_ = l_Lean_Syntax_getArg(v_stx_3910_, v___x_3924_);
v___x_3926_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus(v___x_3923_, v___x_3925_, v___x_3922_, v_a_3911_, v_a_3912_);
lean_dec(v___x_3925_);
lean_dec(v___x_3923_);
if (lean_obj_tag(v___x_3926_) == 0)
{
lean_object* v_a_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3950_; 
v_a_3927_ = lean_ctor_get(v___x_3926_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3926_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3929_ = v___x_3926_;
v_isShared_3930_ = v_isSharedCheck_3950_;
goto v_resetjp_3928_;
}
else
{
lean_inc(v_a_3927_);
lean_dec(v___x_3926_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3950_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
if (lean_obj_tag(v_a_3927_) == 1)
{
lean_object* v_val_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; uint8_t v___x_3934_; 
lean_del_object(v___x_3929_);
v_val_3931_ = lean_ctor_get(v_a_3927_, 0);
lean_inc(v_val_3931_);
lean_dec_ref_known(v_a_3927_, 1);
v___x_3932_ = lean_unsigned_to_nat(5u);
v___x_3933_ = l_Lean_Syntax_getArg(v_stx_3910_, v___x_3932_);
v___x_3934_ = l_Lean_Syntax_isNone(v___x_3933_);
if (v___x_3934_ == 0)
{
lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; uint8_t v___x_3939_; lean_object* v___x_3940_; 
v___x_3935_ = l_Lean_Syntax_getArg(v___x_3933_, v___x_3916_);
lean_dec(v___x_3933_);
v___x_3936_ = lean_unsigned_to_nat(3u);
v___x_3937_ = l_Lean_Syntax_getArg(v___x_3935_, v___x_3936_);
lean_dec(v___x_3935_);
v___x_3938_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkSyntax___closed__0));
v___x_3939_ = lean_unbox(v_val_3931_);
lean_dec(v_val_3931_);
v___x_3940_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v___x_3939_, v___x_3937_, v___x_3938_, v_a_3911_, v_a_3912_);
return v___x_3940_;
}
else
{
lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; uint8_t v___x_3944_; lean_object* v___x_3945_; 
lean_dec(v___x_3933_);
v___x_3941_ = lean_unsigned_to_nat(3u);
v___x_3942_ = l_Lean_Syntax_getArg(v_stx_3910_, v___x_3941_);
v___x_3943_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkSyntax___closed__0));
v___x_3944_ = lean_unbox(v_val_3931_);
lean_dec(v_val_3931_);
v___x_3945_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus(v___x_3944_, v___x_3942_, v___x_3943_, v_a_3911_, v_a_3912_);
return v___x_3945_;
}
}
else
{
lean_object* v___x_3946_; lean_object* v___x_3948_; 
lean_dec(v_a_3927_);
v___x_3946_ = lean_box(0);
if (v_isShared_3930_ == 0)
{
lean_ctor_set(v___x_3929_, 0, v___x_3946_);
v___x_3948_ = v___x_3929_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v___x_3946_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
return v___x_3948_;
}
}
}
}
else
{
lean_object* v_a_3951_; lean_object* v___x_3953_; uint8_t v_isShared_3954_; uint8_t v_isSharedCheck_3958_; 
v_a_3951_ = lean_ctor_get(v___x_3926_, 0);
v_isSharedCheck_3958_ = !lean_is_exclusive(v___x_3926_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3953_ = v___x_3926_;
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
else
{
lean_inc(v_a_3951_);
lean_dec(v___x_3926_);
v___x_3953_ = lean_box(0);
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
v_resetjp_3952_:
{
lean_object* v___x_3956_; 
if (v_isShared_3954_ == 0)
{
v___x_3956_ = v___x_3953_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_a_3951_);
v___x_3956_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
return v___x_3956_;
}
}
}
}
else
{
lean_object* v___x_3959_; lean_object* v___x_3960_; 
v___x_3959_ = lean_box(0);
v___x_3960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3960_, 0, v___x_3959_);
return v___x_3960_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntax___boxed(lean_object* v_stx_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_){
_start:
{
lean_object* v_res_3965_; 
v_res_3965_ = l_Lean_Linter_MissingDocs_checkSyntax(v_stx_3961_, v_a_3962_, v_a_3963_);
lean_dec(v_a_3963_);
lean_dec_ref(v_a_3962_);
lean_dec(v_stx_3961_);
return v_res_3965_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___closed__1(void){
_start:
{
lean_object* v___x_3971_; lean_object* v___x_3972_; 
v___x_3971_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkSyntax___boxed), 4, 0);
v___x_3972_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_3972_, 0, v___x_3971_);
return v___x_3972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1(){
_start:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; 
v___x_3974_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___closed__0));
v___x_3975_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___closed__1, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___closed__1_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___closed__1);
v___x_3976_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_3974_, v___x_3975_);
return v___x_3976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___boxed(lean_object* v_a_3977_){
_start:
{
lean_object* v_res_3978_; 
v_res_3978_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1();
return v_res_3978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_mkSimpleHandler(lean_object* v_name_3979_, lean_object* v_declNameStxIdx_3980_, lean_object* v_stx_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_){
_start:
{
lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; 
v___x_3985_ = lean_unsigned_to_nat(0u);
v___x_3986_ = l_Lean_Syntax_getArg(v_stx_3981_, v___x_3985_);
v___x_3987_ = l_Lean_Linter_MissingDocs_isMissingDoc(v___x_3986_, v_a_3982_, v_a_3983_);
if (lean_obj_tag(v___x_3987_) == 0)
{
lean_object* v_a_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_4012_; 
v_a_3988_ = lean_ctor_get(v___x_3987_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_3990_ = v___x_3987_;
v_isShared_3991_ = v_isSharedCheck_4012_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_a_3988_);
lean_dec(v___x_3987_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_4012_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
uint8_t v___x_3992_; 
v___x_3992_ = lean_unbox(v_a_3988_);
lean_dec(v_a_3988_);
if (v___x_3992_ == 0)
{
lean_object* v___x_3993_; lean_object* v___x_3995_; 
lean_dec(v___x_3986_);
lean_dec_ref(v_name_3979_);
v___x_3993_ = lean_box(0);
if (v_isShared_3991_ == 0)
{
lean_ctor_set(v___x_3990_, 0, v___x_3993_);
v___x_3995_ = v___x_3990_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v___x_3993_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
else
{
lean_object* v___x_3997_; 
lean_del_object(v___x_3990_);
v___x_3997_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString(v___x_3986_, v_a_3982_, v_a_3983_);
lean_dec(v___x_3986_);
if (lean_obj_tag(v___x_3997_) == 0)
{
lean_object* v_a_3998_; uint8_t v___x_3999_; 
v_a_3998_ = lean_ctor_get(v___x_3997_, 0);
lean_inc(v_a_3998_);
lean_dec_ref_known(v___x_3997_, 1);
v___x_3999_ = lean_unbox(v_a_3998_);
lean_dec(v_a_3998_);
if (v___x_3999_ == 0)
{
lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_4000_ = l_Lean_Syntax_getArg(v_stx_3981_, v_declNameStxIdx_3980_);
v___x_4001_ = l_Lean_Linter_MissingDocs_lintNamed(v___x_4000_, v_name_3979_, v_a_3982_, v_a_3983_);
return v___x_4001_;
}
else
{
lean_object* v___x_4002_; lean_object* v___x_4003_; 
v___x_4002_ = l_Lean_Syntax_getArg(v_stx_3981_, v_declNameStxIdx_3980_);
v___x_4003_ = l_Lean_Linter_MissingDocs_lintEmptyNamed(v___x_4002_, v_name_3979_, v_a_3982_, v_a_3983_);
return v___x_4003_;
}
}
else
{
lean_object* v_a_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4011_; 
lean_dec_ref(v_name_3979_);
v_a_4004_ = lean_ctor_get(v___x_3997_, 0);
v_isSharedCheck_4011_ = !lean_is_exclusive(v___x_3997_);
if (v_isSharedCheck_4011_ == 0)
{
v___x_4006_ = v___x_3997_;
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_a_4004_);
lean_dec(v___x_3997_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v___x_4009_; 
if (v_isShared_4007_ == 0)
{
v___x_4009_ = v___x_4006_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v_a_4004_);
v___x_4009_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
return v___x_4009_;
}
}
}
}
}
}
else
{
lean_object* v_a_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4020_; 
lean_dec(v___x_3986_);
lean_dec_ref(v_name_3979_);
v_a_4013_ = lean_ctor_get(v___x_3987_, 0);
v_isSharedCheck_4020_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_4015_ = v___x_3987_;
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_a_4013_);
lean_dec(v___x_3987_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v___x_4018_; 
if (v_isShared_4016_ == 0)
{
v___x_4018_ = v___x_4015_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v_a_4013_);
v___x_4018_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
return v___x_4018_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_mkSimpleHandler___boxed(lean_object* v_name_4021_, lean_object* v_declNameStxIdx_4022_, lean_object* v_stx_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_){
_start:
{
lean_object* v_res_4027_; 
v_res_4027_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v_name_4021_, v_declNameStxIdx_4022_, v_stx_4023_, v_a_4024_, v_a_4025_);
lean_dec(v_a_4025_);
lean_dec_ref(v_a_4024_);
lean_dec(v_stx_4023_);
lean_dec(v_declNameStxIdx_4022_);
return v_res_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntaxAbbrev(lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_){
_start:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; 
v___x_4032_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkSyntax___closed__0));
v___x_4033_ = lean_unsigned_to_nat(2u);
v___x_4034_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_4032_, v___x_4033_, v_a_4028_, v_a_4029_, v_a_4030_);
return v___x_4034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntaxAbbrev___boxed(lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_){
_start:
{
lean_object* v_res_4039_; 
v_res_4039_ = l_Lean_Linter_MissingDocs_checkSyntaxAbbrev(v_a_4035_, v_a_4036_, v_a_4037_);
lean_dec(v_a_4037_);
lean_dec_ref(v_a_4036_);
lean_dec(v_a_4035_);
return v_res_4039_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__2(void){
_start:
{
lean_object* v___x_4046_; lean_object* v___x_4047_; 
v___x_4046_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkSyntaxAbbrev___boxed), 4, 0);
v___x_4047_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4047_, 0, v___x_4046_);
return v___x_4047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1(){
_start:
{
lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; 
v___x_4049_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__1));
v___x_4050_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__2, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__2_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__2);
v___x_4051_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4049_, v___x_4050_);
return v___x_4051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___boxed(lean_object* v_a_4052_){
_start:
{
lean_object* v_res_4053_; 
v_res_4053_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1();
return v_res_4053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntaxCat(lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_){
_start:
{
lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4059_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkSyntaxCat___closed__0));
v___x_4060_ = lean_unsigned_to_nat(2u);
v___x_4061_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_4059_, v___x_4060_, v_a_4055_, v_a_4056_, v_a_4057_);
return v___x_4061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntaxCat___boxed(lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_){
_start:
{
lean_object* v_res_4066_; 
v_res_4066_ = l_Lean_Linter_MissingDocs_checkSyntaxCat(v_a_4062_, v_a_4063_, v_a_4064_);
lean_dec(v_a_4064_);
lean_dec_ref(v_a_4063_);
lean_dec(v_a_4062_);
return v_res_4066_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__2(void){
_start:
{
lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4073_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkSyntaxCat___boxed), 4, 0);
v___x_4074_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4074_, 0, v___x_4073_);
return v___x_4074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1(){
_start:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4076_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__1));
v___x_4077_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__2, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__2_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__2);
v___x_4078_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4076_, v___x_4077_);
return v___x_4078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___boxed(lean_object* v_a_4079_){
_start:
{
lean_object* v_res_4080_; 
v_res_4080_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1();
return v_res_4080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkMacro(lean_object* v_stx_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_){
_start:
{
lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; uint8_t v___x_4093_; 
v___x_4086_ = lean_unsigned_to_nat(2u);
v___x_4087_ = l_Lean_Syntax_getArg(v_stx_4082_, v___x_4086_);
v___x_4088_ = lean_unsigned_to_nat(0u);
v___x_4089_ = l_Lean_Syntax_getArg(v___x_4087_, v___x_4088_);
lean_dec(v___x_4087_);
v___x_4090_ = l_Lean_Syntax_getArg(v___x_4089_, v___x_4088_);
lean_dec(v___x_4089_);
v___x_4091_ = l_Lean_Syntax_getKind(v___x_4090_);
v___x_4092_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkNotation___closed__1));
v___x_4093_ = lean_name_eq(v___x_4091_, v___x_4092_);
lean_dec(v___x_4091_);
if (v___x_4093_ == 0)
{
uint8_t v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
v___x_4094_ = 1;
v___x_4095_ = l_Lean_Syntax_getArg(v_stx_4082_, v___x_4088_);
v___x_4096_ = lean_unsigned_to_nat(1u);
v___x_4097_ = l_Lean_Syntax_getArg(v_stx_4082_, v___x_4096_);
v___x_4098_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus(v___x_4095_, v___x_4097_, v___x_4094_, v_a_4083_, v_a_4084_);
lean_dec(v___x_4097_);
lean_dec(v___x_4095_);
if (lean_obj_tag(v___x_4098_) == 0)
{
lean_object* v_a_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4122_; 
v_a_4099_ = lean_ctor_get(v___x_4098_, 0);
v_isSharedCheck_4122_ = !lean_is_exclusive(v___x_4098_);
if (v_isSharedCheck_4122_ == 0)
{
v___x_4101_ = v___x_4098_;
v_isShared_4102_ = v_isSharedCheck_4122_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_a_4099_);
lean_dec(v___x_4098_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4122_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
if (lean_obj_tag(v_a_4099_) == 1)
{
lean_object* v_val_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; uint8_t v___x_4106_; 
lean_del_object(v___x_4101_);
v_val_4103_ = lean_ctor_get(v_a_4099_, 0);
lean_inc(v_val_4103_);
lean_dec_ref_known(v_a_4099_, 1);
v___x_4104_ = lean_unsigned_to_nat(5u);
v___x_4105_ = l_Lean_Syntax_getArg(v_stx_4082_, v___x_4104_);
v___x_4106_ = l_Lean_Syntax_isNone(v___x_4105_);
if (v___x_4106_ == 0)
{
lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; uint8_t v___x_4111_; lean_object* v___x_4112_; 
v___x_4107_ = l_Lean_Syntax_getArg(v___x_4105_, v___x_4088_);
lean_dec(v___x_4105_);
v___x_4108_ = lean_unsigned_to_nat(3u);
v___x_4109_ = l_Lean_Syntax_getArg(v___x_4107_, v___x_4108_);
lean_dec(v___x_4107_);
v___x_4110_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkMacro___closed__0));
v___x_4111_ = lean_unbox(v_val_4103_);
lean_dec(v_val_4103_);
v___x_4112_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v___x_4111_, v___x_4109_, v___x_4110_, v_a_4083_, v_a_4084_);
return v___x_4112_;
}
else
{
lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; uint8_t v___x_4116_; lean_object* v___x_4117_; 
lean_dec(v___x_4105_);
v___x_4113_ = lean_unsigned_to_nat(3u);
v___x_4114_ = l_Lean_Syntax_getArg(v_stx_4082_, v___x_4113_);
v___x_4115_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkMacro___closed__0));
v___x_4116_ = lean_unbox(v_val_4103_);
lean_dec(v_val_4103_);
v___x_4117_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus(v___x_4116_, v___x_4114_, v___x_4115_, v_a_4083_, v_a_4084_);
return v___x_4117_;
}
}
else
{
lean_object* v___x_4118_; lean_object* v___x_4120_; 
lean_dec(v_a_4099_);
v___x_4118_ = lean_box(0);
if (v_isShared_4102_ == 0)
{
lean_ctor_set(v___x_4101_, 0, v___x_4118_);
v___x_4120_ = v___x_4101_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v___x_4118_);
v___x_4120_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
return v___x_4120_;
}
}
}
}
else
{
lean_object* v_a_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4130_; 
v_a_4123_ = lean_ctor_get(v___x_4098_, 0);
v_isSharedCheck_4130_ = !lean_is_exclusive(v___x_4098_);
if (v_isSharedCheck_4130_ == 0)
{
v___x_4125_ = v___x_4098_;
v_isShared_4126_ = v_isSharedCheck_4130_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_a_4123_);
lean_dec(v___x_4098_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4130_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
lean_object* v___x_4128_; 
if (v_isShared_4126_ == 0)
{
v___x_4128_ = v___x_4125_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4129_; 
v_reuseFailAlloc_4129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4129_, 0, v_a_4123_);
v___x_4128_ = v_reuseFailAlloc_4129_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
return v___x_4128_;
}
}
}
}
else
{
lean_object* v___x_4131_; lean_object* v___x_4132_; 
v___x_4131_ = lean_box(0);
v___x_4132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4131_);
return v___x_4132_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkMacro___boxed(lean_object* v_stx_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_){
_start:
{
lean_object* v_res_4137_; 
v_res_4137_ = l_Lean_Linter_MissingDocs_checkMacro(v_stx_4133_, v_a_4134_, v_a_4135_);
lean_dec(v_a_4135_);
lean_dec_ref(v_a_4134_);
lean_dec(v_stx_4133_);
return v_res_4137_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___closed__1(void){
_start:
{
lean_object* v___x_4143_; lean_object* v___x_4144_; 
v___x_4143_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkMacro___boxed), 4, 0);
v___x_4144_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4144_, 0, v___x_4143_);
return v___x_4144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1(){
_start:
{
lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; 
v___x_4146_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___closed__0));
v___x_4147_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___closed__1, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___closed__1_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___closed__1);
v___x_4148_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4146_, v___x_4147_);
return v___x_4148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___boxed(lean_object* v_a_4149_){
_start:
{
lean_object* v_res_4150_; 
v_res_4150_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1();
return v_res_4150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkElab(lean_object* v_stx_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_){
_start:
{
lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; uint8_t v___x_4163_; 
v___x_4156_ = lean_unsigned_to_nat(2u);
v___x_4157_ = l_Lean_Syntax_getArg(v_stx_4152_, v___x_4156_);
v___x_4158_ = lean_unsigned_to_nat(0u);
v___x_4159_ = l_Lean_Syntax_getArg(v___x_4157_, v___x_4158_);
lean_dec(v___x_4157_);
v___x_4160_ = l_Lean_Syntax_getArg(v___x_4159_, v___x_4158_);
lean_dec(v___x_4159_);
v___x_4161_ = l_Lean_Syntax_getKind(v___x_4160_);
v___x_4162_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkNotation___closed__1));
v___x_4163_ = lean_name_eq(v___x_4161_, v___x_4162_);
lean_dec(v___x_4161_);
if (v___x_4163_ == 0)
{
uint8_t v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; 
v___x_4164_ = 1;
v___x_4165_ = l_Lean_Syntax_getArg(v_stx_4152_, v___x_4158_);
v___x_4166_ = lean_unsigned_to_nat(1u);
v___x_4167_ = l_Lean_Syntax_getArg(v_stx_4152_, v___x_4166_);
v___x_4168_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus(v___x_4165_, v___x_4167_, v___x_4164_, v_a_4153_, v_a_4154_);
lean_dec(v___x_4167_);
lean_dec(v___x_4165_);
if (lean_obj_tag(v___x_4168_) == 0)
{
lean_object* v_a_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4192_; 
v_a_4169_ = lean_ctor_get(v___x_4168_, 0);
v_isSharedCheck_4192_ = !lean_is_exclusive(v___x_4168_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4171_ = v___x_4168_;
v_isShared_4172_ = v_isSharedCheck_4192_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_a_4169_);
lean_dec(v___x_4168_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4192_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
if (lean_obj_tag(v_a_4169_) == 1)
{
lean_object* v_val_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; uint8_t v___x_4176_; 
lean_del_object(v___x_4171_);
v_val_4173_ = lean_ctor_get(v_a_4169_, 0);
lean_inc(v_val_4173_);
lean_dec_ref_known(v_a_4169_, 1);
v___x_4174_ = lean_unsigned_to_nat(5u);
v___x_4175_ = l_Lean_Syntax_getArg(v_stx_4152_, v___x_4174_);
v___x_4176_ = l_Lean_Syntax_isNone(v___x_4175_);
if (v___x_4176_ == 0)
{
lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; uint8_t v___x_4181_; lean_object* v___x_4182_; 
v___x_4177_ = l_Lean_Syntax_getArg(v___x_4175_, v___x_4158_);
lean_dec(v___x_4175_);
v___x_4178_ = lean_unsigned_to_nat(3u);
v___x_4179_ = l_Lean_Syntax_getArg(v___x_4177_, v___x_4178_);
lean_dec(v___x_4177_);
v___x_4180_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkElab___closed__0));
v___x_4181_ = lean_unbox(v_val_4173_);
lean_dec(v_val_4173_);
v___x_4182_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v___x_4181_, v___x_4179_, v___x_4180_, v_a_4153_, v_a_4154_);
return v___x_4182_;
}
else
{
lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; uint8_t v___x_4186_; lean_object* v___x_4187_; 
lean_dec(v___x_4175_);
v___x_4183_ = lean_unsigned_to_nat(3u);
v___x_4184_ = l_Lean_Syntax_getArg(v_stx_4152_, v___x_4183_);
v___x_4185_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkElab___closed__0));
v___x_4186_ = lean_unbox(v_val_4173_);
lean_dec(v_val_4173_);
v___x_4187_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus(v___x_4186_, v___x_4184_, v___x_4185_, v_a_4153_, v_a_4154_);
return v___x_4187_;
}
}
else
{
lean_object* v___x_4188_; lean_object* v___x_4190_; 
lean_dec(v_a_4169_);
v___x_4188_ = lean_box(0);
if (v_isShared_4172_ == 0)
{
lean_ctor_set(v___x_4171_, 0, v___x_4188_);
v___x_4190_ = v___x_4171_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v___x_4188_);
v___x_4190_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
return v___x_4190_;
}
}
}
}
else
{
lean_object* v_a_4193_; lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4200_; 
v_a_4193_ = lean_ctor_get(v___x_4168_, 0);
v_isSharedCheck_4200_ = !lean_is_exclusive(v___x_4168_);
if (v_isSharedCheck_4200_ == 0)
{
v___x_4195_ = v___x_4168_;
v_isShared_4196_ = v_isSharedCheck_4200_;
goto v_resetjp_4194_;
}
else
{
lean_inc(v_a_4193_);
lean_dec(v___x_4168_);
v___x_4195_ = lean_box(0);
v_isShared_4196_ = v_isSharedCheck_4200_;
goto v_resetjp_4194_;
}
v_resetjp_4194_:
{
lean_object* v___x_4198_; 
if (v_isShared_4196_ == 0)
{
v___x_4198_ = v___x_4195_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4199_; 
v_reuseFailAlloc_4199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4199_, 0, v_a_4193_);
v___x_4198_ = v_reuseFailAlloc_4199_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
return v___x_4198_;
}
}
}
}
else
{
lean_object* v___x_4201_; lean_object* v___x_4202_; 
v___x_4201_ = lean_box(0);
v___x_4202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4202_, 0, v___x_4201_);
return v___x_4202_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkElab___boxed(lean_object* v_stx_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_){
_start:
{
lean_object* v_res_4207_; 
v_res_4207_ = l_Lean_Linter_MissingDocs_checkElab(v_stx_4203_, v_a_4204_, v_a_4205_);
lean_dec(v_a_4205_);
lean_dec_ref(v_a_4204_);
lean_dec(v_stx_4203_);
return v_res_4207_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___closed__1(void){
_start:
{
lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___x_4213_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkElab___boxed), 4, 0);
v___x_4214_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4214_, 0, v___x_4213_);
return v___x_4214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1(){
_start:
{
lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; 
v___x_4216_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___closed__0));
v___x_4217_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___closed__1, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___closed__1_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___closed__1);
v___x_4218_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4216_, v___x_4217_);
return v___x_4218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___boxed(lean_object* v_a_4219_){
_start:
{
lean_object* v_res_4220_; 
v_res_4220_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1();
return v_res_4220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkClassAbbrev(lean_object* v_stx_4222_, lean_object* v_a_4223_, lean_object* v_a_4224_){
_start:
{
lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; 
v___x_4226_ = lean_unsigned_to_nat(0u);
v___x_4227_ = l_Lean_Syntax_getArg(v_stx_4222_, v___x_4226_);
v___x_4228_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v___x_4227_, v_a_4223_, v_a_4224_);
lean_dec(v___x_4227_);
if (lean_obj_tag(v___x_4228_) == 0)
{
lean_object* v_a_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4243_; 
v_a_4229_ = lean_ctor_get(v___x_4228_, 0);
v_isSharedCheck_4243_ = !lean_is_exclusive(v___x_4228_);
if (v_isSharedCheck_4243_ == 0)
{
v___x_4231_ = v___x_4228_;
v_isShared_4232_ = v_isSharedCheck_4243_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_a_4229_);
lean_dec(v___x_4228_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4243_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
if (lean_obj_tag(v_a_4229_) == 1)
{
lean_object* v_val_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; uint8_t v___x_4237_; lean_object* v___x_4238_; 
lean_del_object(v___x_4231_);
v_val_4233_ = lean_ctor_get(v_a_4229_, 0);
lean_inc(v_val_4233_);
lean_dec_ref_known(v_a_4229_, 1);
v___x_4234_ = lean_unsigned_to_nat(3u);
v___x_4235_ = l_Lean_Syntax_getArg(v_stx_4222_, v___x_4234_);
v___x_4236_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkClassAbbrev___closed__0));
v___x_4237_ = lean_unbox(v_val_4233_);
lean_dec(v_val_4233_);
v___x_4238_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v___x_4237_, v___x_4235_, v___x_4236_, v_a_4223_, v_a_4224_);
return v___x_4238_;
}
else
{
lean_object* v___x_4239_; lean_object* v___x_4241_; 
lean_dec(v_a_4229_);
v___x_4239_ = lean_box(0);
if (v_isShared_4232_ == 0)
{
lean_ctor_set(v___x_4231_, 0, v___x_4239_);
v___x_4241_ = v___x_4231_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v___x_4239_);
v___x_4241_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
return v___x_4241_;
}
}
}
}
else
{
lean_object* v_a_4244_; lean_object* v___x_4246_; uint8_t v_isShared_4247_; uint8_t v_isSharedCheck_4251_; 
v_a_4244_ = lean_ctor_get(v___x_4228_, 0);
v_isSharedCheck_4251_ = !lean_is_exclusive(v___x_4228_);
if (v_isSharedCheck_4251_ == 0)
{
v___x_4246_ = v___x_4228_;
v_isShared_4247_ = v_isSharedCheck_4251_;
goto v_resetjp_4245_;
}
else
{
lean_inc(v_a_4244_);
lean_dec(v___x_4228_);
v___x_4246_ = lean_box(0);
v_isShared_4247_ = v_isSharedCheck_4251_;
goto v_resetjp_4245_;
}
v_resetjp_4245_:
{
lean_object* v___x_4249_; 
if (v_isShared_4247_ == 0)
{
v___x_4249_ = v___x_4246_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4250_; 
v_reuseFailAlloc_4250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4250_, 0, v_a_4244_);
v___x_4249_ = v_reuseFailAlloc_4250_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
return v___x_4249_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkClassAbbrev___boxed(lean_object* v_stx_4252_, lean_object* v_a_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_){
_start:
{
lean_object* v_res_4256_; 
v_res_4256_ = l_Lean_Linter_MissingDocs_checkClassAbbrev(v_stx_4252_, v_a_4253_, v_a_4254_);
lean_dec(v_a_4254_);
lean_dec_ref(v_a_4253_);
lean_dec(v_stx_4252_);
return v_res_4256_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__2(void){
_start:
{
lean_object* v___x_4263_; lean_object* v___x_4264_; 
v___x_4263_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkClassAbbrev___boxed), 4, 0);
v___x_4264_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4264_, 0, v___x_4263_);
return v___x_4264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1(){
_start:
{
lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; 
v___x_4266_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__1));
v___x_4267_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__2, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__2_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__2);
v___x_4268_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4266_, v___x_4267_);
return v___x_4268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___boxed(lean_object* v_a_4269_){
_start:
{
lean_object* v_res_4270_; 
v_res_4270_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1();
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSimpLike(lean_object* v_a_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_){
_start:
{
lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; 
v___x_4276_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkSimpLike___closed__0));
v___x_4277_ = lean_unsigned_to_nat(2u);
v___x_4278_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_4276_, v___x_4277_, v_a_4272_, v_a_4273_, v_a_4274_);
return v___x_4278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSimpLike___boxed(lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_){
_start:
{
lean_object* v_res_4283_; 
v_res_4283_ = l_Lean_Linter_MissingDocs_checkSimpLike(v_a_4279_, v_a_4280_, v_a_4281_);
lean_dec(v_a_4281_);
lean_dec_ref(v_a_4280_);
lean_dec(v_a_4279_);
return v_res_4283_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__3(void){
_start:
{
lean_object* v___x_4291_; lean_object* v___x_4292_; 
v___x_4291_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkSimpLike___boxed), 4, 0);
v___x_4292_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4292_, 0, v___x_4291_);
return v___x_4292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1(){
_start:
{
lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; 
v___x_4294_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__2));
v___x_4295_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__3, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__3_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__3);
v___x_4296_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4294_, v___x_4295_);
return v___x_4296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___boxed(lean_object* v_a_4297_){
_start:
{
lean_object* v_res_4298_; 
v_res_4298_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1();
return v_res_4298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption(lean_object* v_a_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_){
_start:
{
lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; 
v___x_4304_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption___closed__0));
v___x_4305_ = lean_unsigned_to_nat(3u);
v___x_4306_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_4304_, v___x_4305_, v_a_4300_, v_a_4301_, v_a_4302_);
return v___x_4306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption___boxed(lean_object* v_a_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_){
_start:
{
lean_object* v_res_4311_; 
v_res_4311_ = l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption(v_a_4307_, v_a_4308_, v_a_4309_);
lean_dec(v_a_4309_);
lean_dec_ref(v_a_4308_);
lean_dec(v_a_4307_);
return v_res_4311_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__3(void){
_start:
{
lean_object* v___x_4318_; lean_object* v___x_4319_; 
v___x_4318_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption___boxed), 4, 0);
v___x_4319_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4319_, 0, v___x_4318_);
return v___x_4319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1(){
_start:
{
lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; 
v___x_4321_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__2));
v___x_4322_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__3, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__3_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__3);
v___x_4323_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4321_, v___x_4322_);
return v___x_4323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___boxed(lean_object* v_a_4324_){
_start:
{
lean_object* v_res_4325_; 
v_res_4325_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1();
return v_res_4325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterOption(lean_object* v_stx_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_){
_start:
{
lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; 
v___x_4330_ = lean_unsigned_to_nat(0u);
v___x_4331_ = l_Lean_Syntax_getArg(v_stx_4326_, v___x_4330_);
v___x_4332_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v___x_4331_, v_a_4327_, v_a_4328_);
lean_dec(v___x_4331_);
if (lean_obj_tag(v___x_4332_) == 0)
{
lean_object* v_a_4333_; lean_object* v___x_4335_; uint8_t v_isShared_4336_; uint8_t v_isSharedCheck_4347_; 
v_a_4333_ = lean_ctor_get(v___x_4332_, 0);
v_isSharedCheck_4347_ = !lean_is_exclusive(v___x_4332_);
if (v_isSharedCheck_4347_ == 0)
{
v___x_4335_ = v___x_4332_;
v_isShared_4336_ = v_isSharedCheck_4347_;
goto v_resetjp_4334_;
}
else
{
lean_inc(v_a_4333_);
lean_dec(v___x_4332_);
v___x_4335_ = lean_box(0);
v_isShared_4336_ = v_isSharedCheck_4347_;
goto v_resetjp_4334_;
}
v_resetjp_4334_:
{
if (lean_obj_tag(v_a_4333_) == 1)
{
lean_object* v_val_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; uint8_t v___x_4341_; lean_object* v___x_4342_; 
lean_del_object(v___x_4335_);
v_val_4337_ = lean_ctor_get(v_a_4333_, 0);
lean_inc(v_val_4337_);
lean_dec_ref_known(v_a_4333_, 1);
v___x_4338_ = lean_unsigned_to_nat(2u);
v___x_4339_ = l_Lean_Syntax_getArg(v_stx_4326_, v___x_4338_);
v___x_4340_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption___closed__0));
v___x_4341_ = lean_unbox(v_val_4337_);
lean_dec(v_val_4337_);
v___x_4342_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v___x_4341_, v___x_4339_, v___x_4340_, v_a_4327_, v_a_4328_);
return v___x_4342_;
}
else
{
lean_object* v___x_4343_; lean_object* v___x_4345_; 
lean_dec(v_a_4333_);
v___x_4343_ = lean_box(0);
if (v_isShared_4336_ == 0)
{
lean_ctor_set(v___x_4335_, 0, v___x_4343_);
v___x_4345_ = v___x_4335_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v___x_4343_);
v___x_4345_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
return v___x_4345_;
}
}
}
}
else
{
lean_object* v_a_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4355_; 
v_a_4348_ = lean_ctor_get(v___x_4332_, 0);
v_isSharedCheck_4355_ = !lean_is_exclusive(v___x_4332_);
if (v_isSharedCheck_4355_ == 0)
{
v___x_4350_ = v___x_4332_;
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_a_4348_);
lean_dec(v___x_4332_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4355_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v___x_4353_; 
if (v_isShared_4351_ == 0)
{
v___x_4353_ = v___x_4350_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4354_; 
v_reuseFailAlloc_4354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4354_, 0, v_a_4348_);
v___x_4353_ = v_reuseFailAlloc_4354_;
goto v_reusejp_4352_;
}
v_reusejp_4352_:
{
return v___x_4353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterOption___boxed(lean_object* v_stx_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_){
_start:
{
lean_object* v_res_4360_; 
v_res_4360_ = l_Lean_Linter_MissingDocs_checkRegisterOption(v_stx_4356_, v_a_4357_, v_a_4358_);
lean_dec(v_a_4358_);
lean_dec_ref(v_a_4357_);
lean_dec(v_stx_4356_);
return v_res_4360_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__2(void){
_start:
{
lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4366_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkRegisterOption___boxed), 4, 0);
v___x_4367_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4367_, 0, v___x_4366_);
return v___x_4367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1(){
_start:
{
lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; 
v___x_4369_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__1));
v___x_4370_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__2, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__2_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__2);
v___x_4371_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4369_, v___x_4370_);
return v___x_4371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___boxed(lean_object* v_a_4372_){
_start:
{
lean_object* v_res_4373_; 
v_res_4373_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1();
return v_res_4373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterSimpAttr(lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_){
_start:
{
lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; 
v___x_4379_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkRegisterSimpAttr___closed__0));
v___x_4380_ = lean_unsigned_to_nat(2u);
v___x_4381_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_4379_, v___x_4380_, v_a_4375_, v_a_4376_, v_a_4377_);
return v___x_4381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterSimpAttr___boxed(lean_object* v_a_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_){
_start:
{
lean_object* v_res_4386_; 
v_res_4386_ = l_Lean_Linter_MissingDocs_checkRegisterSimpAttr(v_a_4382_, v_a_4383_, v_a_4384_);
lean_dec(v_a_4384_);
lean_dec_ref(v_a_4383_);
lean_dec(v_a_4382_);
return v_res_4386_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__2(void){
_start:
{
lean_object* v___x_4393_; lean_object* v___x_4394_; 
v___x_4393_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkRegisterSimpAttr___boxed), 4, 0);
v___x_4394_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4394_, 0, v___x_4393_);
return v___x_4394_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1(){
_start:
{
lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; 
v___x_4396_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__1));
v___x_4397_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__2, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__2_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__2);
v___x_4398_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4396_, v___x_4397_);
return v___x_4398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___boxed(lean_object* v_a_4399_){
_start:
{
lean_object* v_res_4400_; 
v_res_4400_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1();
return v_res_4400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2___redArg(lean_object* v_t_4401_, lean_object* v___y_4402_){
_start:
{
lean_object* v___x_4404_; lean_object* v_infoState_4405_; uint8_t v_enabled_4406_; 
v___x_4404_ = lean_st_ref_get(v___y_4402_);
v_infoState_4405_ = lean_ctor_get(v___x_4404_, 8);
lean_inc_ref(v_infoState_4405_);
lean_dec(v___x_4404_);
v_enabled_4406_ = lean_ctor_get_uint8(v_infoState_4405_, sizeof(void*)*3);
lean_dec_ref(v_infoState_4405_);
if (v_enabled_4406_ == 0)
{
lean_object* v___x_4407_; lean_object* v___x_4408_; 
lean_dec_ref(v_t_4401_);
v___x_4407_ = lean_box(0);
v___x_4408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4408_, 0, v___x_4407_);
return v___x_4408_;
}
else
{
lean_object* v___x_4409_; lean_object* v_infoState_4410_; lean_object* v_env_4411_; lean_object* v_messages_4412_; lean_object* v_scopes_4413_; lean_object* v_usedQuotCtxts_4414_; lean_object* v_nextMacroScope_4415_; lean_object* v_maxRecDepth_4416_; lean_object* v_ngen_4417_; lean_object* v_auxDeclNGen_4418_; lean_object* v_traceState_4419_; lean_object* v_snapshotTasks_4420_; lean_object* v_prevLinterStates_4421_; lean_object* v_codeQualityEntryTasks_4422_; lean_object* v___x_4424_; uint8_t v_isShared_4425_; uint8_t v_isSharedCheck_4444_; 
v___x_4409_ = lean_st_ref_take(v___y_4402_);
v_infoState_4410_ = lean_ctor_get(v___x_4409_, 8);
v_env_4411_ = lean_ctor_get(v___x_4409_, 0);
v_messages_4412_ = lean_ctor_get(v___x_4409_, 1);
v_scopes_4413_ = lean_ctor_get(v___x_4409_, 2);
v_usedQuotCtxts_4414_ = lean_ctor_get(v___x_4409_, 3);
v_nextMacroScope_4415_ = lean_ctor_get(v___x_4409_, 4);
v_maxRecDepth_4416_ = lean_ctor_get(v___x_4409_, 5);
v_ngen_4417_ = lean_ctor_get(v___x_4409_, 6);
v_auxDeclNGen_4418_ = lean_ctor_get(v___x_4409_, 7);
v_traceState_4419_ = lean_ctor_get(v___x_4409_, 9);
v_snapshotTasks_4420_ = lean_ctor_get(v___x_4409_, 10);
v_prevLinterStates_4421_ = lean_ctor_get(v___x_4409_, 11);
v_codeQualityEntryTasks_4422_ = lean_ctor_get(v___x_4409_, 12);
v_isSharedCheck_4444_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4424_ = v___x_4409_;
v_isShared_4425_ = v_isSharedCheck_4444_;
goto v_resetjp_4423_;
}
else
{
lean_inc(v_codeQualityEntryTasks_4422_);
lean_inc(v_prevLinterStates_4421_);
lean_inc(v_snapshotTasks_4420_);
lean_inc(v_traceState_4419_);
lean_inc(v_infoState_4410_);
lean_inc(v_auxDeclNGen_4418_);
lean_inc(v_ngen_4417_);
lean_inc(v_maxRecDepth_4416_);
lean_inc(v_nextMacroScope_4415_);
lean_inc(v_usedQuotCtxts_4414_);
lean_inc(v_scopes_4413_);
lean_inc(v_messages_4412_);
lean_inc(v_env_4411_);
lean_dec(v___x_4409_);
v___x_4424_ = lean_box(0);
v_isShared_4425_ = v_isSharedCheck_4444_;
goto v_resetjp_4423_;
}
v_resetjp_4423_:
{
uint8_t v_enabled_4426_; lean_object* v_assignment_4427_; lean_object* v_lazyAssignment_4428_; lean_object* v_trees_4429_; lean_object* v___x_4431_; uint8_t v_isShared_4432_; uint8_t v_isSharedCheck_4443_; 
v_enabled_4426_ = lean_ctor_get_uint8(v_infoState_4410_, sizeof(void*)*3);
v_assignment_4427_ = lean_ctor_get(v_infoState_4410_, 0);
v_lazyAssignment_4428_ = lean_ctor_get(v_infoState_4410_, 1);
v_trees_4429_ = lean_ctor_get(v_infoState_4410_, 2);
v_isSharedCheck_4443_ = !lean_is_exclusive(v_infoState_4410_);
if (v_isSharedCheck_4443_ == 0)
{
v___x_4431_ = v_infoState_4410_;
v_isShared_4432_ = v_isSharedCheck_4443_;
goto v_resetjp_4430_;
}
else
{
lean_inc(v_trees_4429_);
lean_inc(v_lazyAssignment_4428_);
lean_inc(v_assignment_4427_);
lean_dec(v_infoState_4410_);
v___x_4431_ = lean_box(0);
v_isShared_4432_ = v_isSharedCheck_4443_;
goto v_resetjp_4430_;
}
v_resetjp_4430_:
{
lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4436_; 
v___x_4433_ = lean_box(0);
v___x_4434_ = l_Lean_PersistentArray_push___redArg(v_trees_4429_, v_t_4401_);
if (v_isShared_4432_ == 0)
{
lean_ctor_set(v___x_4431_, 2, v___x_4434_);
v___x_4436_ = v___x_4431_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v_assignment_4427_);
lean_ctor_set(v_reuseFailAlloc_4442_, 1, v_lazyAssignment_4428_);
lean_ctor_set(v_reuseFailAlloc_4442_, 2, v___x_4434_);
lean_ctor_set_uint8(v_reuseFailAlloc_4442_, sizeof(void*)*3, v_enabled_4426_);
v___x_4436_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
lean_object* v___x_4438_; 
if (v_isShared_4425_ == 0)
{
lean_ctor_set(v___x_4424_, 8, v___x_4436_);
v___x_4438_ = v___x_4424_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v_env_4411_);
lean_ctor_set(v_reuseFailAlloc_4441_, 1, v_messages_4412_);
lean_ctor_set(v_reuseFailAlloc_4441_, 2, v_scopes_4413_);
lean_ctor_set(v_reuseFailAlloc_4441_, 3, v_usedQuotCtxts_4414_);
lean_ctor_set(v_reuseFailAlloc_4441_, 4, v_nextMacroScope_4415_);
lean_ctor_set(v_reuseFailAlloc_4441_, 5, v_maxRecDepth_4416_);
lean_ctor_set(v_reuseFailAlloc_4441_, 6, v_ngen_4417_);
lean_ctor_set(v_reuseFailAlloc_4441_, 7, v_auxDeclNGen_4418_);
lean_ctor_set(v_reuseFailAlloc_4441_, 8, v___x_4436_);
lean_ctor_set(v_reuseFailAlloc_4441_, 9, v_traceState_4419_);
lean_ctor_set(v_reuseFailAlloc_4441_, 10, v_snapshotTasks_4420_);
lean_ctor_set(v_reuseFailAlloc_4441_, 11, v_prevLinterStates_4421_);
lean_ctor_set(v_reuseFailAlloc_4441_, 12, v_codeQualityEntryTasks_4422_);
v___x_4438_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
lean_object* v___x_4439_; lean_object* v___x_4440_; 
v___x_4439_ = lean_st_ref_put(v___y_4402_, v___x_4438_);
v___x_4440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4440_, 0, v___x_4433_);
return v___x_4440_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_t_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_){
_start:
{
lean_object* v_res_4448_; 
v_res_4448_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2___redArg(v_t_4445_, v___y_4446_);
lean_dec(v___y_4446_);
return v_res_4448_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; 
v___x_4449_ = lean_unsigned_to_nat(32u);
v___x_4450_ = lean_mk_empty_array_with_capacity(v___x_4449_);
v___x_4451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4451_, 0, v___x_4450_);
return v___x_4451_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__1(void){
_start:
{
size_t v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; 
v___x_4452_ = ((size_t)5ULL);
v___x_4453_ = lean_unsigned_to_nat(0u);
v___x_4454_ = lean_unsigned_to_nat(32u);
v___x_4455_ = lean_mk_empty_array_with_capacity(v___x_4454_);
v___x_4456_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__0);
v___x_4457_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4457_, 0, v___x_4456_);
lean_ctor_set(v___x_4457_, 1, v___x_4455_);
lean_ctor_set(v___x_4457_, 2, v___x_4453_);
lean_ctor_set(v___x_4457_, 3, v___x_4453_);
lean_ctor_set_usize(v___x_4457_, 4, v___x_4452_);
return v___x_4457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1(lean_object* v_t_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_){
_start:
{
lean_object* v___x_4462_; lean_object* v_infoState_4463_; uint8_t v_enabled_4464_; 
v___x_4462_ = lean_st_ref_get(v___y_4460_);
v_infoState_4463_ = lean_ctor_get(v___x_4462_, 8);
lean_inc_ref(v_infoState_4463_);
lean_dec(v___x_4462_);
v_enabled_4464_ = lean_ctor_get_uint8(v_infoState_4463_, sizeof(void*)*3);
lean_dec_ref(v_infoState_4463_);
if (v_enabled_4464_ == 0)
{
lean_object* v___x_4465_; lean_object* v___x_4466_; 
lean_dec_ref(v_t_4458_);
v___x_4465_ = lean_box(0);
v___x_4466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4466_, 0, v___x_4465_);
return v___x_4466_;
}
else
{
lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; 
v___x_4467_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__1);
v___x_4468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4468_, 0, v_t_4458_);
lean_ctor_set(v___x_4468_, 1, v___x_4467_);
v___x_4469_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2___redArg(v___x_4468_, v___y_4460_);
return v___x_4469_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___boxed(lean_object* v_t_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_){
_start:
{
lean_object* v_res_4474_; 
v_res_4474_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1(v_t_4470_, v___y_4471_, v___y_4472_);
lean_dec(v___y_4472_);
lean_dec_ref(v___y_4471_);
return v_res_4474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__0(lean_object* v_info_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_){
_start:
{
lean_object* v___x_4479_; lean_object* v___x_4480_; 
v___x_4479_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_4479_, 0, v_info_4475_);
v___x_4480_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1(v___x_4479_, v___y_4476_, v___y_4477_);
return v___x_4480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__0___boxed(lean_object* v_info_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_){
_start:
{
lean_object* v_res_4485_; 
v_res_4485_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__0(v_info_4481_, v___y_4482_, v___y_4483_);
lean_dec(v___y_4483_);
lean_dec_ref(v___y_4482_);
return v_res_4485_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4487_; lean_object* v___x_4488_; 
v___x_4487_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__0));
v___x_4488_ = l_Lean_stringToMessageData(v___x_4487_);
return v___x_4488_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4490_; lean_object* v___x_4491_; 
v___x_4490_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__2));
v___x_4491_ = l_Lean_stringToMessageData(v___x_4490_);
return v___x_4491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg(lean_object* v_optionName_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_){
_start:
{
lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; 
v___x_4496_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__1, &l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__1_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__1);
v___x_4497_ = l_Lean_MessageData_ofName(v_optionName_4492_);
v___x_4498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4498_, 0, v___x_4496_);
lean_ctor_set(v___x_4498_, 1, v___x_4497_);
v___x_4499_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__3, &l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__3_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__3);
v___x_4500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4500_, 0, v___x_4498_);
lean_ctor_set(v___x_4500_, 1, v___x_4499_);
v___x_4501_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg(v___x_4500_, v___y_4493_, v___y_4494_);
return v___x_4501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___boxed(lean_object* v_optionName_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_){
_start:
{
lean_object* v_res_4506_; 
v_res_4506_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg(v_optionName_4502_, v___y_4503_, v___y_4504_);
lean_dec(v___y_4504_);
lean_dec_ref(v___y_4503_);
return v_res_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__6(lean_object* v_o_4507_, lean_object* v_k_4508_, lean_object* v_v_4509_){
_start:
{
lean_object* v_map_4510_; uint8_t v_hasTrace_4511_; lean_object* v___x_4513_; uint8_t v_isShared_4514_; uint8_t v_isSharedCheck_4524_; 
v_map_4510_ = lean_ctor_get(v_o_4507_, 0);
v_hasTrace_4511_ = lean_ctor_get_uint8(v_o_4507_, sizeof(void*)*1);
v_isSharedCheck_4524_ = !lean_is_exclusive(v_o_4507_);
if (v_isSharedCheck_4524_ == 0)
{
v___x_4513_ = v_o_4507_;
v_isShared_4514_ = v_isSharedCheck_4524_;
goto v_resetjp_4512_;
}
else
{
lean_inc(v_map_4510_);
lean_dec(v_o_4507_);
v___x_4513_ = lean_box(0);
v_isShared_4514_ = v_isSharedCheck_4524_;
goto v_resetjp_4512_;
}
v_resetjp_4512_:
{
lean_object* v___x_4515_; 
lean_inc(v_k_4508_);
v___x_4515_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4508_, v_v_4509_, v_map_4510_);
if (v_hasTrace_4511_ == 0)
{
lean_object* v___x_4516_; uint8_t v___x_4517_; lean_object* v___x_4519_; 
v___x_4516_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__9));
v___x_4517_ = l_Lean_Name_isPrefixOf(v___x_4516_, v_k_4508_);
lean_dec(v_k_4508_);
if (v_isShared_4514_ == 0)
{
lean_ctor_set(v___x_4513_, 0, v___x_4515_);
v___x_4519_ = v___x_4513_;
goto v_reusejp_4518_;
}
else
{
lean_object* v_reuseFailAlloc_4520_; 
v_reuseFailAlloc_4520_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4520_, 0, v___x_4515_);
v___x_4519_ = v_reuseFailAlloc_4520_;
goto v_reusejp_4518_;
}
v_reusejp_4518_:
{
lean_ctor_set_uint8(v___x_4519_, sizeof(void*)*1, v___x_4517_);
return v___x_4519_;
}
}
else
{
lean_object* v___x_4522_; 
lean_dec(v_k_4508_);
if (v_isShared_4514_ == 0)
{
lean_ctor_set(v___x_4513_, 0, v___x_4515_);
v___x_4522_ = v___x_4513_;
goto v_reusejp_4521_;
}
else
{
lean_object* v_reuseFailAlloc_4523_; 
v_reuseFailAlloc_4523_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4523_, 0, v___x_4515_);
lean_ctor_set_uint8(v_reuseFailAlloc_4523_, sizeof(void*)*1, v_hasTrace_4511_);
v___x_4522_ = v_reuseFailAlloc_4523_;
goto v_reusejp_4521_;
}
v_reusejp_4521_:
{
return v___x_4522_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8_spec__10(lean_object* v_msg_4525_){
_start:
{
lean_object* v___x_4526_; lean_object* v___x_4527_; 
v___x_4526_ = l_Lean_instInhabitedExpr;
v___x_4527_ = lean_panic_fn_borrowed(v___x_4526_, v_msg_4525_);
return v___x_4527_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__1(void){
_start:
{
lean_object* v___x_4529_; lean_object* v___x_4530_; 
v___x_4529_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__0));
v___x_4530_ = l_Lean_stringToMessageData(v___x_4529_);
return v___x_4530_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__3(void){
_start:
{
lean_object* v___x_4532_; lean_object* v___x_4533_; 
v___x_4532_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__2));
v___x_4533_ = l_Lean_stringToMessageData(v___x_4532_);
return v___x_4533_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__5(void){
_start:
{
lean_object* v___x_4535_; lean_object* v___x_4536_; 
v___x_4535_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__4));
v___x_4536_ = l_Lean_stringToMessageData(v___x_4535_);
return v___x_4536_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__7(void){
_start:
{
lean_object* v___x_4538_; lean_object* v___x_4539_; 
v___x_4538_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__6));
v___x_4539_ = l_Lean_stringToMessageData(v___x_4538_);
return v___x_4539_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__16(void){
_start:
{
lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; 
v___x_4551_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__15));
v___x_4552_ = lean_unsigned_to_nat(14u);
v___x_4553_ = lean_unsigned_to_nat(22u);
v___x_4554_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__14));
v___x_4555_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__13));
v___x_4556_ = l_mkPanicMessageWithDecl(v___x_4555_, v___x_4554_, v___x_4553_, v___x_4552_, v___x_4551_);
return v___x_4556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8(lean_object* v_optionName_4557_, lean_object* v_found_4558_, lean_object* v_defVal_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_){
_start:
{
lean_object* v___x_4563_; 
v___x_4563_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_defVal_4559_);
if (lean_obj_tag(v___x_4563_) == 1)
{
lean_object* v_val_4564_; lean_object* v___y_4566_; lean_object* v___y_4567_; lean_object* v___y_4568_; lean_object* v___y_4587_; lean_object* v___x_4635_; 
v_val_4564_ = lean_ctor_get(v___x_4563_, 0);
lean_inc(v_val_4564_);
lean_dec_ref_known(v___x_4563_, 1);
v___x_4635_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_found_4558_);
if (lean_obj_tag(v___x_4635_) == 0)
{
lean_object* v___x_4636_; lean_object* v___x_4637_; 
v___x_4636_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__16, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__16_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__16);
v___x_4637_ = l_panic___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8_spec__10(v___x_4636_);
v___y_4587_ = v___x_4637_;
goto v___jp_4586_;
}
else
{
lean_object* v_val_4638_; 
v_val_4638_ = lean_ctor_get(v___x_4635_, 0);
lean_inc(v_val_4638_);
lean_dec_ref_known(v___x_4635_, 1);
v___y_4587_ = v_val_4638_;
goto v___jp_4586_;
}
v___jp_4565_:
{
lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; 
v___x_4569_ = l_Lean_MessageData_ofFormat(v___y_4568_);
v___x_4570_ = l_Lean_indentD(v___x_4569_);
lean_inc_ref(v___y_4566_);
v___x_4571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4571_, 0, v___y_4566_);
lean_ctor_set(v___x_4571_, 1, v___x_4570_);
v___x_4572_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__1, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__1_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__1);
v___x_4573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4573_, 0, v___x_4571_);
lean_ctor_set(v___x_4573_, 1, v___x_4572_);
v___x_4574_ = l_Lean_MessageData_ofExpr(v___y_4567_);
v___x_4575_ = l_Lean_indentD(v___x_4574_);
v___x_4576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4576_, 0, v___x_4573_);
lean_ctor_set(v___x_4576_, 1, v___x_4575_);
v___x_4577_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__3, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__3_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__3);
v___x_4578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4578_, 0, v___x_4576_);
lean_ctor_set(v___x_4578_, 1, v___x_4577_);
v___x_4579_ = l_Lean_MessageData_ofName(v_optionName_4557_);
v___x_4580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4580_, 0, v___x_4578_);
lean_ctor_set(v___x_4580_, 1, v___x_4579_);
v___x_4581_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__5, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__5_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__5);
v___x_4582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4582_, 0, v___x_4580_);
lean_ctor_set(v___x_4582_, 1, v___x_4581_);
v___x_4583_ = l_Lean_indentExpr(v_val_4564_);
v___x_4584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4584_, 0, v___x_4582_);
lean_ctor_set(v___x_4584_, 1, v___x_4583_);
v___x_4585_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg(v___x_4584_, v___y_4560_, v___y_4561_);
return v___x_4585_;
}
v___jp_4586_:
{
lean_object* v___x_4588_; 
v___x_4588_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__7, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__7_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__7);
switch(lean_obj_tag(v_found_4558_))
{
case 0:
{
lean_object* v_v_4589_; lean_object* v___x_4591_; uint8_t v_isShared_4592_; uint8_t v_isSharedCheck_4597_; 
v_v_4589_ = lean_ctor_get(v_found_4558_, 0);
v_isSharedCheck_4597_ = !lean_is_exclusive(v_found_4558_);
if (v_isSharedCheck_4597_ == 0)
{
v___x_4591_ = v_found_4558_;
v_isShared_4592_ = v_isSharedCheck_4597_;
goto v_resetjp_4590_;
}
else
{
lean_inc(v_v_4589_);
lean_dec(v_found_4558_);
v___x_4591_ = lean_box(0);
v_isShared_4592_ = v_isSharedCheck_4597_;
goto v_resetjp_4590_;
}
v_resetjp_4590_:
{
lean_object* v___x_4593_; lean_object* v___x_4595_; 
v___x_4593_ = l_String_quote(v_v_4589_);
if (v_isShared_4592_ == 0)
{
lean_ctor_set_tag(v___x_4591_, 3);
lean_ctor_set(v___x_4591_, 0, v___x_4593_);
v___x_4595_ = v___x_4591_;
goto v_reusejp_4594_;
}
else
{
lean_object* v_reuseFailAlloc_4596_; 
v_reuseFailAlloc_4596_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4596_, 0, v___x_4593_);
v___x_4595_ = v_reuseFailAlloc_4596_;
goto v_reusejp_4594_;
}
v_reusejp_4594_:
{
v___y_4566_ = v___x_4588_;
v___y_4567_ = v___y_4587_;
v___y_4568_ = v___x_4595_;
goto v___jp_4565_;
}
}
}
case 1:
{
uint8_t v_v_4598_; 
v_v_4598_ = lean_ctor_get_uint8(v_found_4558_, 0);
lean_dec_ref_known(v_found_4558_, 0);
if (v_v_4598_ == 0)
{
lean_object* v___x_4599_; 
v___x_4599_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__9));
v___y_4566_ = v___x_4588_;
v___y_4567_ = v___y_4587_;
v___y_4568_ = v___x_4599_;
goto v___jp_4565_;
}
else
{
lean_object* v___x_4600_; 
v___x_4600_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__11));
v___y_4566_ = v___x_4588_;
v___y_4567_ = v___y_4587_;
v___y_4568_ = v___x_4600_;
goto v___jp_4565_;
}
}
case 2:
{
lean_object* v_v_4601_; lean_object* v___x_4603_; uint8_t v_isShared_4604_; uint8_t v_isSharedCheck_4612_; 
v_v_4601_ = lean_ctor_get(v_found_4558_, 0);
v_isSharedCheck_4612_ = !lean_is_exclusive(v_found_4558_);
if (v_isSharedCheck_4612_ == 0)
{
v___x_4603_ = v_found_4558_;
v_isShared_4604_ = v_isSharedCheck_4612_;
goto v_resetjp_4602_;
}
else
{
lean_inc(v_v_4601_);
lean_dec(v_found_4558_);
v___x_4603_ = lean_box(0);
v_isShared_4604_ = v_isSharedCheck_4612_;
goto v_resetjp_4602_;
}
v_resetjp_4602_:
{
lean_object* v___x_4605_; uint8_t v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4609_; 
v___x_4605_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__12));
v___x_4606_ = 1;
v___x_4607_ = l_Lean_Name_toString(v_v_4601_, v___x_4606_);
if (v_isShared_4604_ == 0)
{
lean_ctor_set_tag(v___x_4603_, 3);
lean_ctor_set(v___x_4603_, 0, v___x_4607_);
v___x_4609_ = v___x_4603_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4611_; 
v_reuseFailAlloc_4611_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4611_, 0, v___x_4607_);
v___x_4609_ = v_reuseFailAlloc_4611_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
lean_object* v___x_4610_; 
v___x_4610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4610_, 0, v___x_4605_);
lean_ctor_set(v___x_4610_, 1, v___x_4609_);
v___y_4566_ = v___x_4588_;
v___y_4567_ = v___y_4587_;
v___y_4568_ = v___x_4610_;
goto v___jp_4565_;
}
}
}
case 3:
{
lean_object* v_v_4613_; lean_object* v___x_4615_; uint8_t v_isShared_4616_; uint8_t v_isSharedCheck_4621_; 
v_v_4613_ = lean_ctor_get(v_found_4558_, 0);
v_isSharedCheck_4621_ = !lean_is_exclusive(v_found_4558_);
if (v_isSharedCheck_4621_ == 0)
{
v___x_4615_ = v_found_4558_;
v_isShared_4616_ = v_isSharedCheck_4621_;
goto v_resetjp_4614_;
}
else
{
lean_inc(v_v_4613_);
lean_dec(v_found_4558_);
v___x_4615_ = lean_box(0);
v_isShared_4616_ = v_isSharedCheck_4621_;
goto v_resetjp_4614_;
}
v_resetjp_4614_:
{
lean_object* v___x_4617_; lean_object* v___x_4619_; 
v___x_4617_ = l_Nat_reprFast(v_v_4613_);
if (v_isShared_4616_ == 0)
{
lean_ctor_set(v___x_4615_, 0, v___x_4617_);
v___x_4619_ = v___x_4615_;
goto v_reusejp_4618_;
}
else
{
lean_object* v_reuseFailAlloc_4620_; 
v_reuseFailAlloc_4620_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4620_, 0, v___x_4617_);
v___x_4619_ = v_reuseFailAlloc_4620_;
goto v_reusejp_4618_;
}
v_reusejp_4618_:
{
v___y_4566_ = v___x_4588_;
v___y_4567_ = v___y_4587_;
v___y_4568_ = v___x_4619_;
goto v___jp_4565_;
}
}
}
case 4:
{
lean_object* v_v_4622_; lean_object* v___x_4624_; uint8_t v_isShared_4625_; uint8_t v_isSharedCheck_4630_; 
v_v_4622_ = lean_ctor_get(v_found_4558_, 0);
v_isSharedCheck_4630_ = !lean_is_exclusive(v_found_4558_);
if (v_isSharedCheck_4630_ == 0)
{
v___x_4624_ = v_found_4558_;
v_isShared_4625_ = v_isSharedCheck_4630_;
goto v_resetjp_4623_;
}
else
{
lean_inc(v_v_4622_);
lean_dec(v_found_4558_);
v___x_4624_ = lean_box(0);
v_isShared_4625_ = v_isSharedCheck_4630_;
goto v_resetjp_4623_;
}
v_resetjp_4623_:
{
lean_object* v___x_4626_; lean_object* v___x_4628_; 
v___x_4626_ = l_Int_repr(v_v_4622_);
lean_dec(v_v_4622_);
if (v_isShared_4625_ == 0)
{
lean_ctor_set_tag(v___x_4624_, 3);
lean_ctor_set(v___x_4624_, 0, v___x_4626_);
v___x_4628_ = v___x_4624_;
goto v_reusejp_4627_;
}
else
{
lean_object* v_reuseFailAlloc_4629_; 
v_reuseFailAlloc_4629_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4629_, 0, v___x_4626_);
v___x_4628_ = v_reuseFailAlloc_4629_;
goto v_reusejp_4627_;
}
v_reusejp_4627_:
{
v___y_4566_ = v___x_4588_;
v___y_4567_ = v___y_4587_;
v___y_4568_ = v___x_4628_;
goto v___jp_4565_;
}
}
}
default: 
{
lean_object* v_v_4631_; lean_object* v___x_4632_; uint8_t v___x_4633_; lean_object* v___x_4634_; 
v_v_4631_ = lean_ctor_get(v_found_4558_, 0);
lean_inc(v_v_4631_);
lean_dec_ref_known(v_found_4558_, 1);
v___x_4632_ = lean_box(0);
v___x_4633_ = 0;
v___x_4634_ = l_Lean_Syntax_formatStx(v_v_4631_, v___x_4632_, v___x_4633_);
v___y_4566_ = v___x_4588_;
v___y_4567_ = v___y_4587_;
v___y_4568_ = v___x_4634_;
goto v___jp_4565_;
}
}
}
}
else
{
lean_object* v___x_4639_; 
lean_dec(v___x_4563_);
lean_dec_ref(v_found_4558_);
v___x_4639_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg(v_optionName_4557_, v___y_4560_, v___y_4561_);
return v___x_4639_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___boxed(lean_object* v_optionName_4640_, lean_object* v_found_4641_, lean_object* v_defVal_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_){
_start:
{
lean_object* v_res_4646_; 
v_res_4646_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8(v_optionName_4640_, v_found_4641_, v_defVal_4642_, v___y_4643_, v___y_4644_);
lean_dec(v___y_4644_);
lean_dec_ref(v___y_4643_);
lean_dec_ref(v_defVal_4642_);
return v_res_4646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5(lean_object* v_optionName_4647_, lean_object* v_decl_4648_, lean_object* v_val_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_){
_start:
{
lean_object* v_defValue_4653_; uint8_t v___x_4654_; 
v_defValue_4653_ = lean_ctor_get(v_decl_4648_, 2);
v___x_4654_ = l_Lean_DataValue_sameCtor(v_defValue_4653_, v_val_4649_);
if (v___x_4654_ == 0)
{
lean_object* v___x_4655_; 
v___x_4655_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8(v_optionName_4647_, v_val_4649_, v_defValue_4653_, v___y_4650_, v___y_4651_);
return v___x_4655_;
}
else
{
lean_object* v___x_4656_; lean_object* v___x_4657_; 
lean_dec_ref(v_val_4649_);
lean_dec(v_optionName_4647_);
v___x_4656_ = lean_box(0);
v___x_4657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4657_, 0, v___x_4656_);
return v___x_4657_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5___boxed(lean_object* v_optionName_4658_, lean_object* v_decl_4659_, lean_object* v_val_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_){
_start:
{
lean_object* v_res_4664_; 
v_res_4664_ = l_Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5(v_optionName_4658_, v_decl_4659_, v_val_4660_, v___y_4661_, v___y_4662_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
lean_dec_ref(v_decl_4659_);
return v_res_4664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3(lean_object* v_optionName_4665_, lean_object* v_decl_4666_, lean_object* v_val_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_){
_start:
{
lean_object* v___x_4671_; 
lean_inc_ref(v_val_4667_);
lean_inc(v_optionName_4665_);
v___x_4671_ = l_Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5(v_optionName_4665_, v_decl_4666_, v_val_4667_, v___y_4668_, v___y_4669_);
if (lean_obj_tag(v___x_4671_) == 0)
{
lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4685_; 
v_isSharedCheck_4685_ = !lean_is_exclusive(v___x_4671_);
if (v_isSharedCheck_4685_ == 0)
{
lean_object* v_unused_4686_; 
v_unused_4686_ = lean_ctor_get(v___x_4671_, 0);
lean_dec(v_unused_4686_);
v___x_4673_ = v___x_4671_;
v_isShared_4674_ = v_isSharedCheck_4685_;
goto v_resetjp_4672_;
}
else
{
lean_dec(v___x_4671_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4685_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v_scopes_4677_; lean_object* v___x_4678_; lean_object* v_opts_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4683_; 
v___x_4675_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4676_ = lean_st_ref_get(v___y_4669_);
v_scopes_4677_ = lean_ctor_get(v___x_4676_, 2);
lean_inc(v_scopes_4677_);
lean_dec(v___x_4676_);
v___x_4678_ = l_List_head_x21___redArg(v___x_4675_, v_scopes_4677_);
lean_dec(v_scopes_4677_);
v_opts_4679_ = lean_ctor_get(v___x_4678_, 1);
lean_inc_ref(v_opts_4679_);
lean_dec(v___x_4678_);
v___x_4680_ = l_Lean_Options_set___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__6(v_opts_4679_, v_optionName_4665_, v_val_4667_);
v___x_4681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4681_, 0, v___x_4680_);
lean_ctor_set(v___x_4681_, 1, v_decl_4666_);
if (v_isShared_4674_ == 0)
{
lean_ctor_set(v___x_4673_, 0, v___x_4681_);
v___x_4683_ = v___x_4673_;
goto v_reusejp_4682_;
}
else
{
lean_object* v_reuseFailAlloc_4684_; 
v_reuseFailAlloc_4684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4684_, 0, v___x_4681_);
v___x_4683_ = v_reuseFailAlloc_4684_;
goto v_reusejp_4682_;
}
v_reusejp_4682_:
{
return v___x_4683_;
}
}
}
else
{
lean_object* v_a_4687_; lean_object* v___x_4689_; uint8_t v_isShared_4690_; uint8_t v_isSharedCheck_4694_; 
lean_dec_ref(v_val_4667_);
lean_dec_ref(v_decl_4666_);
lean_dec(v_optionName_4665_);
v_a_4687_ = lean_ctor_get(v___x_4671_, 0);
v_isSharedCheck_4694_ = !lean_is_exclusive(v___x_4671_);
if (v_isSharedCheck_4694_ == 0)
{
v___x_4689_ = v___x_4671_;
v_isShared_4690_ = v_isSharedCheck_4694_;
goto v_resetjp_4688_;
}
else
{
lean_inc(v_a_4687_);
lean_dec(v___x_4671_);
v___x_4689_ = lean_box(0);
v_isShared_4690_ = v_isSharedCheck_4694_;
goto v_resetjp_4688_;
}
v_resetjp_4688_:
{
lean_object* v___x_4692_; 
if (v_isShared_4690_ == 0)
{
v___x_4692_ = v___x_4689_;
goto v_reusejp_4691_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v_a_4687_);
v___x_4692_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4691_;
}
v_reusejp_4691_:
{
return v___x_4692_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3___boxed(lean_object* v_optionName_4695_, lean_object* v_decl_4696_, lean_object* v_val_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_){
_start:
{
lean_object* v_res_4701_; 
v_res_4701_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3(v_optionName_4695_, v_decl_4696_, v_val_4697_, v___y_4698_, v___y_4699_);
lean_dec(v___y_4699_);
lean_dec_ref(v___y_4698_);
return v_res_4701_;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4703_; lean_object* v___x_4704_; 
v___x_4703_ = ((lean_object*)(l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__0));
v___x_4704_ = l_Lean_stringToMessageData(v___x_4703_);
return v___x_4704_;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4706_; lean_object* v___x_4707_; 
v___x_4706_ = ((lean_object*)(l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__2));
v___x_4707_ = l_Lean_stringToMessageData(v___x_4706_);
return v___x_4707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0(lean_object* v_id_4708_, lean_object* v_val_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_){
_start:
{
lean_object* v___x_4713_; 
v___x_4713_ = l_Lean_Elab_Command_getRef___redArg(v___y_4710_);
if (lean_obj_tag(v___x_4713_) == 0)
{
lean_object* v_a_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4724_; uint8_t v_isShared_4725_; uint8_t v_isSharedCheck_4794_; 
v_a_4714_ = lean_ctor_get(v___x_4713_, 0);
lean_inc_n(v_a_4714_, 2);
lean_dec_ref_known(v___x_4713_, 1);
v___x_4715_ = l_Lean_Syntax_getArgs(v_a_4714_);
v___x_4716_ = lean_unsigned_to_nat(3u);
v___x_4717_ = lean_unsigned_to_nat(0u);
v___x_4718_ = l_Array_toSubarray___redArg(v___x_4715_, v___x_4717_, v___x_4716_);
v___x_4719_ = l_Subarray_copy___redArg(v___x_4718_);
v___x_4720_ = l_Lean_Syntax_setArgs(v_a_4714_, v___x_4719_);
v___x_4721_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_4721_, 0, v___x_4720_);
v___x_4722_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__0(v___x_4721_, v___y_4710_, v___y_4711_);
v_isSharedCheck_4794_ = !lean_is_exclusive(v___x_4722_);
if (v_isSharedCheck_4794_ == 0)
{
lean_object* v_unused_4795_; 
v_unused_4795_ = lean_ctor_get(v___x_4722_, 0);
lean_dec(v_unused_4795_);
v___x_4724_ = v___x_4722_;
v_isShared_4725_ = v_isSharedCheck_4794_;
goto v_resetjp_4723_;
}
else
{
lean_dec(v___x_4722_);
v___x_4724_ = lean_box(0);
v_isShared_4725_ = v_isSharedCheck_4794_;
goto v_resetjp_4723_;
}
v_resetjp_4723_:
{
lean_object* v___x_4726_; lean_object* v_optionName_4727_; lean_object* v___x_4728_; 
v___x_4726_ = l_Lean_Syntax_getId(v_id_4708_);
v_optionName_4727_ = l_Lean_Name_eraseMacroScopes(v___x_4726_);
lean_dec(v___x_4726_);
lean_inc(v_optionName_4727_);
v___x_4728_ = l_Lean_getOptionDecl(v_optionName_4727_);
if (lean_obj_tag(v___x_4728_) == 0)
{
lean_object* v_a_4729_; lean_object* v_declName_4730_; lean_object* v_defValue_4731_; lean_object* v___x_4732_; lean_object* v___x_4734_; 
lean_dec(v_a_4714_);
v_a_4729_ = lean_ctor_get(v___x_4728_, 0);
lean_inc(v_a_4729_);
lean_dec_ref_known(v___x_4728_, 1);
v_declName_4730_ = lean_ctor_get(v_a_4729_, 1);
v_defValue_4731_ = lean_ctor_get(v_a_4729_, 2);
lean_inc(v_declName_4730_);
lean_inc(v_optionName_4727_);
v___x_4732_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4732_, 0, v_id_4708_);
lean_ctor_set(v___x_4732_, 1, v_optionName_4727_);
lean_ctor_set(v___x_4732_, 2, v_declName_4730_);
if (v_isShared_4725_ == 0)
{
lean_ctor_set_tag(v___x_4724_, 5);
lean_ctor_set(v___x_4724_, 0, v___x_4732_);
v___x_4734_ = v___x_4724_;
goto v_reusejp_4733_;
}
else
{
lean_object* v_reuseFailAlloc_4779_; 
v_reuseFailAlloc_4779_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4779_, 0, v___x_4732_);
v___x_4734_ = v_reuseFailAlloc_4779_;
goto v_reusejp_4733_;
}
v_reusejp_4733_:
{
lean_object* v___x_4735_; lean_object* v___x_4750_; 
v___x_4735_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1(v___x_4734_, v___y_4710_, v___y_4711_);
lean_dec_ref(v___x_4735_);
v___x_4750_ = l_Lean_Syntax_isStrLit_x3f(v_val_4709_);
if (lean_obj_tag(v___x_4750_) == 0)
{
lean_object* v___x_4751_; 
v___x_4751_ = l_Lean_Syntax_isNatLit_x3f(v_val_4709_);
if (lean_obj_tag(v___x_4751_) == 0)
{
if (lean_obj_tag(v_val_4709_) == 2)
{
lean_object* v_val_4752_; lean_object* v___x_4753_; uint8_t v___x_4754_; 
v_val_4752_ = lean_ctor_get(v_val_4709_, 1);
v___x_4753_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__10));
v___x_4754_ = lean_string_dec_eq(v_val_4752_, v___x_4753_);
if (v___x_4754_ == 0)
{
lean_object* v___x_4755_; uint8_t v___x_4756_; 
v___x_4755_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__8));
v___x_4756_ = lean_string_dec_eq(v_val_4752_, v___x_4755_);
if (v___x_4756_ == 0)
{
lean_inc_ref(v_defValue_4731_);
lean_dec(v_a_4729_);
goto v___jp_4736_;
}
else
{
lean_object* v___x_4757_; lean_object* v___x_4758_; 
lean_dec_ref_known(v_val_4709_, 2);
v___x_4757_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4757_, 0, v___x_4754_);
v___x_4758_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3(v_optionName_4727_, v_a_4729_, v___x_4757_, v___y_4710_, v___y_4711_);
return v___x_4758_;
}
}
else
{
lean_object* v___x_4759_; lean_object* v___x_4760_; 
lean_dec_ref_known(v_val_4709_, 2);
v___x_4759_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4759_, 0, v___x_4754_);
v___x_4760_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3(v_optionName_4727_, v_a_4729_, v___x_4759_, v___y_4710_, v___y_4711_);
return v___x_4760_;
}
}
else
{
lean_inc_ref(v_defValue_4731_);
lean_dec(v_a_4729_);
goto v___jp_4736_;
}
}
else
{
lean_object* v_val_4761_; lean_object* v___x_4763_; uint8_t v_isShared_4764_; uint8_t v_isSharedCheck_4769_; 
lean_dec(v_val_4709_);
v_val_4761_ = lean_ctor_get(v___x_4751_, 0);
v_isSharedCheck_4769_ = !lean_is_exclusive(v___x_4751_);
if (v_isSharedCheck_4769_ == 0)
{
v___x_4763_ = v___x_4751_;
v_isShared_4764_ = v_isSharedCheck_4769_;
goto v_resetjp_4762_;
}
else
{
lean_inc(v_val_4761_);
lean_dec(v___x_4751_);
v___x_4763_ = lean_box(0);
v_isShared_4764_ = v_isSharedCheck_4769_;
goto v_resetjp_4762_;
}
v_resetjp_4762_:
{
lean_object* v___x_4766_; 
if (v_isShared_4764_ == 0)
{
lean_ctor_set_tag(v___x_4763_, 3);
v___x_4766_ = v___x_4763_;
goto v_reusejp_4765_;
}
else
{
lean_object* v_reuseFailAlloc_4768_; 
v_reuseFailAlloc_4768_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4768_, 0, v_val_4761_);
v___x_4766_ = v_reuseFailAlloc_4768_;
goto v_reusejp_4765_;
}
v_reusejp_4765_:
{
lean_object* v___x_4767_; 
v___x_4767_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3(v_optionName_4727_, v_a_4729_, v___x_4766_, v___y_4710_, v___y_4711_);
return v___x_4767_;
}
}
}
}
else
{
lean_object* v_val_4770_; lean_object* v___x_4772_; uint8_t v_isShared_4773_; uint8_t v_isSharedCheck_4778_; 
lean_dec(v_val_4709_);
v_val_4770_ = lean_ctor_get(v___x_4750_, 0);
v_isSharedCheck_4778_ = !lean_is_exclusive(v___x_4750_);
if (v_isSharedCheck_4778_ == 0)
{
v___x_4772_ = v___x_4750_;
v_isShared_4773_ = v_isSharedCheck_4778_;
goto v_resetjp_4771_;
}
else
{
lean_inc(v_val_4770_);
lean_dec(v___x_4750_);
v___x_4772_ = lean_box(0);
v_isShared_4773_ = v_isSharedCheck_4778_;
goto v_resetjp_4771_;
}
v_resetjp_4771_:
{
lean_object* v___x_4775_; 
if (v_isShared_4773_ == 0)
{
lean_ctor_set_tag(v___x_4772_, 0);
v___x_4775_ = v___x_4772_;
goto v_reusejp_4774_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v_val_4770_);
v___x_4775_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4774_;
}
v_reusejp_4774_:
{
lean_object* v___x_4776_; 
v___x_4776_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3(v_optionName_4727_, v_a_4729_, v___x_4775_, v___y_4710_, v___y_4711_);
return v___x_4776_;
}
}
}
v___jp_4736_:
{
lean_object* v___x_4737_; 
v___x_4737_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_defValue_4731_);
lean_dec_ref(v_defValue_4731_);
if (lean_obj_tag(v___x_4737_) == 1)
{
lean_object* v_val_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; 
lean_dec(v_optionName_4727_);
v_val_4738_ = lean_ctor_get(v___x_4737_, 0);
lean_inc(v_val_4738_);
lean_dec_ref_known(v___x_4737_, 1);
v___x_4739_ = lean_obj_once(&l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__1, &l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__1_once, _init_l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__1);
v___x_4740_ = l_Lean_MessageData_ofSyntax(v_val_4709_);
v___x_4741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4741_, 0, v___x_4739_);
lean_ctor_set(v___x_4741_, 1, v___x_4740_);
v___x_4742_ = lean_obj_once(&l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__3, &l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__3_once, _init_l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__3);
v___x_4743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4743_, 0, v___x_4741_);
lean_ctor_set(v___x_4743_, 1, v___x_4742_);
v___x_4744_ = l_Lean_MessageData_ofExpr(v_val_4738_);
v___x_4745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4745_, 0, v___x_4743_);
lean_ctor_set(v___x_4745_, 1, v___x_4744_);
v___x_4746_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1);
v___x_4747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4747_, 0, v___x_4745_);
lean_ctor_set(v___x_4747_, 1, v___x_4746_);
v___x_4748_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg(v___x_4747_, v___y_4710_, v___y_4711_);
return v___x_4748_;
}
else
{
lean_object* v___x_4749_; 
lean_dec(v___x_4737_);
lean_dec(v_val_4709_);
v___x_4749_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg(v_optionName_4727_, v___y_4710_, v___y_4711_);
return v___x_4749_;
}
}
}
}
else
{
lean_object* v_a_4780_; lean_object* v___x_4782_; uint8_t v_isShared_4783_; uint8_t v_isSharedCheck_4793_; 
lean_dec(v_optionName_4727_);
lean_dec(v_val_4709_);
lean_dec(v_id_4708_);
v_a_4780_ = lean_ctor_get(v___x_4728_, 0);
v_isSharedCheck_4793_ = !lean_is_exclusive(v___x_4728_);
if (v_isSharedCheck_4793_ == 0)
{
v___x_4782_ = v___x_4728_;
v_isShared_4783_ = v_isSharedCheck_4793_;
goto v_resetjp_4781_;
}
else
{
lean_inc(v_a_4780_);
lean_dec(v___x_4728_);
v___x_4782_ = lean_box(0);
v_isShared_4783_ = v_isSharedCheck_4793_;
goto v_resetjp_4781_;
}
v_resetjp_4781_:
{
lean_object* v___x_4784_; lean_object* v___x_4786_; 
v___x_4784_ = lean_io_error_to_string(v_a_4780_);
if (v_isShared_4725_ == 0)
{
lean_ctor_set_tag(v___x_4724_, 3);
lean_ctor_set(v___x_4724_, 0, v___x_4784_);
v___x_4786_ = v___x_4724_;
goto v_reusejp_4785_;
}
else
{
lean_object* v_reuseFailAlloc_4792_; 
v_reuseFailAlloc_4792_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4792_, 0, v___x_4784_);
v___x_4786_ = v_reuseFailAlloc_4792_;
goto v_reusejp_4785_;
}
v_reusejp_4785_:
{
lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4790_; 
v___x_4787_ = l_Lean_MessageData_ofFormat(v___x_4786_);
v___x_4788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4788_, 0, v_a_4714_);
lean_ctor_set(v___x_4788_, 1, v___x_4787_);
if (v_isShared_4783_ == 0)
{
lean_ctor_set(v___x_4782_, 0, v___x_4788_);
v___x_4790_ = v___x_4782_;
goto v_reusejp_4789_;
}
else
{
lean_object* v_reuseFailAlloc_4791_; 
v_reuseFailAlloc_4791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4791_, 0, v___x_4788_);
v___x_4790_ = v_reuseFailAlloc_4791_;
goto v_reusejp_4789_;
}
v_reusejp_4789_:
{
return v___x_4790_;
}
}
}
}
}
}
else
{
lean_object* v_a_4796_; lean_object* v___x_4798_; uint8_t v_isShared_4799_; uint8_t v_isSharedCheck_4803_; 
lean_dec(v_val_4709_);
lean_dec(v_id_4708_);
v_a_4796_ = lean_ctor_get(v___x_4713_, 0);
v_isSharedCheck_4803_ = !lean_is_exclusive(v___x_4713_);
if (v_isSharedCheck_4803_ == 0)
{
v___x_4798_ = v___x_4713_;
v_isShared_4799_ = v_isSharedCheck_4803_;
goto v_resetjp_4797_;
}
else
{
lean_inc(v_a_4796_);
lean_dec(v___x_4713_);
v___x_4798_ = lean_box(0);
v_isShared_4799_ = v_isSharedCheck_4803_;
goto v_resetjp_4797_;
}
v_resetjp_4797_:
{
lean_object* v___x_4801_; 
if (v_isShared_4799_ == 0)
{
v___x_4801_ = v___x_4798_;
goto v_reusejp_4800_;
}
else
{
lean_object* v_reuseFailAlloc_4802_; 
v_reuseFailAlloc_4802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4802_, 0, v_a_4796_);
v___x_4801_ = v_reuseFailAlloc_4802_;
goto v_reusejp_4800_;
}
v_reusejp_4800_:
{
return v___x_4801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___boxed(lean_object* v_id_4804_, lean_object* v_val_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_){
_start:
{
lean_object* v_res_4809_; 
v_res_4809_ = l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0(v_id_4804_, v_val_4805_, v___y_4806_, v___y_4807_);
lean_dec(v___y_4807_);
lean_dec_ref(v___y_4806_);
return v_res_4809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg___lam__0(lean_object* v___x_4810_, lean_object* v___x_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_){
_start:
{
lean_object* v___x_4815_; 
v___x_4815_ = l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0(v___x_4810_, v___x_4811_, v___y_4812_, v___y_4813_);
if (lean_obj_tag(v___x_4815_) == 0)
{
lean_object* v_a_4816_; lean_object* v___x_4818_; uint8_t v_isShared_4819_; uint8_t v_isSharedCheck_4824_; 
v_a_4816_ = lean_ctor_get(v___x_4815_, 0);
v_isSharedCheck_4824_ = !lean_is_exclusive(v___x_4815_);
if (v_isSharedCheck_4824_ == 0)
{
v___x_4818_ = v___x_4815_;
v_isShared_4819_ = v_isSharedCheck_4824_;
goto v_resetjp_4817_;
}
else
{
lean_inc(v_a_4816_);
lean_dec(v___x_4815_);
v___x_4818_ = lean_box(0);
v_isShared_4819_ = v_isSharedCheck_4824_;
goto v_resetjp_4817_;
}
v_resetjp_4817_:
{
lean_object* v_fst_4820_; lean_object* v___x_4822_; 
v_fst_4820_ = lean_ctor_get(v_a_4816_, 0);
lean_inc(v_fst_4820_);
lean_dec(v_a_4816_);
if (v_isShared_4819_ == 0)
{
lean_ctor_set(v___x_4818_, 0, v_fst_4820_);
v___x_4822_ = v___x_4818_;
goto v_reusejp_4821_;
}
else
{
lean_object* v_reuseFailAlloc_4823_; 
v_reuseFailAlloc_4823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4823_, 0, v_fst_4820_);
v___x_4822_ = v_reuseFailAlloc_4823_;
goto v_reusejp_4821_;
}
v_reusejp_4821_:
{
return v___x_4822_;
}
}
}
else
{
lean_object* v_a_4825_; lean_object* v___x_4827_; uint8_t v_isShared_4828_; uint8_t v_isSharedCheck_4841_; 
v_a_4825_ = lean_ctor_get(v___x_4815_, 0);
v_isSharedCheck_4841_ = !lean_is_exclusive(v___x_4815_);
if (v_isSharedCheck_4841_ == 0)
{
v___x_4827_ = v___x_4815_;
v_isShared_4828_ = v_isSharedCheck_4841_;
goto v_resetjp_4826_;
}
else
{
lean_inc(v_a_4825_);
lean_dec(v___x_4815_);
v___x_4827_ = lean_box(0);
v_isShared_4828_ = v_isSharedCheck_4841_;
goto v_resetjp_4826_;
}
v_resetjp_4826_:
{
uint8_t v___x_4829_; 
v___x_4829_ = l_Lean_Exception_isInterrupt(v_a_4825_);
if (v___x_4829_ == 0)
{
lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v_scopes_4832_; lean_object* v___x_4833_; lean_object* v_opts_4834_; lean_object* v___x_4836_; 
lean_dec(v_a_4825_);
v___x_4830_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4831_ = lean_st_ref_get(v___y_4813_);
v_scopes_4832_ = lean_ctor_get(v___x_4831_, 2);
lean_inc(v_scopes_4832_);
lean_dec(v___x_4831_);
v___x_4833_ = l_List_head_x21___redArg(v___x_4830_, v_scopes_4832_);
lean_dec(v_scopes_4832_);
v_opts_4834_ = lean_ctor_get(v___x_4833_, 1);
lean_inc_ref(v_opts_4834_);
lean_dec(v___x_4833_);
if (v_isShared_4828_ == 0)
{
lean_ctor_set_tag(v___x_4827_, 0);
lean_ctor_set(v___x_4827_, 0, v_opts_4834_);
v___x_4836_ = v___x_4827_;
goto v_reusejp_4835_;
}
else
{
lean_object* v_reuseFailAlloc_4837_; 
v_reuseFailAlloc_4837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4837_, 0, v_opts_4834_);
v___x_4836_ = v_reuseFailAlloc_4837_;
goto v_reusejp_4835_;
}
v_reusejp_4835_:
{
return v___x_4836_;
}
}
else
{
lean_object* v___x_4839_; 
if (v_isShared_4828_ == 0)
{
v___x_4839_ = v___x_4827_;
goto v_reusejp_4838_;
}
else
{
lean_object* v_reuseFailAlloc_4840_; 
v_reuseFailAlloc_4840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4840_, 0, v_a_4825_);
v___x_4839_ = v_reuseFailAlloc_4840_;
goto v_reusejp_4838_;
}
v_reusejp_4838_:
{
return v___x_4839_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg___lam__0___boxed(lean_object* v___x_4842_, lean_object* v___x_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_){
_start:
{
lean_object* v_res_4847_; 
v_res_4847_ = l_Lean_Linter_MissingDocs_handleIn___redArg___lam__0(v___x_4842_, v___x_4843_, v___y_4844_, v___y_4845_);
lean_dec(v___y_4845_);
lean_dec_ref(v___y_4844_);
return v_res_4847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg___lam__1(lean_object* v_a_4848_, lean_object* v_x_4849_){
_start:
{
lean_object* v_header_4850_; lean_object* v_currNamespace_4851_; lean_object* v_openDecls_4852_; lean_object* v_levelNames_4853_; lean_object* v_varDecls_4854_; lean_object* v_varUIds_4855_; lean_object* v_includedVars_4856_; lean_object* v_omittedVars_4857_; uint8_t v_isNoncomputable_4858_; uint8_t v_isPublic_4859_; uint8_t v_isMeta_4860_; lean_object* v_attrs_4861_; lean_object* v___x_4863_; uint8_t v_isShared_4864_; uint8_t v_isSharedCheck_4868_; 
v_header_4850_ = lean_ctor_get(v_x_4849_, 0);
v_currNamespace_4851_ = lean_ctor_get(v_x_4849_, 2);
v_openDecls_4852_ = lean_ctor_get(v_x_4849_, 3);
v_levelNames_4853_ = lean_ctor_get(v_x_4849_, 4);
v_varDecls_4854_ = lean_ctor_get(v_x_4849_, 5);
v_varUIds_4855_ = lean_ctor_get(v_x_4849_, 6);
v_includedVars_4856_ = lean_ctor_get(v_x_4849_, 7);
v_omittedVars_4857_ = lean_ctor_get(v_x_4849_, 8);
v_isNoncomputable_4858_ = lean_ctor_get_uint8(v_x_4849_, sizeof(void*)*10);
v_isPublic_4859_ = lean_ctor_get_uint8(v_x_4849_, sizeof(void*)*10 + 1);
v_isMeta_4860_ = lean_ctor_get_uint8(v_x_4849_, sizeof(void*)*10 + 2);
v_attrs_4861_ = lean_ctor_get(v_x_4849_, 9);
v_isSharedCheck_4868_ = !lean_is_exclusive(v_x_4849_);
if (v_isSharedCheck_4868_ == 0)
{
lean_object* v_unused_4869_; 
v_unused_4869_ = lean_ctor_get(v_x_4849_, 1);
lean_dec(v_unused_4869_);
v___x_4863_ = v_x_4849_;
v_isShared_4864_ = v_isSharedCheck_4868_;
goto v_resetjp_4862_;
}
else
{
lean_inc(v_attrs_4861_);
lean_inc(v_omittedVars_4857_);
lean_inc(v_includedVars_4856_);
lean_inc(v_varUIds_4855_);
lean_inc(v_varDecls_4854_);
lean_inc(v_levelNames_4853_);
lean_inc(v_openDecls_4852_);
lean_inc(v_currNamespace_4851_);
lean_inc(v_header_4850_);
lean_dec(v_x_4849_);
v___x_4863_ = lean_box(0);
v_isShared_4864_ = v_isSharedCheck_4868_;
goto v_resetjp_4862_;
}
v_resetjp_4862_:
{
lean_object* v___x_4866_; 
if (v_isShared_4864_ == 0)
{
lean_ctor_set(v___x_4863_, 1, v_a_4848_);
v___x_4866_ = v___x_4863_;
goto v_reusejp_4865_;
}
else
{
lean_object* v_reuseFailAlloc_4867_; 
v_reuseFailAlloc_4867_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v_reuseFailAlloc_4867_, 0, v_header_4850_);
lean_ctor_set(v_reuseFailAlloc_4867_, 1, v_a_4848_);
lean_ctor_set(v_reuseFailAlloc_4867_, 2, v_currNamespace_4851_);
lean_ctor_set(v_reuseFailAlloc_4867_, 3, v_openDecls_4852_);
lean_ctor_set(v_reuseFailAlloc_4867_, 4, v_levelNames_4853_);
lean_ctor_set(v_reuseFailAlloc_4867_, 5, v_varDecls_4854_);
lean_ctor_set(v_reuseFailAlloc_4867_, 6, v_varUIds_4855_);
lean_ctor_set(v_reuseFailAlloc_4867_, 7, v_includedVars_4856_);
lean_ctor_set(v_reuseFailAlloc_4867_, 8, v_omittedVars_4857_);
lean_ctor_set(v_reuseFailAlloc_4867_, 9, v_attrs_4861_);
lean_ctor_set_uint8(v_reuseFailAlloc_4867_, sizeof(void*)*10, v_isNoncomputable_4858_);
lean_ctor_set_uint8(v_reuseFailAlloc_4867_, sizeof(void*)*10 + 1, v_isPublic_4859_);
lean_ctor_set_uint8(v_reuseFailAlloc_4867_, sizeof(void*)*10 + 2, v_isMeta_4860_);
v___x_4866_ = v_reuseFailAlloc_4867_;
goto v_reusejp_4865_;
}
v_reusejp_4865_:
{
return v___x_4866_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___redArg(uint8_t v_flag_4870_, lean_object* v___y_4871_){
_start:
{
lean_object* v___x_4873_; lean_object* v_infoState_4874_; lean_object* v_env_4875_; lean_object* v_messages_4876_; lean_object* v_scopes_4877_; lean_object* v_usedQuotCtxts_4878_; lean_object* v_nextMacroScope_4879_; lean_object* v_maxRecDepth_4880_; lean_object* v_ngen_4881_; lean_object* v_auxDeclNGen_4882_; lean_object* v_traceState_4883_; lean_object* v_snapshotTasks_4884_; lean_object* v_prevLinterStates_4885_; lean_object* v_codeQualityEntryTasks_4886_; lean_object* v___x_4888_; uint8_t v_isShared_4889_; uint8_t v_isSharedCheck_4906_; 
v___x_4873_ = lean_st_ref_take(v___y_4871_);
v_infoState_4874_ = lean_ctor_get(v___x_4873_, 8);
v_env_4875_ = lean_ctor_get(v___x_4873_, 0);
v_messages_4876_ = lean_ctor_get(v___x_4873_, 1);
v_scopes_4877_ = lean_ctor_get(v___x_4873_, 2);
v_usedQuotCtxts_4878_ = lean_ctor_get(v___x_4873_, 3);
v_nextMacroScope_4879_ = lean_ctor_get(v___x_4873_, 4);
v_maxRecDepth_4880_ = lean_ctor_get(v___x_4873_, 5);
v_ngen_4881_ = lean_ctor_get(v___x_4873_, 6);
v_auxDeclNGen_4882_ = lean_ctor_get(v___x_4873_, 7);
v_traceState_4883_ = lean_ctor_get(v___x_4873_, 9);
v_snapshotTasks_4884_ = lean_ctor_get(v___x_4873_, 10);
v_prevLinterStates_4885_ = lean_ctor_get(v___x_4873_, 11);
v_codeQualityEntryTasks_4886_ = lean_ctor_get(v___x_4873_, 12);
v_isSharedCheck_4906_ = !lean_is_exclusive(v___x_4873_);
if (v_isSharedCheck_4906_ == 0)
{
v___x_4888_ = v___x_4873_;
v_isShared_4889_ = v_isSharedCheck_4906_;
goto v_resetjp_4887_;
}
else
{
lean_inc(v_codeQualityEntryTasks_4886_);
lean_inc(v_prevLinterStates_4885_);
lean_inc(v_snapshotTasks_4884_);
lean_inc(v_traceState_4883_);
lean_inc(v_infoState_4874_);
lean_inc(v_auxDeclNGen_4882_);
lean_inc(v_ngen_4881_);
lean_inc(v_maxRecDepth_4880_);
lean_inc(v_nextMacroScope_4879_);
lean_inc(v_usedQuotCtxts_4878_);
lean_inc(v_scopes_4877_);
lean_inc(v_messages_4876_);
lean_inc(v_env_4875_);
lean_dec(v___x_4873_);
v___x_4888_ = lean_box(0);
v_isShared_4889_ = v_isSharedCheck_4906_;
goto v_resetjp_4887_;
}
v_resetjp_4887_:
{
lean_object* v_assignment_4890_; lean_object* v_lazyAssignment_4891_; lean_object* v_trees_4892_; lean_object* v___x_4894_; uint8_t v_isShared_4895_; uint8_t v_isSharedCheck_4905_; 
v_assignment_4890_ = lean_ctor_get(v_infoState_4874_, 0);
v_lazyAssignment_4891_ = lean_ctor_get(v_infoState_4874_, 1);
v_trees_4892_ = lean_ctor_get(v_infoState_4874_, 2);
v_isSharedCheck_4905_ = !lean_is_exclusive(v_infoState_4874_);
if (v_isSharedCheck_4905_ == 0)
{
v___x_4894_ = v_infoState_4874_;
v_isShared_4895_ = v_isSharedCheck_4905_;
goto v_resetjp_4893_;
}
else
{
lean_inc(v_trees_4892_);
lean_inc(v_lazyAssignment_4891_);
lean_inc(v_assignment_4890_);
lean_dec(v_infoState_4874_);
v___x_4894_ = lean_box(0);
v_isShared_4895_ = v_isSharedCheck_4905_;
goto v_resetjp_4893_;
}
v_resetjp_4893_:
{
lean_object* v___x_4896_; lean_object* v___x_4898_; 
v___x_4896_ = lean_box(0);
if (v_isShared_4895_ == 0)
{
v___x_4898_ = v___x_4894_;
goto v_reusejp_4897_;
}
else
{
lean_object* v_reuseFailAlloc_4904_; 
v_reuseFailAlloc_4904_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4904_, 0, v_assignment_4890_);
lean_ctor_set(v_reuseFailAlloc_4904_, 1, v_lazyAssignment_4891_);
lean_ctor_set(v_reuseFailAlloc_4904_, 2, v_trees_4892_);
v___x_4898_ = v_reuseFailAlloc_4904_;
goto v_reusejp_4897_;
}
v_reusejp_4897_:
{
lean_object* v___x_4900_; 
lean_ctor_set_uint8(v___x_4898_, sizeof(void*)*3, v_flag_4870_);
if (v_isShared_4889_ == 0)
{
lean_ctor_set(v___x_4888_, 8, v___x_4898_);
v___x_4900_ = v___x_4888_;
goto v_reusejp_4899_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v_env_4875_);
lean_ctor_set(v_reuseFailAlloc_4903_, 1, v_messages_4876_);
lean_ctor_set(v_reuseFailAlloc_4903_, 2, v_scopes_4877_);
lean_ctor_set(v_reuseFailAlloc_4903_, 3, v_usedQuotCtxts_4878_);
lean_ctor_set(v_reuseFailAlloc_4903_, 4, v_nextMacroScope_4879_);
lean_ctor_set(v_reuseFailAlloc_4903_, 5, v_maxRecDepth_4880_);
lean_ctor_set(v_reuseFailAlloc_4903_, 6, v_ngen_4881_);
lean_ctor_set(v_reuseFailAlloc_4903_, 7, v_auxDeclNGen_4882_);
lean_ctor_set(v_reuseFailAlloc_4903_, 8, v___x_4898_);
lean_ctor_set(v_reuseFailAlloc_4903_, 9, v_traceState_4883_);
lean_ctor_set(v_reuseFailAlloc_4903_, 10, v_snapshotTasks_4884_);
lean_ctor_set(v_reuseFailAlloc_4903_, 11, v_prevLinterStates_4885_);
lean_ctor_set(v_reuseFailAlloc_4903_, 12, v_codeQualityEntryTasks_4886_);
v___x_4900_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4899_;
}
v_reusejp_4899_:
{
lean_object* v___x_4901_; lean_object* v___x_4902_; 
v___x_4901_ = lean_st_ref_put(v___y_4871_, v___x_4900_);
v___x_4902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4902_, 0, v___x_4896_);
return v___x_4902_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___redArg___boxed(lean_object* v_flag_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_){
_start:
{
uint8_t v_flag_boxed_4910_; lean_object* v_res_4911_; 
v_flag_boxed_4910_ = lean_unbox(v_flag_4907_);
v_res_4911_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___redArg(v_flag_boxed_4910_, v___y_4908_);
lean_dec(v___y_4908_);
return v_res_4911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1___redArg(uint8_t v_flag_4912_, lean_object* v_x_4913_, lean_object* v___y_4914_, lean_object* v___y_4915_){
_start:
{
lean_object* v___x_4917_; lean_object* v_infoState_4918_; uint8_t v_enabled_4919_; lean_object* v_a_4921_; lean_object* v___x_4931_; lean_object* v___x_4932_; 
v___x_4917_ = lean_st_ref_get(v___y_4915_);
v_infoState_4918_ = lean_ctor_get(v___x_4917_, 8);
lean_inc_ref(v_infoState_4918_);
lean_dec(v___x_4917_);
v_enabled_4919_ = lean_ctor_get_uint8(v_infoState_4918_, sizeof(void*)*3);
lean_dec_ref(v_infoState_4918_);
v___x_4931_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___redArg(v_flag_4912_, v___y_4915_);
lean_dec_ref(v___x_4931_);
lean_inc(v___y_4915_);
lean_inc_ref(v___y_4914_);
v___x_4932_ = lean_apply_3(v_x_4913_, v___y_4914_, v___y_4915_, lean_box(0));
if (lean_obj_tag(v___x_4932_) == 0)
{
lean_object* v_a_4933_; lean_object* v___x_4934_; lean_object* v___x_4936_; uint8_t v_isShared_4937_; uint8_t v_isSharedCheck_4941_; 
v_a_4933_ = lean_ctor_get(v___x_4932_, 0);
lean_inc(v_a_4933_);
lean_dec_ref_known(v___x_4932_, 1);
v___x_4934_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___redArg(v_enabled_4919_, v___y_4915_);
v_isSharedCheck_4941_ = !lean_is_exclusive(v___x_4934_);
if (v_isSharedCheck_4941_ == 0)
{
lean_object* v_unused_4942_; 
v_unused_4942_ = lean_ctor_get(v___x_4934_, 0);
lean_dec(v_unused_4942_);
v___x_4936_ = v___x_4934_;
v_isShared_4937_ = v_isSharedCheck_4941_;
goto v_resetjp_4935_;
}
else
{
lean_dec(v___x_4934_);
v___x_4936_ = lean_box(0);
v_isShared_4937_ = v_isSharedCheck_4941_;
goto v_resetjp_4935_;
}
v_resetjp_4935_:
{
lean_object* v___x_4939_; 
if (v_isShared_4937_ == 0)
{
lean_ctor_set(v___x_4936_, 0, v_a_4933_);
v___x_4939_ = v___x_4936_;
goto v_reusejp_4938_;
}
else
{
lean_object* v_reuseFailAlloc_4940_; 
v_reuseFailAlloc_4940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4940_, 0, v_a_4933_);
v___x_4939_ = v_reuseFailAlloc_4940_;
goto v_reusejp_4938_;
}
v_reusejp_4938_:
{
return v___x_4939_;
}
}
}
else
{
lean_object* v_a_4943_; 
v_a_4943_ = lean_ctor_get(v___x_4932_, 0);
lean_inc(v_a_4943_);
lean_dec_ref_known(v___x_4932_, 1);
v_a_4921_ = v_a_4943_;
goto v___jp_4920_;
}
v___jp_4920_:
{
lean_object* v___x_4922_; lean_object* v___x_4924_; uint8_t v_isShared_4925_; uint8_t v_isSharedCheck_4929_; 
v___x_4922_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___redArg(v_enabled_4919_, v___y_4915_);
v_isSharedCheck_4929_ = !lean_is_exclusive(v___x_4922_);
if (v_isSharedCheck_4929_ == 0)
{
lean_object* v_unused_4930_; 
v_unused_4930_ = lean_ctor_get(v___x_4922_, 0);
lean_dec(v_unused_4930_);
v___x_4924_ = v___x_4922_;
v_isShared_4925_ = v_isSharedCheck_4929_;
goto v_resetjp_4923_;
}
else
{
lean_dec(v___x_4922_);
v___x_4924_ = lean_box(0);
v_isShared_4925_ = v_isSharedCheck_4929_;
goto v_resetjp_4923_;
}
v_resetjp_4923_:
{
lean_object* v___x_4927_; 
if (v_isShared_4925_ == 0)
{
lean_ctor_set_tag(v___x_4924_, 1);
lean_ctor_set(v___x_4924_, 0, v_a_4921_);
v___x_4927_ = v___x_4924_;
goto v_reusejp_4926_;
}
else
{
lean_object* v_reuseFailAlloc_4928_; 
v_reuseFailAlloc_4928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4928_, 0, v_a_4921_);
v___x_4927_ = v_reuseFailAlloc_4928_;
goto v_reusejp_4926_;
}
v_reusejp_4926_:
{
return v___x_4927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1___redArg___boxed(lean_object* v_flag_4944_, lean_object* v_x_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_){
_start:
{
uint8_t v_flag_boxed_4949_; lean_object* v_res_4950_; 
v_flag_boxed_4949_ = lean_unbox(v_flag_4944_);
v_res_4950_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1___redArg(v_flag_boxed_4949_, v_x_4945_, v___y_4946_, v___y_4947_);
lean_dec(v___y_4947_);
lean_dec_ref(v___y_4946_);
return v_res_4950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg(lean_object* v_stx_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_){
_start:
{
lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; uint8_t v___x_4965_; 
v___x_4961_ = lean_unsigned_to_nat(0u);
v___x_4962_ = l_Lean_Syntax_getArg(v_stx_4957_, v___x_4961_);
lean_inc(v___x_4962_);
v___x_4963_ = l_Lean_Syntax_getKind(v___x_4962_);
v___x_4964_ = ((lean_object*)(l_Lean_Linter_MissingDocs_handleIn___redArg___closed__1));
v___x_4965_ = lean_name_eq(v___x_4963_, v___x_4964_);
lean_dec(v___x_4963_);
if (v___x_4965_ == 0)
{
lean_object* v___x_4966_; lean_object* v_run_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; 
lean_dec(v___x_4962_);
v___x_4966_ = ((lean_object*)(l_Lean_Linter_MissingDocs_missingDocs));
v_run_4967_ = lean_ctor_get(v___x_4966_, 0);
v___x_4968_ = lean_unsigned_to_nat(2u);
v___x_4969_ = l_Lean_Syntax_getArg(v_stx_4957_, v___x_4968_);
lean_inc_ref(v_run_4967_);
lean_inc(v_a_4959_);
lean_inc_ref(v_a_4958_);
v___x_4970_ = lean_apply_4(v_run_4967_, v___x_4969_, v_a_4958_, v_a_4959_, lean_box(0));
return v___x_4970_;
}
else
{
uint8_t v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___f_4976_; lean_object* v___x_4977_; 
v___x_4971_ = 0;
v___x_4972_ = lean_unsigned_to_nat(1u);
v___x_4973_ = l_Lean_Syntax_getArg(v___x_4962_, v___x_4972_);
v___x_4974_ = lean_unsigned_to_nat(3u);
v___x_4975_ = l_Lean_Syntax_getArg(v___x_4962_, v___x_4974_);
lean_dec(v___x_4962_);
v___f_4976_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_handleIn___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_4976_, 0, v___x_4973_);
lean_closure_set(v___f_4976_, 1, v___x_4975_);
v___x_4977_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1___redArg(v___x_4971_, v___f_4976_, v_a_4958_, v_a_4959_);
if (lean_obj_tag(v___x_4977_) == 0)
{
lean_object* v_a_4978_; lean_object* v___x_4979_; lean_object* v_run_4980_; lean_object* v___f_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; 
v_a_4978_ = lean_ctor_get(v___x_4977_, 0);
lean_inc(v_a_4978_);
lean_dec_ref_known(v___x_4977_, 1);
v___x_4979_ = ((lean_object*)(l_Lean_Linter_MissingDocs_missingDocs));
v_run_4980_ = lean_ctor_get(v___x_4979_, 0);
v___f_4981_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_handleIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4981_, 0, v_a_4978_);
v___x_4982_ = lean_unsigned_to_nat(2u);
v___x_4983_ = l_Lean_Syntax_getArg(v_stx_4957_, v___x_4982_);
lean_inc_ref(v_run_4980_);
v___x_4984_ = lean_apply_1(v_run_4980_, v___x_4983_);
v___x_4985_ = l_Lean_Elab_Command_withScope___redArg(v___f_4981_, v___x_4984_, v_a_4958_, v_a_4959_);
return v___x_4985_;
}
else
{
lean_object* v_a_4986_; lean_object* v___x_4988_; uint8_t v_isShared_4989_; uint8_t v_isSharedCheck_4993_; 
v_a_4986_ = lean_ctor_get(v___x_4977_, 0);
v_isSharedCheck_4993_ = !lean_is_exclusive(v___x_4977_);
if (v_isSharedCheck_4993_ == 0)
{
v___x_4988_ = v___x_4977_;
v_isShared_4989_ = v_isSharedCheck_4993_;
goto v_resetjp_4987_;
}
else
{
lean_inc(v_a_4986_);
lean_dec(v___x_4977_);
v___x_4988_ = lean_box(0);
v_isShared_4989_ = v_isSharedCheck_4993_;
goto v_resetjp_4987_;
}
v_resetjp_4987_:
{
lean_object* v___x_4991_; 
if (v_isShared_4989_ == 0)
{
v___x_4991_ = v___x_4988_;
goto v_reusejp_4990_;
}
else
{
lean_object* v_reuseFailAlloc_4992_; 
v_reuseFailAlloc_4992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4992_, 0, v_a_4986_);
v___x_4991_ = v_reuseFailAlloc_4992_;
goto v_reusejp_4990_;
}
v_reusejp_4990_:
{
return v___x_4991_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg___boxed(lean_object* v_stx_4994_, lean_object* v_a_4995_, lean_object* v_a_4996_, lean_object* v_a_4997_){
_start:
{
lean_object* v_res_4998_; 
v_res_4998_ = l_Lean_Linter_MissingDocs_handleIn___redArg(v_stx_4994_, v_a_4995_, v_a_4996_);
lean_dec(v_a_4996_);
lean_dec_ref(v_a_4995_);
lean_dec(v_stx_4994_);
return v_res_4998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn(uint8_t v_x_4999_, lean_object* v_stx_5000_, lean_object* v_a_5001_, lean_object* v_a_5002_){
_start:
{
lean_object* v___x_5004_; 
v___x_5004_ = l_Lean_Linter_MissingDocs_handleIn___redArg(v_stx_5000_, v_a_5001_, v_a_5002_);
return v___x_5004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___boxed(lean_object* v_x_5005_, lean_object* v_stx_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_){
_start:
{
uint8_t v_x_4370__boxed_5010_; lean_object* v_res_5011_; 
v_x_4370__boxed_5010_ = lean_unbox(v_x_5005_);
v_res_5011_ = l_Lean_Linter_MissingDocs_handleIn(v_x_4370__boxed_5010_, v_stx_5006_, v_a_5007_, v_a_5008_);
lean_dec(v_a_5008_);
lean_dec_ref(v_a_5007_);
lean_dec(v_stx_5006_);
return v_res_5011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5(uint8_t v_flag_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_){
_start:
{
lean_object* v___x_5016_; 
v___x_5016_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___redArg(v_flag_5012_, v___y_5014_);
return v___x_5016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___boxed(lean_object* v_flag_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_){
_start:
{
uint8_t v_flag_boxed_5021_; lean_object* v_res_5022_; 
v_flag_boxed_5021_ = lean_unbox(v_flag_5017_);
v_res_5022_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5(v_flag_boxed_5021_, v___y_5018_, v___y_5019_);
lean_dec(v___y_5019_);
lean_dec_ref(v___y_5018_);
return v_res_5022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1(lean_object* v_00_u03b1_5023_, uint8_t v_flag_5024_, lean_object* v_x_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_){
_start:
{
lean_object* v___x_5029_; 
v___x_5029_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1___redArg(v_flag_5024_, v_x_5025_, v___y_5026_, v___y_5027_);
return v___x_5029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1___boxed(lean_object* v_00_u03b1_5030_, lean_object* v_flag_5031_, lean_object* v_x_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_){
_start:
{
uint8_t v_flag_boxed_5036_; lean_object* v_res_5037_; 
v_flag_boxed_5036_ = lean_unbox(v_flag_5031_);
v_res_5037_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1(v_00_u03b1_5030_, v_flag_boxed_5036_, v_x_5032_, v___y_5033_, v___y_5034_);
lean_dec(v___y_5034_);
lean_dec_ref(v___y_5033_);
return v_res_5037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2(lean_object* v_t_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_){
_start:
{
lean_object* v___x_5042_; 
v___x_5042_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2___redArg(v_t_5038_, v___y_5040_);
return v___x_5042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2___boxed(lean_object* v_t_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_){
_start:
{
lean_object* v_res_5047_; 
v_res_5047_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2(v_t_5043_, v___y_5044_, v___y_5045_);
lean_dec(v___y_5045_);
lean_dec_ref(v___y_5044_);
return v_res_5047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2(lean_object* v_00_u03b1_5048_, lean_object* v_optionName_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_){
_start:
{
lean_object* v___x_5053_; 
v___x_5053_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg(v_optionName_5049_, v___y_5050_, v___y_5051_);
return v___x_5053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___boxed(lean_object* v_00_u03b1_5054_, lean_object* v_optionName_5055_, lean_object* v___y_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_){
_start:
{
lean_object* v_res_5059_; 
v_res_5059_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2(v_00_u03b1_5054_, v_optionName_5055_, v___y_5056_, v___y_5057_);
lean_dec(v___y_5057_);
lean_dec_ref(v___y_5056_);
return v_res_5059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleIn___regBuiltin_Lean_Linter_MissingDocs_handleIn__1(){
_start:
{
lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; 
v___x_5067_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleIn___regBuiltin_Lean_Linter_MissingDocs_handleIn__1___closed__1));
v___x_5068_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_handleIn___boxed), 5, 0);
v___x_5069_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_5067_, v___x_5068_);
return v___x_5069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleIn___regBuiltin_Lean_Linter_MissingDocs_handleIn__1___boxed(lean_object* v_a_5070_){
_start:
{
lean_object* v_res_5071_; 
v_res_5071_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleIn___regBuiltin_Lean_Linter_MissingDocs_handleIn__1();
return v_res_5071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_MissingDocs_handleMutual_spec__0(lean_object* v_as_5072_, size_t v_i_5073_, size_t v_stop_5074_, lean_object* v_b_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_){
_start:
{
lean_object* v___x_5079_; lean_object* v_run_5080_; uint8_t v___x_5081_; 
v___x_5079_ = ((lean_object*)(l_Lean_Linter_MissingDocs_missingDocs));
v_run_5080_ = lean_ctor_get(v___x_5079_, 0);
v___x_5081_ = lean_usize_dec_eq(v_i_5073_, v_stop_5074_);
if (v___x_5081_ == 0)
{
lean_object* v___x_5082_; lean_object* v___x_5083_; 
v___x_5082_ = lean_array_uget_borrowed(v_as_5072_, v_i_5073_);
lean_inc_ref(v_run_5080_);
lean_inc(v___y_5077_);
lean_inc_ref(v___y_5076_);
lean_inc(v___x_5082_);
v___x_5083_ = lean_apply_4(v_run_5080_, v___x_5082_, v___y_5076_, v___y_5077_, lean_box(0));
if (lean_obj_tag(v___x_5083_) == 0)
{
lean_object* v_a_5084_; size_t v___x_5085_; size_t v___x_5086_; 
v_a_5084_ = lean_ctor_get(v___x_5083_, 0);
lean_inc(v_a_5084_);
lean_dec_ref_known(v___x_5083_, 1);
v___x_5085_ = ((size_t)1ULL);
v___x_5086_ = lean_usize_add(v_i_5073_, v___x_5085_);
v_i_5073_ = v___x_5086_;
v_b_5075_ = v_a_5084_;
goto _start;
}
else
{
return v___x_5083_;
}
}
else
{
lean_object* v___x_5088_; 
v___x_5088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5088_, 0, v_b_5075_);
return v___x_5088_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_MissingDocs_handleMutual_spec__0___boxed(lean_object* v_as_5089_, lean_object* v_i_5090_, lean_object* v_stop_5091_, lean_object* v_b_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_){
_start:
{
size_t v_i_boxed_5096_; size_t v_stop_boxed_5097_; lean_object* v_res_5098_; 
v_i_boxed_5096_ = lean_unbox_usize(v_i_5090_);
lean_dec(v_i_5090_);
v_stop_boxed_5097_ = lean_unbox_usize(v_stop_5091_);
lean_dec(v_stop_5091_);
v_res_5098_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_MissingDocs_handleMutual_spec__0(v_as_5089_, v_i_boxed_5096_, v_stop_boxed_5097_, v_b_5092_, v___y_5093_, v___y_5094_);
lean_dec(v___y_5094_);
lean_dec_ref(v___y_5093_);
lean_dec_ref(v_as_5089_);
return v_res_5098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleMutual___redArg(lean_object* v_stx_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_){
_start:
{
lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; uint8_t v___x_5109_; 
v___x_5103_ = lean_unsigned_to_nat(1u);
v___x_5104_ = l_Lean_Syntax_getArg(v_stx_5099_, v___x_5103_);
v___x_5105_ = l_Lean_Syntax_getArgs(v___x_5104_);
lean_dec(v___x_5104_);
v___x_5106_ = lean_unsigned_to_nat(0u);
v___x_5107_ = lean_array_get_size(v___x_5105_);
v___x_5108_ = lean_box(0);
v___x_5109_ = lean_nat_dec_lt(v___x_5106_, v___x_5107_);
if (v___x_5109_ == 0)
{
lean_object* v___x_5110_; 
lean_dec_ref(v___x_5105_);
v___x_5110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5110_, 0, v___x_5108_);
return v___x_5110_;
}
else
{
size_t v___x_5111_; size_t v___x_5112_; lean_object* v___x_5113_; 
v___x_5111_ = ((size_t)0ULL);
v___x_5112_ = lean_usize_of_nat(v___x_5107_);
v___x_5113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_MissingDocs_handleMutual_spec__0(v___x_5105_, v___x_5111_, v___x_5112_, v___x_5108_, v_a_5100_, v_a_5101_);
lean_dec_ref(v___x_5105_);
return v___x_5113_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleMutual___redArg___boxed(lean_object* v_stx_5114_, lean_object* v_a_5115_, lean_object* v_a_5116_, lean_object* v_a_5117_){
_start:
{
lean_object* v_res_5118_; 
v_res_5118_ = l_Lean_Linter_MissingDocs_handleMutual___redArg(v_stx_5114_, v_a_5115_, v_a_5116_);
lean_dec(v_a_5116_);
lean_dec_ref(v_a_5115_);
lean_dec(v_stx_5114_);
return v_res_5118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleMutual(uint8_t v_x_5119_, lean_object* v_stx_5120_, lean_object* v_a_5121_, lean_object* v_a_5122_){
_start:
{
lean_object* v___x_5124_; 
v___x_5124_ = l_Lean_Linter_MissingDocs_handleMutual___redArg(v_stx_5120_, v_a_5121_, v_a_5122_);
return v___x_5124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleMutual___boxed(lean_object* v_x_5125_, lean_object* v_stx_5126_, lean_object* v_a_5127_, lean_object* v_a_5128_, lean_object* v_a_5129_){
_start:
{
uint8_t v_x_392__boxed_5130_; lean_object* v_res_5131_; 
v_x_392__boxed_5130_ = lean_unbox(v_x_5125_);
v_res_5131_ = l_Lean_Linter_MissingDocs_handleMutual(v_x_392__boxed_5130_, v_stx_5126_, v_a_5127_, v_a_5128_);
lean_dec(v_a_5128_);
lean_dec_ref(v_a_5127_);
lean_dec(v_stx_5126_);
return v_res_5131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleMutual___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1(){
_start:
{
lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; 
v___x_5139_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleMutual___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1___closed__1));
v___x_5140_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_handleMutual___boxed), 5, 0);
v___x_5141_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_5139_, v___x_5140_);
return v___x_5141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleMutual___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1___boxed(lean_object* v_a_5142_){
_start:
{
lean_object* v_res_5143_; 
v_res_5143_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleMutual___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1();
return v_res_5143_;
}
}
lean_object* runtime_initialize_Lean_Parser_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_RegisterCommand(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_MissingDocs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Parser_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_RegisterCommand(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linter_missingDocs = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linter_missingDocs);
lean_dec_ref(res);
res = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_537855421____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_MissingDocs_builtinHandlersRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_MissingDocs_builtinHandlersRef);
lean_dec_ref(res);
res = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_MissingDocs_missingDocsExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_MissingDocs_missingDocsExt);
lean_dec_ref(res);
res = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_2727349317____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleIn___regBuiltin_Lean_Linter_MissingDocs_handleIn__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleMutual___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_MissingDocs(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_RegisterCommand(uint8_t builtin);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Linter_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_MissingDocs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_RegisterCommand(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_MissingDocs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_MissingDocs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_MissingDocs(builtin);
}
#ifdef __cplusplus
}
#endif
