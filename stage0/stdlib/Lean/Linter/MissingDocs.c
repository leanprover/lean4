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
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
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
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_sub(size_t, size_t);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_foldInfo___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_Syntax_getAtomVal(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "addBuiltinHandler"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "toHandler"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "Unexpected type for missing docs handler: Expected `"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__4_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "` or `"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__4_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__4_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__5_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__5_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__6_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "`, but `"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__6_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__6_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__7_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__7_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__8_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` has type"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__8_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__8_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__9_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__9_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(196, 60, 89, 104, 222, 184, 104, 61)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__4_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(109, 71, 38, 78, 110, 121, 74, 1)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__4_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__4_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__5_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__4_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(88, 142, 224, 55, 28, 93, 167, 225)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__5_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__5_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__6_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__5_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(209, 103, 172, 65, 70, 157, 34, 163)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__6_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__6_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__7_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__6_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(171, 148, 68, 129, 115, 167, 183, 177)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__7_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__7_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__8_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__7_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(206, 122, 164, 204, 198, 240, 47, 250)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__8_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__8_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__9_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__9_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__9_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__10_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__8_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__9_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(227, 126, 117, 226, 154, 200, 97, 116)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__10_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__10_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__11_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__11_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__11_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__12_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__10_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__11_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 196, 57, 107, 246, 197, 178, 184)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__12_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__12_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__13_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__12_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(127, 128, 182, 1, 36, 142, 177, 207)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__13_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__13_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__14_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__13_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(101, 71, 117, 107, 84, 87, 150, 165)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__14_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__14_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__15_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__14_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(184, 204, 34, 53, 202, 221, 81, 185)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__15_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__15_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__16_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__15_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),((lean_object*)(((size_t)(573930092) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(172, 197, 83, 166, 62, 29, 54, 93)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__16_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__16_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__17_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__17_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__17_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__18_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__16_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__17_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 131, 13, 165, 249, 155, 232, 74)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__18_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__18_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__19_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__19_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__19_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__20_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__18_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__19_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(3, 89, 8, 244, 216, 147, 164, 205)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__20_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__20_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__21_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__20_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(198, 101, 182, 233, 18, 154, 75, 102)}};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__21_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__21_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__22_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "adds a syntax traversal for the missing docs linter"};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__22_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__22_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__23_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "(builtin) "};
static const lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__23_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__23_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "versoCommentBody"};
static const lean_object* l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__4 = (const lean_object*)&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec(v_pre_146_);
lean_dec_ref_known(v_declName_145_, 2);
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
lean_object* v_a_306_; lean_object* v___y_311_; uint8_t v___x_313_; 
v___x_313_ = lean_usize_dec_eq(v_i_300_, v_stop_301_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_314_ = lean_array_uget_borrowed(v_as_299_, v_i_300_);
v___x_315_ = lean_unsigned_to_nat(0u);
v___x_316_ = lean_array_get_size(v___x_314_);
v___x_317_ = lean_nat_dec_lt(v___x_315_, v___x_316_);
if (v___x_317_ == 0)
{
v_a_306_ = v_b_302_;
goto v___jp_305_;
}
else
{
uint8_t v___x_318_; 
v___x_318_ = lean_nat_dec_le(v___x_316_, v___x_316_);
if (v___x_318_ == 0)
{
if (v___x_317_ == 0)
{
v_a_306_ = v_b_302_;
goto v___jp_305_;
}
else
{
size_t v___x_319_; size_t v___x_320_; lean_object* v___x_321_; 
v___x_319_ = ((size_t)0ULL);
v___x_320_ = lean_usize_of_nat(v___x_316_);
v___x_321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__spec__0(v___x_314_, v___x_319_, v___x_320_, v_b_302_, v___y_303_);
v___y_311_ = v___x_321_;
goto v___jp_310_;
}
}
else
{
size_t v___x_322_; size_t v___x_323_; lean_object* v___x_324_; 
v___x_322_ = ((size_t)0ULL);
v___x_323_ = lean_usize_of_nat(v___x_316_);
v___x_324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__spec__0(v___x_314_, v___x_322_, v___x_323_, v_b_302_, v___y_303_);
v___y_311_ = v___x_324_;
goto v___jp_310_;
}
}
}
else
{
lean_object* v___x_325_; 
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v_b_302_);
return v___x_325_;
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
v___jp_310_:
{
if (lean_obj_tag(v___y_311_) == 0)
{
lean_object* v_a_312_; 
v_a_312_ = lean_ctor_get(v___y_311_, 0);
lean_inc(v_a_312_);
lean_dec_ref_known(v___y_311_, 1);
v_a_306_ = v_a_312_;
goto v___jp_305_;
}
else
{
return v___y_311_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_326_, lean_object* v_i_327_, lean_object* v_stop_328_, lean_object* v_b_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
size_t v_i_boxed_332_; size_t v_stop_boxed_333_; lean_object* v_res_334_; 
v_i_boxed_332_ = lean_unbox_usize(v_i_327_);
lean_dec(v_i_327_);
v_stop_boxed_333_ = lean_unbox_usize(v_stop_328_);
lean_dec(v_stop_328_);
v_res_334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__spec__1(v_as_326_, v_i_boxed_332_, v_stop_boxed_333_, v_b_329_, v___y_330_);
lean_dec_ref(v___y_330_);
lean_dec_ref(v_as_326_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__5_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_(lean_object* v___x_335_, lean_object* v_as_336_, lean_object* v___y_337_){
_start:
{
lean_object* v_a_340_; lean_object* v___y_345_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_355_ = lean_st_ref_get(v___x_335_);
v___x_356_ = lean_unsigned_to_nat(0u);
v___x_357_ = lean_array_get_size(v_as_336_);
v___x_358_ = lean_nat_dec_lt(v___x_356_, v___x_357_);
if (v___x_358_ == 0)
{
v_a_340_ = v___x_355_;
goto v___jp_339_;
}
else
{
uint8_t v___x_359_; 
v___x_359_ = lean_nat_dec_le(v___x_357_, v___x_357_);
if (v___x_359_ == 0)
{
if (v___x_358_ == 0)
{
v_a_340_ = v___x_355_;
goto v___jp_339_;
}
else
{
size_t v___x_360_; size_t v___x_361_; lean_object* v___x_362_; 
v___x_360_ = ((size_t)0ULL);
v___x_361_ = lean_usize_of_nat(v___x_357_);
v___x_362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__spec__1(v_as_336_, v___x_360_, v___x_361_, v___x_355_, v___y_337_);
v___y_345_ = v___x_362_;
goto v___jp_344_;
}
}
else
{
size_t v___x_363_; size_t v___x_364_; lean_object* v___x_365_; 
v___x_363_ = ((size_t)0ULL);
v___x_364_ = lean_usize_of_nat(v___x_357_);
v___x_365_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__spec__1(v_as_336_, v___x_363_, v___x_364_, v___x_355_, v___y_337_);
v___y_345_ = v___x_365_;
goto v___jp_344_;
}
}
v___jp_339_:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_341_ = lean_box(0);
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v_a_340_);
v___x_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
return v___x_343_;
}
v___jp_344_:
{
if (lean_obj_tag(v___y_345_) == 0)
{
lean_object* v_a_346_; 
v_a_346_ = lean_ctor_get(v___y_345_, 0);
lean_inc(v_a_346_);
lean_dec_ref_known(v___y_345_, 1);
v_a_340_ = v_a_346_;
goto v___jp_339_;
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
v_a_347_ = lean_ctor_get(v___y_345_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___y_345_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___y_345_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___y_345_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__5_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2____boxed(lean_object* v___x_366_, lean_object* v_as_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__5_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_(v___x_366_, v_as_367_, v___y_368_);
lean_dec_ref(v___y_368_);
lean_dec_ref(v_as_367_);
lean_dec(v___x_366_);
return v_res_370_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__6_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_381_; lean_object* v___f_382_; 
v___x_381_ = l_Lean_Linter_MissingDocs_builtinHandlersRef;
v___f_382_ = lean_alloc_closure((void*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__4_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_382_, 0, v___x_381_);
return v___f_382_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__7_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_383_; lean_object* v___f_384_; 
v___x_383_ = l_Lean_Linter_MissingDocs_builtinHandlersRef;
v___f_384_ = lean_alloc_closure((void*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__5_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2____boxed), 4, 1);
lean_closure_set(v___f_384_, 0, v___x_383_);
return v___f_384_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__8_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___f_387_; lean_object* v___f_388_; lean_object* v___f_389_; lean_object* v___f_390_; lean_object* v___f_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_385_ = lean_box(0);
v___x_386_ = lean_box(2);
v___f_387_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__1_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_));
v___f_388_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__2_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_));
v___f_389_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__3_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_));
v___f_390_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__7_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__7_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__7_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_);
v___f_391_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__6_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__6_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__6_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_);
v___x_392_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_));
v___x_393_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
lean_ctor_set(v___x_393_, 1, v___f_391_);
lean_ctor_set(v___x_393_, 2, v___f_390_);
lean_ctor_set(v___x_393_, 3, v___f_389_);
lean_ctor_set(v___x_393_, 4, v___f_388_);
lean_ctor_set(v___x_393_, 5, v___f_387_);
lean_ctor_set(v___x_393_, 6, v___x_386_);
lean_ctor_set(v___x_393_, 7, v___x_385_);
return v___x_393_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__9_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___f_394_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__0_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_));
v___x_395_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__8_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__8_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__8_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_);
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v___f_394_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__9_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__9_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__9_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_);
v___x_399_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2____boxed(lean_object* v_a_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_103323494____hygCtx___hyg_2_();
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_addHandler(lean_object* v_env_402_, lean_object* v_declName_403_, lean_object* v_key_404_, lean_object* v_h_405_){
_start:
{
lean_object* v___x_406_; lean_object* v_toEnvExtension_407_; lean_object* v_asyncMode_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_406_ = l_Lean_Linter_MissingDocs_missingDocsExt;
v_toEnvExtension_407_ = lean_ctor_get(v___x_406_, 0);
v_asyncMode_408_ = lean_ctor_get(v_toEnvExtension_407_, 2);
v___x_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_409_, 0, v_key_404_);
lean_ctor_set(v___x_409_, 1, v_h_405_);
v___x_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_410_, 0, v_declName_403_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
v___x_411_ = lean_box(0);
v___x_412_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_406_, v_env_402_, v___x_410_, v_asyncMode_408_, v___x_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_getHandlers(lean_object* v_env_416_){
_start:
{
lean_object* v___x_417_; lean_object* v_toEnvExtension_418_; lean_object* v_asyncMode_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v_snd_423_; 
v___x_417_ = l_Lean_Linter_MissingDocs_missingDocsExt;
v_toEnvExtension_418_ = lean_ctor_get(v___x_417_, 0);
v_asyncMode_419_ = lean_ctor_get(v_toEnvExtension_418_, 2);
v___x_420_ = ((lean_object*)(l_Lean_Linter_MissingDocs_getHandlers___closed__0));
v___x_421_ = lean_box(0);
v___x_422_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_420_, v___x_417_, v_env_416_, v_asyncMode_419_, v___x_421_);
v_snd_423_ = lean_ctor_get(v___x_422_, 1);
lean_inc(v_snd_423_);
lean_dec(v___x_422_);
return v_snd_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_MissingDocs_missingDocs_spec__0_spec__0___redArg(lean_object* v_o_424_, lean_object* v___y_425_){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v_env_429_; lean_object* v___x_430_; lean_object* v_toEnvExtension_431_; lean_object* v_asyncMode_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v_merged_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_443_; 
v___x_427_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_428_ = lean_st_ref_get(v___y_425_);
v_env_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc_ref(v_env_429_);
lean_dec(v___x_428_);
v___x_430_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_431_ = lean_ctor_get(v___x_430_, 0);
v_asyncMode_432_ = lean_ctor_get(v_toEnvExtension_431_, 2);
v___x_433_ = lean_box(0);
v___x_434_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_427_, v___x_430_, v_env_429_, v_asyncMode_432_, v___x_433_);
v_merged_435_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_443_ == 0)
{
lean_object* v_unused_444_; 
v_unused_444_ = lean_ctor_get(v___x_434_, 1);
lean_dec(v_unused_444_);
v___x_437_ = v___x_434_;
v_isShared_438_ = v_isSharedCheck_443_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_merged_435_);
lean_dec(v___x_434_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_443_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_440_; 
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 1, v_merged_435_);
lean_ctor_set(v___x_437_, 0, v_o_424_);
v___x_440_ = v___x_437_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_o_424_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_merged_435_);
v___x_440_ = v_reuseFailAlloc_442_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_441_; 
v___x_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
return v___x_441_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_MissingDocs_missingDocs_spec__0_spec__0___redArg___boxed(lean_object* v_o_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_MissingDocs_missingDocs_spec__0_spec__0___redArg(v_o_445_, v___y_446_);
lean_dec(v___y_446_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_MissingDocs_missingDocs_spec__0(lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v_scopes_454_; lean_object* v___x_455_; lean_object* v_opts_456_; lean_object* v___x_457_; 
v___x_452_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_453_ = lean_st_ref_get(v___y_450_);
v_scopes_454_ = lean_ctor_get(v___x_453_, 2);
lean_inc(v_scopes_454_);
lean_dec(v___x_453_);
v___x_455_ = l_List_head_x21___redArg(v___x_452_, v_scopes_454_);
lean_dec(v_scopes_454_);
v_opts_456_ = lean_ctor_get(v___x_455_, 1);
lean_inc_ref(v_opts_456_);
lean_dec(v___x_455_);
v___x_457_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_MissingDocs_missingDocs_spec__0_spec__0___redArg(v_opts_456_, v___y_450_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_MissingDocs_missingDocs_spec__0___boxed(lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_MissingDocs_missingDocs_spec__0(v___y_458_, v___y_459_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_missingDocs___lam__0(lean_object* v_stx_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v___x_466_; lean_object* v_env_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_466_ = lean_st_ref_get(v___y_464_);
v_env_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc_ref(v_env_467_);
lean_dec(v___x_466_);
v___x_468_ = l_Lean_Linter_MissingDocs_getHandlers(v_env_467_);
lean_inc(v_stx_462_);
v___x_469_ = l_Lean_Syntax_getKind(v_stx_462_);
v___x_470_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_468_, v___x_469_);
lean_dec(v___x_469_);
lean_dec(v___x_468_);
if (lean_obj_tag(v___x_470_) == 1)
{
lean_object* v_val_471_; lean_object* v___x_472_; lean_object* v_a_473_; uint8_t v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v_val_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_val_471_);
lean_dec_ref_known(v___x_470_, 1);
v___x_472_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_MissingDocs_missingDocs_spec__0(v___y_463_, v___y_464_);
v_a_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_a_473_);
lean_dec_ref(v___x_472_);
v___x_474_ = l_Lean_Linter_getLinterMissingDocs(v_a_473_);
lean_dec(v_a_473_);
v___x_475_ = lean_box(v___x_474_);
lean_inc(v___y_464_);
lean_inc_ref(v___y_463_);
v___x_476_ = lean_apply_5(v_val_471_, v___x_475_, v_stx_462_, v___y_463_, v___y_464_, lean_box(0));
return v___x_476_;
}
else
{
lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec(v___x_470_);
lean_dec(v_stx_462_);
v___x_477_ = lean_box(0);
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
return v___x_478_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_missingDocs___lam__0___boxed(lean_object* v_stx_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_Linter_MissingDocs_missingDocs___lam__0(v_stx_479_, v___y_480_, v___y_481_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_MissingDocs_missingDocs_spec__0_spec__0(lean_object* v_o_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_MissingDocs_missingDocs_spec__0_spec__0___redArg(v_o_494_, v___y_496_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_MissingDocs_missingDocs_spec__0_spec__0___boxed(lean_object* v_o_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_MissingDocs_missingDocs_spec__0_spec__0(v_o_499_, v___y_500_, v___y_501_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_2727349317____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = ((lean_object*)(l_Lean_Linter_MissingDocs_missingDocs));
v___x_506_ = l_Lean_Elab_Command_addLinter(v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_2727349317____hygCtx___hyg_2____boxed(lean_object* v_a_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_2727349317____hygCtx___hyg_2_();
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_addBuiltinHandler(lean_object* v_key_509_, lean_object* v_h_510_){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_512_ = l_Lean_Linter_MissingDocs_builtinHandlersRef;
v___x_513_ = lean_st_ref_take(v___x_512_);
v___x_514_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_key_509_, v_h_510_, v___x_513_);
v___x_515_ = lean_st_ref_put(v___x_512_, v___x_514_);
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_addBuiltinHandler___boxed(lean_object* v_key_517_, lean_object* v_h_518_, lean_object* v_a_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v_key_517_, v_h_518_);
return v_res_520_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_521_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__0);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
return v___x_523_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__1, &l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__1_once, _init_l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__1);
v___x_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg(lean_object* v_env_526_, lean_object* v___y_527_){
_start:
{
lean_object* v___x_529_; lean_object* v_nextMacroScope_530_; lean_object* v_ngen_531_; lean_object* v_auxDeclNGen_532_; lean_object* v_traceState_533_; lean_object* v_messages_534_; lean_object* v_infoState_535_; lean_object* v_snapshotTasks_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_547_; 
v___x_529_ = lean_st_ref_take(v___y_527_);
v_nextMacroScope_530_ = lean_ctor_get(v___x_529_, 1);
v_ngen_531_ = lean_ctor_get(v___x_529_, 2);
v_auxDeclNGen_532_ = lean_ctor_get(v___x_529_, 3);
v_traceState_533_ = lean_ctor_get(v___x_529_, 4);
v_messages_534_ = lean_ctor_get(v___x_529_, 6);
v_infoState_535_ = lean_ctor_get(v___x_529_, 7);
v_snapshotTasks_536_ = lean_ctor_get(v___x_529_, 8);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_547_ == 0)
{
lean_object* v_unused_548_; lean_object* v_unused_549_; 
v_unused_548_ = lean_ctor_get(v___x_529_, 5);
lean_dec(v_unused_548_);
v_unused_549_ = lean_ctor_get(v___x_529_, 0);
lean_dec(v_unused_549_);
v___x_538_ = v___x_529_;
v_isShared_539_ = v_isSharedCheck_547_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_snapshotTasks_536_);
lean_inc(v_infoState_535_);
lean_inc(v_messages_534_);
lean_inc(v_traceState_533_);
lean_inc(v_auxDeclNGen_532_);
lean_inc(v_ngen_531_);
lean_inc(v_nextMacroScope_530_);
lean_dec(v___x_529_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_547_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_540_ = lean_box(0);
v___x_541_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__2);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 5, v___x_541_);
lean_ctor_set(v___x_538_, 0, v_env_526_);
v___x_543_ = v___x_538_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_env_526_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_nextMacroScope_530_);
lean_ctor_set(v_reuseFailAlloc_546_, 2, v_ngen_531_);
lean_ctor_set(v_reuseFailAlloc_546_, 3, v_auxDeclNGen_532_);
lean_ctor_set(v_reuseFailAlloc_546_, 4, v_traceState_533_);
lean_ctor_set(v_reuseFailAlloc_546_, 5, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_546_, 6, v_messages_534_);
lean_ctor_set(v_reuseFailAlloc_546_, 7, v_infoState_535_);
lean_ctor_set(v_reuseFailAlloc_546_, 8, v_snapshotTasks_536_);
v___x_543_ = v_reuseFailAlloc_546_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = lean_st_ref_put(v___y_527_, v___x_543_);
v___x_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_540_);
return v___x_545_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___boxed(lean_object* v_env_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg(v_env_550_, v___y_551_);
lean_dec(v___y_551_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2(lean_object* v_env_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg(v_env_554_, v___y_556_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___boxed(lean_object* v_env_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2(v_env_559_, v___y_560_, v___y_561_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
return v_res_563_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__0);
v___x_565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
return v___x_565_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_566_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
lean_ctor_set(v___x_568_, 2, v___x_567_);
lean_ctor_set(v___x_568_, 3, v___x_567_);
lean_ctor_set(v___x_568_, 4, v___x_566_);
lean_ctor_set(v___x_568_, 5, v___x_566_);
lean_ctor_set(v___x_568_, 6, v___x_566_);
lean_ctor_set(v___x_568_, 7, v___x_566_);
lean_ctor_set(v___x_568_, 8, v___x_566_);
lean_ctor_set(v___x_568_, 9, v___x_566_);
lean_ctor_set(v___x_568_, 10, v___x_566_);
return v___x_568_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_569_ = lean_unsigned_to_nat(32u);
v___x_570_ = lean_mk_empty_array_with_capacity(v___x_569_);
v___x_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
return v___x_571_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_572_ = ((size_t)5ULL);
v___x_573_ = lean_unsigned_to_nat(0u);
v___x_574_ = lean_unsigned_to_nat(32u);
v___x_575_ = lean_mk_empty_array_with_capacity(v___x_574_);
v___x_576_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_577_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v___x_575_);
lean_ctor_set(v___x_577_, 2, v___x_573_);
lean_ctor_set(v___x_577_, 3, v___x_573_);
lean_ctor_set_usize(v___x_577_, 4, v___x_572_);
return v___x_577_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_578_ = lean_box(1);
v___x_579_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_580_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_581_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v___x_579_);
lean_ctor_set(v___x_581_, 2, v___x_578_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v___x_586_; lean_object* v_toCold_587_; lean_object* v_env_588_; lean_object* v_options_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_586_ = lean_st_ref_get(v___y_584_);
v_toCold_587_ = lean_ctor_get(v___y_583_, 0);
v_env_588_ = lean_ctor_get(v___x_586_, 0);
lean_inc_ref(v_env_588_);
lean_dec(v___x_586_);
v_options_589_ = lean_ctor_get(v_toCold_587_, 2);
v___x_590_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_591_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__4);
lean_inc_ref(v_options_589_);
v___x_592_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_592_, 0, v_env_588_);
lean_ctor_set(v___x_592_, 1, v___x_590_);
lean_ctor_set(v___x_592_, 2, v___x_591_);
lean_ctor_set(v___x_592_, 3, v_options_589_);
v___x_593_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
lean_ctor_set(v___x_593_, 1, v_msgData_582_);
v___x_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0(v_msgData_595_, v___y_596_, v___y_597_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v_ref_604_; lean_object* v___x_605_; lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_614_; 
v_ref_604_ = lean_ctor_get(v___y_601_, 2);
v___x_605_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0(v_msg_600_, v___y_601_, v___y_602_);
v_a_606_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_614_ == 0)
{
v___x_608_ = v___x_605_;
v_isShared_609_ = v_isSharedCheck_614_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_605_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_614_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; lean_object* v___x_612_; 
lean_inc(v_ref_604_);
v___x_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_610_, 0, v_ref_604_);
lean_ctor_set(v___x_610_, 1, v_a_606_);
if (v_isShared_609_ == 0)
{
lean_ctor_set_tag(v___x_608_, 1);
lean_ctor_set(v___x_608_, 0, v___x_610_);
v___x_612_ = v___x_608_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_610_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0___redArg(v_msg_615_, v___y_616_, v___y_617_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
return v_res_619_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0___closed__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___x_622_ = l_Lean_stringToMessageData(v___x_621_);
return v___x_622_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0___closed__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___x_625_ = l_Lean_stringToMessageData(v___x_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(lean_object* v_name_626_, lean_object* v_decl_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_631_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_);
v___x_632_ = l_Lean_MessageData_ofName(v_name_626_);
v___x_633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_631_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
v___x_634_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_);
v___x_635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_633_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
v___x_636_ = l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0___redArg(v___x_635_, v___y_628_, v___y_629_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2____boxed(lean_object* v_name_637_, lean_object* v_decl_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(v_name_637_, v_decl_638_, v___y_639_, v___y_640_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v_decl_638_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__13___redArg(lean_object* v_ref_643_, lean_object* v_msg_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v_toCold_648_; lean_object* v_currRecDepth_649_; lean_object* v_ref_650_; uint8_t v_diag_651_; uint8_t v_suppressElabErrors_652_; lean_object* v_ref_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v_toCold_648_ = lean_ctor_get(v___y_645_, 0);
v_currRecDepth_649_ = lean_ctor_get(v___y_645_, 1);
v_ref_650_ = lean_ctor_get(v___y_645_, 2);
v_diag_651_ = lean_ctor_get_uint8(v___y_645_, sizeof(void*)*3);
v_suppressElabErrors_652_ = lean_ctor_get_uint8(v___y_645_, sizeof(void*)*3 + 1);
v_ref_653_ = l_Lean_replaceRef(v_ref_643_, v_ref_650_);
lean_inc(v_currRecDepth_649_);
lean_inc_ref(v_toCold_648_);
v___x_654_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_654_, 0, v_toCold_648_);
lean_ctor_set(v___x_654_, 1, v_currRecDepth_649_);
lean_ctor_set(v___x_654_, 2, v_ref_653_);
lean_ctor_set_uint8(v___x_654_, sizeof(void*)*3, v_diag_651_);
lean_ctor_set_uint8(v___x_654_, sizeof(void*)*3 + 1, v_suppressElabErrors_652_);
v___x_655_ = l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0___redArg(v_msg_644_, v___x_654_, v___y_646_);
lean_dec_ref_known(v___x_654_, 3);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__13___redArg___boxed(lean_object* v_ref_656_, lean_object* v_msg_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__13___redArg(v_ref_656_, v_msg_657_, v___y_658_, v___y_659_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v_ref_656_);
return v_res_661_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__0));
v___x_664_ = l_Lean_stringToMessageData(v___x_663_);
return v___x_664_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__2));
v___x_667_ = l_Lean_stringToMessageData(v___x_666_);
return v___x_667_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__5(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__4));
v___x_670_ = l_Lean_stringToMessageData(v___x_669_);
return v___x_670_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__7(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__6));
v___x_673_ = l_Lean_stringToMessageData(v___x_672_);
return v___x_673_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__9(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__8));
v___x_676_ = l_Lean_stringToMessageData(v___x_675_);
return v___x_676_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__11(void){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__10));
v___x_679_ = l_Lean_stringToMessageData(v___x_678_);
return v___x_679_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__13(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__12));
v___x_682_ = l_Lean_stringToMessageData(v___x_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg(lean_object* v_msg_683_, lean_object* v_declHint_684_, lean_object* v___y_685_){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v_env_689_; uint8_t v___x_690_; 
v___x_687_ = lean_box(0);
v___x_688_ = lean_st_ref_get(v___y_685_);
v_env_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc_ref(v_env_689_);
lean_dec(v___x_688_);
v___x_690_ = l_Lean_Name_isAnonymous(v_declHint_684_);
if (v___x_690_ == 0)
{
uint8_t v_isExporting_691_; 
v_isExporting_691_ = lean_ctor_get_uint8(v_env_689_, sizeof(void*)*8);
if (v_isExporting_691_ == 0)
{
lean_object* v___x_692_; 
lean_dec_ref(v_env_689_);
lean_dec(v_declHint_684_);
v___x_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_692_, 0, v_msg_683_);
return v___x_692_;
}
else
{
lean_object* v___x_693_; uint8_t v___x_694_; 
lean_inc_ref(v_env_689_);
v___x_693_ = l_Lean_Environment_setExporting(v_env_689_, v___x_690_);
lean_inc(v_declHint_684_);
lean_inc_ref(v___x_693_);
v___x_694_ = l_Lean_Environment_contains(v___x_693_, v_declHint_684_, v_isExporting_691_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; 
lean_dec_ref(v___x_693_);
lean_dec_ref(v_env_689_);
lean_dec(v_declHint_684_);
v___x_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_695_, 0, v_msg_683_);
return v___x_695_;
}
else
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v_c_701_; lean_object* v___x_702_; 
v___x_696_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_697_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_698_ = l_Lean_Options_empty;
v___x_699_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_699_, 0, v___x_693_);
lean_ctor_set(v___x_699_, 1, v___x_696_);
lean_ctor_set(v___x_699_, 2, v___x_697_);
lean_ctor_set(v___x_699_, 3, v___x_698_);
lean_inc(v_declHint_684_);
v___x_700_ = l_Lean_MessageData_ofConstName(v_declHint_684_, v___x_690_);
v_c_701_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_701_, 0, v___x_699_);
lean_ctor_set(v_c_701_, 1, v___x_700_);
v___x_702_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_689_, v_declHint_684_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
lean_dec_ref(v_env_689_);
lean_dec(v_declHint_684_);
v___x_703_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__1);
v___x_704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
lean_ctor_set(v___x_704_, 1, v_c_701_);
v___x_705_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__3);
v___x_706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_704_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
v___x_707_ = l_Lean_MessageData_note(v___x_706_);
v___x_708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_708_, 0, v_msg_683_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
v___x_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
return v___x_709_;
}
else
{
lean_object* v_val_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_744_; 
v_val_710_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_744_ == 0)
{
v___x_712_ = v___x_702_;
v_isShared_713_ = v_isSharedCheck_744_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_val_710_);
lean_dec(v___x_702_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_744_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v_mod_716_; uint8_t v___x_717_; 
v___x_714_ = l_Lean_Environment_header(v_env_689_);
lean_dec_ref(v_env_689_);
v___x_715_ = l_Lean_EnvironmentHeader_moduleNames(v___x_714_);
v_mod_716_ = lean_array_get(v___x_687_, v___x_715_, v_val_710_);
lean_dec(v_val_710_);
lean_dec_ref(v___x_715_);
v___x_717_ = l_Lean_isPrivateName(v_declHint_684_);
lean_dec(v_declHint_684_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_729_; 
v___x_718_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__5);
v___x_719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
lean_ctor_set(v___x_719_, 1, v_c_701_);
v___x_720_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__7);
v___x_721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_719_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
v___x_722_ = l_Lean_MessageData_ofName(v_mod_716_);
v___x_723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_721_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
v___x_724_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__9);
v___x_725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_723_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
v___x_726_ = l_Lean_MessageData_note(v___x_725_);
v___x_727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_727_, 0, v_msg_683_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
if (v_isShared_713_ == 0)
{
lean_ctor_set_tag(v___x_712_, 0);
lean_ctor_set(v___x_712_, 0, v___x_727_);
v___x_729_ = v___x_712_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_727_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
else
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_731_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__1);
v___x_732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
lean_ctor_set(v___x_732_, 1, v_c_701_);
v___x_733_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__11);
v___x_734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_732_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v___x_735_ = l_Lean_MessageData_ofName(v_mod_716_);
v___x_736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_734_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___closed__13);
v___x_738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_736_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
v___x_739_ = l_Lean_MessageData_note(v___x_738_);
v___x_740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_740_, 0, v_msg_683_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
if (v_isShared_713_ == 0)
{
lean_ctor_set_tag(v___x_712_, 0);
lean_ctor_set(v___x_712_, 0, v___x_740_);
v___x_742_ = v___x_712_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_745_; 
lean_dec_ref(v_env_689_);
lean_dec(v_declHint_684_);
v___x_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_745_, 0, v_msg_683_);
return v___x_745_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg___boxed(lean_object* v_msg_746_, lean_object* v_declHint_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg(v_msg_746_, v_declHint_747_, v___y_748_);
lean_dec(v___y_748_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12(lean_object* v_msg_751_, lean_object* v_declHint_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v___x_756_; lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_766_; 
v___x_756_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg(v_msg_751_, v_declHint_752_, v___y_754_);
v_a_757_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_766_ == 0)
{
v___x_759_ = v___x_756_;
v_isShared_760_ = v_isSharedCheck_766_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_756_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_766_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_764_; 
v___x_761_ = l_Lean_unknownIdentifierMessageTag;
v___x_762_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
lean_ctor_set(v___x_762_, 1, v_a_757_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 0, v___x_762_);
v___x_764_ = v___x_759_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_762_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12___boxed(lean_object* v_msg_767_, lean_object* v_declHint_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12(v_msg_767_, v_declHint_768_, v___y_769_, v___y_770_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8___redArg(lean_object* v_ref_773_, lean_object* v_msg_774_, lean_object* v_declHint_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v___x_779_; lean_object* v_a_780_; lean_object* v___x_781_; 
v___x_779_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12(v_msg_774_, v_declHint_775_, v___y_776_, v___y_777_);
v_a_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_a_780_);
lean_dec_ref(v___x_779_);
v___x_781_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__13___redArg(v_ref_773_, v_a_780_, v___y_776_, v___y_777_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_ref_782_, lean_object* v_msg_783_, lean_object* v_declHint_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8___redArg(v_ref_782_, v_msg_783_, v_declHint_784_, v___y_785_, v___y_786_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v_ref_782_);
return v_res_788_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__2));
v___x_790_ = l_Lean_stringToMessageData(v___x_789_);
return v___x_790_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__3));
v___x_792_ = l_Lean_stringToMessageData(v___x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(lean_object* v_ref_793_, lean_object* v_constName_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v___x_798_; uint8_t v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_798_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__0, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__0);
v___x_799_ = 0;
lean_inc(v_constName_794_);
v___x_800_ = l_Lean_MessageData_ofConstName(v_constName_794_, v___x_799_);
v___x_801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_798_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
v___x_802_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1);
v___x_803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_801_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
v___x_804_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8___redArg(v_ref_793_, v___x_803_, v_constName_794_, v___y_795_, v___y_796_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_805_, lean_object* v_constName_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_ref_805_, v_constName_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v_ref_805_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_constName_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v_ref_815_; lean_object* v___x_816_; 
v_ref_815_ = lean_ctor_get(v___y_812_, 2);
v___x_816_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_ref_815_, v_constName_811_, v___y_812_, v___y_813_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_constName_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2___redArg(v_constName_817_, v___y_818_, v___y_819_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1(lean_object* v_constName_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v___x_826_; lean_object* v_env_827_; uint8_t v___x_828_; lean_object* v___x_829_; 
v___x_826_ = lean_st_ref_get(v___y_824_);
v_env_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc_ref(v_env_827_);
lean_dec(v___x_826_);
v___x_828_ = 0;
lean_inc(v_constName_822_);
v___x_829_ = l_Lean_Environment_find_x3f(v_env_827_, v_constName_822_, v___x_828_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v___x_830_; 
v___x_830_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2___redArg(v_constName_822_, v___y_823_, v___y_824_);
return v___x_830_;
}
else
{
lean_object* v_val_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec(v_constName_822_);
v_val_831_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_829_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_val_831_);
lean_dec(v___x_829_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
lean_ctor_set_tag(v___x_833_, 0);
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_val_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1___boxed(lean_object* v_constName_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1(v_constName_839_, v___y_840_, v___y_841_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
return v_res_843_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__0));
v___x_846_ = l_Lean_stringToMessageData(v___x_845_);
return v___x_846_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__2));
v___x_849_ = l_Lean_stringToMessageData(v___x_848_);
return v___x_849_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__4));
v___x_852_ = l_Lean_stringToMessageData(v___x_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg(lean_object* v_attrName_853_, lean_object* v_declName_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; uint8_t v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_858_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__1);
v___x_859_ = l_Lean_MessageData_ofName(v_attrName_853_);
v___x_860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_858_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
v___x_861_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__3);
v___x_862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_860_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
v___x_863_ = 0;
v___x_864_ = l_Lean_MessageData_ofConstName(v_declName_854_, v___x_863_);
v___x_865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_862_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
v___x_866_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___closed__5);
v___x_867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_865_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0___redArg(v___x_867_, v___y_855_, v___y_856_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object* v_attrName_869_, lean_object* v_declName_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg(v_attrName_869_, v_declName_870_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
return v_res_874_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__0));
v___x_877_ = l_Lean_stringToMessageData(v___x_876_);
return v___x_877_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__2));
v___x_880_ = l_Lean_stringToMessageData(v___x_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg(lean_object* v_name_884_, uint8_t v_kind_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___y_895_; 
v___x_889_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__1);
v___x_890_ = l_Lean_MessageData_ofName(v_name_884_);
v___x_891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_889_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__3);
v___x_893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_891_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
switch(v_kind_885_)
{
case 0:
{
lean_object* v___x_902_; 
v___x_902_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__4));
v___y_895_ = v___x_902_;
goto v___jp_894_;
}
case 1:
{
lean_object* v___x_903_; 
v___x_903_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__5));
v___y_895_ = v___x_903_;
goto v___jp_894_;
}
default: 
{
lean_object* v___x_904_; 
v___x_904_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___closed__6));
v___y_895_ = v___x_904_;
goto v___jp_894_;
}
}
v___jp_894_:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
lean_inc_ref(v___y_895_);
v___x_896_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_896_, 0, v___y_895_);
v___x_897_ = l_Lean_MessageData_ofFormat(v___x_896_);
v___x_898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_893_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1);
v___x_900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_898_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0___redArg(v___x_900_, v___y_886_, v___y_887_);
return v___x_901_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg___boxed(lean_object* v_name_905_, lean_object* v_kind_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
uint8_t v_kind_boxed_910_; lean_object* v_res_911_; 
v_kind_boxed_910_ = lean_unbox(v_kind_906_);
v_res_911_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg(v_name_905_, v_kind_boxed_910_, v___y_907_, v___y_908_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
return v_res_911_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16___redArg(lean_object* v_keys_912_, lean_object* v_i_913_, lean_object* v_k_914_){
_start:
{
lean_object* v___x_915_; uint8_t v___x_916_; 
v___x_915_ = lean_array_get_size(v_keys_912_);
v___x_916_ = lean_nat_dec_lt(v_i_913_, v___x_915_);
if (v___x_916_ == 0)
{
lean_dec(v_i_913_);
return v___x_916_;
}
else
{
lean_object* v_k_x27_917_; uint8_t v___x_918_; 
v_k_x27_917_ = lean_array_fget_borrowed(v_keys_912_, v_i_913_);
v___x_918_ = l_Lean_instBEqExtraModUse_beq(v_k_914_, v_k_x27_917_);
if (v___x_918_ == 0)
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = lean_unsigned_to_nat(1u);
v___x_920_ = lean_nat_add(v_i_913_, v___x_919_);
lean_dec(v_i_913_);
v_i_913_ = v___x_920_;
goto _start;
}
else
{
lean_dec(v_i_913_);
return v___x_916_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16___redArg___boxed(lean_object* v_keys_922_, lean_object* v_i_923_, lean_object* v_k_924_){
_start:
{
uint8_t v_res_925_; lean_object* v_r_926_; 
v_res_925_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16___redArg(v_keys_922_, v_i_923_, v_k_924_);
lean_dec_ref(v_k_924_);
lean_dec_ref(v_keys_922_);
v_r_926_ = lean_box(v_res_925_);
return v_r_926_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg(lean_object* v_x_927_, size_t v_x_928_, lean_object* v_x_929_){
_start:
{
if (lean_obj_tag(v_x_927_) == 0)
{
lean_object* v_es_930_; lean_object* v___x_931_; size_t v___x_932_; size_t v___x_933_; lean_object* v_j_934_; lean_object* v___x_935_; 
v_es_930_ = lean_ctor_get(v_x_927_, 0);
v___x_931_ = lean_box(2);
v___x_932_ = ((size_t)31ULL);
v___x_933_ = lean_usize_land(v_x_928_, v___x_932_);
v_j_934_ = lean_usize_to_nat(v___x_933_);
v___x_935_ = lean_array_get_borrowed(v___x_931_, v_es_930_, v_j_934_);
lean_dec(v_j_934_);
switch(lean_obj_tag(v___x_935_))
{
case 0:
{
lean_object* v_key_936_; uint8_t v___x_937_; 
v_key_936_ = lean_ctor_get(v___x_935_, 0);
v___x_937_ = l_Lean_instBEqExtraModUse_beq(v_x_929_, v_key_936_);
return v___x_937_;
}
case 1:
{
lean_object* v_node_938_; size_t v___x_939_; size_t v___x_940_; 
v_node_938_ = lean_ctor_get(v___x_935_, 0);
v___x_939_ = ((size_t)5ULL);
v___x_940_ = lean_usize_shift_right(v_x_928_, v___x_939_);
v_x_927_ = v_node_938_;
v_x_928_ = v___x_940_;
goto _start;
}
default: 
{
uint8_t v___x_942_; 
v___x_942_ = 0;
return v___x_942_;
}
}
}
else
{
lean_object* v_ks_943_; lean_object* v___x_944_; uint8_t v___x_945_; 
v_ks_943_ = lean_ctor_get(v_x_927_, 0);
v___x_944_ = lean_unsigned_to_nat(0u);
v___x_945_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16___redArg(v_ks_943_, v___x_944_, v_x_929_);
return v___x_945_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg___boxed(lean_object* v_x_946_, lean_object* v_x_947_, lean_object* v_x_948_){
_start:
{
size_t v_x_8797__boxed_949_; uint8_t v_res_950_; lean_object* v_r_951_; 
v_x_8797__boxed_949_ = lean_unbox_usize(v_x_947_);
lean_dec(v_x_947_);
v_res_950_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg(v_x_946_, v_x_8797__boxed_949_, v_x_948_);
lean_dec_ref(v_x_948_);
lean_dec_ref(v_x_946_);
v_r_951_ = lean_box(v_res_950_);
return v_r_951_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(lean_object* v_x_952_, lean_object* v_x_953_){
_start:
{
uint64_t v___x_954_; size_t v___x_955_; uint8_t v___x_956_; 
v___x_954_ = l_Lean_instHashableExtraModUse_hash(v_x_953_);
v___x_955_ = lean_uint64_to_usize(v___x_954_);
v___x_956_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg(v_x_952_, v___x_955_, v_x_953_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_x_957_, lean_object* v_x_958_){
_start:
{
uint8_t v_res_959_; lean_object* v_r_960_; 
v_res_959_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(v_x_957_, v_x_958_);
lean_dec_ref(v_x_958_);
lean_dec_ref(v_x_957_);
v_r_960_ = lean_box(v_res_959_);
return v_r_960_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__0(void){
_start:
{
lean_object* v___x_961_; double v___x_962_; 
v___x_961_ = lean_unsigned_to_nat(0u);
v___x_962_ = lean_float_of_nat(v___x_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8(lean_object* v_cls_966_, lean_object* v_msg_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v_ref_971_; lean_object* v___x_972_; lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_1017_; 
v_ref_971_ = lean_ctor_get(v___y_968_, 2);
v___x_972_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0(v_msg_967_, v___y_968_, v___y_969_);
v_a_973_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_975_ = v___x_972_;
v_isShared_976_ = v_isSharedCheck_1017_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_1017_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_977_; lean_object* v_traceState_978_; lean_object* v_env_979_; lean_object* v_nextMacroScope_980_; lean_object* v_ngen_981_; lean_object* v_auxDeclNGen_982_; lean_object* v_cache_983_; lean_object* v_messages_984_; lean_object* v_infoState_985_; lean_object* v_snapshotTasks_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1016_; 
v___x_977_ = lean_st_ref_take(v___y_969_);
v_traceState_978_ = lean_ctor_get(v___x_977_, 4);
v_env_979_ = lean_ctor_get(v___x_977_, 0);
v_nextMacroScope_980_ = lean_ctor_get(v___x_977_, 1);
v_ngen_981_ = lean_ctor_get(v___x_977_, 2);
v_auxDeclNGen_982_ = lean_ctor_get(v___x_977_, 3);
v_cache_983_ = lean_ctor_get(v___x_977_, 5);
v_messages_984_ = lean_ctor_get(v___x_977_, 6);
v_infoState_985_ = lean_ctor_get(v___x_977_, 7);
v_snapshotTasks_986_ = lean_ctor_get(v___x_977_, 8);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_988_ = v___x_977_;
v_isShared_989_ = v_isSharedCheck_1016_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_snapshotTasks_986_);
lean_inc(v_infoState_985_);
lean_inc(v_messages_984_);
lean_inc(v_cache_983_);
lean_inc(v_traceState_978_);
lean_inc(v_auxDeclNGen_982_);
lean_inc(v_ngen_981_);
lean_inc(v_nextMacroScope_980_);
lean_inc(v_env_979_);
lean_dec(v___x_977_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1016_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
uint64_t v_tid_990_; lean_object* v_traces_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1015_; 
v_tid_990_ = lean_ctor_get_uint64(v_traceState_978_, sizeof(void*)*1);
v_traces_991_ = lean_ctor_get(v_traceState_978_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v_traceState_978_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_993_ = v_traceState_978_;
v_isShared_994_ = v_isSharedCheck_1015_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_traces_991_);
lean_dec(v_traceState_978_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1015_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; lean_object* v___x_996_; double v___x_997_; uint8_t v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1006_; 
v___x_995_ = lean_box(0);
v___x_996_ = lean_box(0);
v___x_997_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__0);
v___x_998_ = 0;
v___x_999_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__1));
v___x_1000_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1000_, 0, v_cls_966_);
lean_ctor_set(v___x_1000_, 1, v___x_996_);
lean_ctor_set(v___x_1000_, 2, v___x_999_);
lean_ctor_set_float(v___x_1000_, sizeof(void*)*3, v___x_997_);
lean_ctor_set_float(v___x_1000_, sizeof(void*)*3 + 8, v___x_997_);
lean_ctor_set_uint8(v___x_1000_, sizeof(void*)*3 + 16, v___x_998_);
v___x_1001_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__2));
v___x_1002_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1000_);
lean_ctor_set(v___x_1002_, 1, v_a_973_);
lean_ctor_set(v___x_1002_, 2, v___x_1001_);
lean_inc(v_ref_971_);
v___x_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1003_, 0, v_ref_971_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = l_Lean_PersistentArray_push___redArg(v_traces_991_, v___x_1003_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 0, v___x_1004_);
v___x_1006_ = v___x_993_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v___x_1004_);
lean_ctor_set_uint64(v_reuseFailAlloc_1014_, sizeof(void*)*1, v_tid_990_);
v___x_1006_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
lean_object* v___x_1008_; 
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 4, v___x_1006_);
v___x_1008_ = v___x_988_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_env_979_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_nextMacroScope_980_);
lean_ctor_set(v_reuseFailAlloc_1013_, 2, v_ngen_981_);
lean_ctor_set(v_reuseFailAlloc_1013_, 3, v_auxDeclNGen_982_);
lean_ctor_set(v_reuseFailAlloc_1013_, 4, v___x_1006_);
lean_ctor_set(v_reuseFailAlloc_1013_, 5, v_cache_983_);
lean_ctor_set(v_reuseFailAlloc_1013_, 6, v_messages_984_);
lean_ctor_set(v_reuseFailAlloc_1013_, 7, v_infoState_985_);
lean_ctor_set(v_reuseFailAlloc_1013_, 8, v_snapshotTasks_986_);
v___x_1008_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
lean_object* v___x_1009_; lean_object* v___x_1011_; 
v___x_1009_ = lean_st_ref_put(v___y_969_, v___x_1008_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_995_);
v___x_1011_ = v___x_975_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_995_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___boxed(lean_object* v_cls_1018_, lean_object* v_msg_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8(v_cls_1018_, v_msg_1019_, v___y_1020_, v___y_1021_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
return v_res_1023_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1024_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__4(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__3));
v___x_1030_ = l_Lean_stringToMessageData(v___x_1029_);
return v___x_1030_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__6(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__5));
v___x_1033_ = l_Lean_stringToMessageData(v___x_1032_);
return v___x_1033_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__7(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__1));
v___x_1035_ = l_Lean_stringToMessageData(v___x_1034_);
return v___x_1035_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__10(void){
_start:
{
lean_object* v_cls_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v_cls_1039_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__2));
v___x_1040_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__9));
v___x_1041_ = l_Lean_Name_append(v___x_1040_, v_cls_1039_);
return v___x_1041_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__12(void){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__11));
v___x_1044_ = l_Lean_stringToMessageData(v___x_1043_);
return v___x_1044_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__14(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__13));
v___x_1047_ = l_Lean_stringToMessageData(v___x_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5(lean_object* v_mod_1052_, uint8_t v_isMeta_1053_, lean_object* v_hint_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v_env_1060_; uint8_t v_isExporting_1061_; lean_object* v_entry_1062_; lean_object* v___x_1063_; lean_object* v_env_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___y_1069_; lean_object* v___x_1094_; uint8_t v___x_1095_; 
v___x_1058_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__0);
v___x_1059_ = lean_st_ref_get(v___y_1056_);
v_env_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc_ref(v_env_1060_);
lean_dec(v___x_1059_);
v_isExporting_1061_ = lean_ctor_get_uint8(v_env_1060_, sizeof(void*)*8);
lean_dec_ref(v_env_1060_);
lean_inc(v_mod_1052_);
v_entry_1062_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_1062_, 0, v_mod_1052_);
lean_ctor_set_uint8(v_entry_1062_, sizeof(void*)*1, v_isExporting_1061_);
lean_ctor_set_uint8(v_entry_1062_, sizeof(void*)*1 + 1, v_isMeta_1053_);
v___x_1063_ = lean_st_ref_get(v___y_1056_);
v_env_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc_ref(v_env_1064_);
lean_dec(v___x_1063_);
v___x_1065_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_1066_ = lean_box(1);
v___x_1067_ = lean_box(0);
v___x_1094_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1058_, v___x_1065_, v_env_1064_, v___x_1066_, v___x_1067_);
v___x_1095_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(v___x_1094_, v_entry_1062_);
lean_dec(v___x_1094_);
if (v___x_1095_ == 0)
{
lean_object* v_toCold_1096_; lean_object* v_options_1097_; uint8_t v_hasTrace_1098_; 
v_toCold_1096_ = lean_ctor_get(v___y_1055_, 0);
v_options_1097_ = lean_ctor_get(v_toCold_1096_, 2);
v_hasTrace_1098_ = lean_ctor_get_uint8(v_options_1097_, sizeof(void*)*1);
if (v_hasTrace_1098_ == 0)
{
lean_dec(v_hint_1054_);
lean_dec(v_mod_1052_);
v___y_1069_ = v___y_1056_;
goto v___jp_1068_;
}
else
{
lean_object* v_inheritedTraceOptions_1099_; lean_object* v_cls_1100_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___x_1120_; uint8_t v___x_1121_; 
v_inheritedTraceOptions_1099_ = lean_ctor_get(v_toCold_1096_, 11);
v_cls_1100_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__2));
v___x_1120_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__10);
v___x_1121_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1099_, v_options_1097_, v___x_1120_);
if (v___x_1121_ == 0)
{
lean_dec(v_hint_1054_);
lean_dec(v_mod_1052_);
v___y_1069_ = v___y_1056_;
goto v___jp_1068_;
}
else
{
lean_object* v___x_1122_; lean_object* v___y_1124_; 
v___x_1122_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__12);
if (v_isExporting_1061_ == 0)
{
lean_object* v___x_1131_; 
v___x_1131_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__17));
v___y_1124_ = v___x_1131_;
goto v___jp_1123_;
}
else
{
lean_object* v___x_1132_; 
v___x_1132_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__18));
v___y_1124_ = v___x_1132_;
goto v___jp_1123_;
}
v___jp_1123_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
lean_inc_ref(v___y_1124_);
v___x_1125_ = l_Lean_stringToMessageData(v___y_1124_);
v___x_1126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1122_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
v___x_1127_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__14);
v___x_1128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1126_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
if (v_isMeta_1053_ == 0)
{
lean_object* v___x_1129_; 
v___x_1129_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__15));
v___y_1107_ = v___x_1128_;
v___y_1108_ = v___x_1129_;
goto v___jp_1106_;
}
else
{
lean_object* v___x_1130_; 
v___x_1130_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__16));
v___y_1107_ = v___x_1128_;
v___y_1108_ = v___x_1130_;
goto v___jp_1106_;
}
}
}
v___jp_1101_:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___y_1102_);
lean_ctor_set(v___x_1104_, 1, v___y_1103_);
v___x_1105_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8(v_cls_1100_, v___x_1104_, v___y_1055_, v___y_1056_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_dec_ref_known(v___x_1105_, 1);
v___y_1069_ = v___y_1056_;
goto v___jp_1068_;
}
else
{
lean_dec_ref_known(v_entry_1062_, 1);
return v___x_1105_;
}
}
v___jp_1106_:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; 
lean_inc_ref(v___y_1108_);
v___x_1109_ = l_Lean_stringToMessageData(v___y_1108_);
v___x_1110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___y_1107_);
lean_ctor_set(v___x_1110_, 1, v___x_1109_);
v___x_1111_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__4);
v___x_1112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1110_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
v___x_1113_ = l_Lean_MessageData_ofName(v_mod_1052_);
v___x_1114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1112_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
v___x_1115_ = l_Lean_Name_isAnonymous(v_hint_1054_);
if (v___x_1115_ == 0)
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1116_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__6);
v___x_1117_ = l_Lean_MessageData_ofName(v_hint_1054_);
v___x_1118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1116_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___y_1102_ = v___x_1114_;
v___y_1103_ = v___x_1118_;
goto v___jp_1101_;
}
else
{
lean_object* v___x_1119_; 
lean_dec(v_hint_1054_);
v___x_1119_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__7);
v___y_1102_ = v___x_1114_;
v___y_1103_ = v___x_1119_;
goto v___jp_1101_;
}
}
}
}
else
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_dec_ref_known(v_entry_1062_, 1);
lean_dec(v_hint_1054_);
lean_dec(v_mod_1052_);
v___x_1133_ = lean_box(0);
v___x_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
return v___x_1134_;
}
v___jp_1068_:
{
lean_object* v___x_1070_; lean_object* v_toEnvExtension_1071_; lean_object* v_env_1072_; lean_object* v_nextMacroScope_1073_; lean_object* v_ngen_1074_; lean_object* v_auxDeclNGen_1075_; lean_object* v_traceState_1076_; lean_object* v_messages_1077_; lean_object* v_infoState_1078_; lean_object* v_snapshotTasks_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1092_; 
v___x_1070_ = lean_st_ref_take(v___y_1069_);
v_toEnvExtension_1071_ = lean_ctor_get(v___x_1065_, 0);
v_env_1072_ = lean_ctor_get(v___x_1070_, 0);
v_nextMacroScope_1073_ = lean_ctor_get(v___x_1070_, 1);
v_ngen_1074_ = lean_ctor_get(v___x_1070_, 2);
v_auxDeclNGen_1075_ = lean_ctor_get(v___x_1070_, 3);
v_traceState_1076_ = lean_ctor_get(v___x_1070_, 4);
v_messages_1077_ = lean_ctor_get(v___x_1070_, 6);
v_infoState_1078_ = lean_ctor_get(v___x_1070_, 7);
v_snapshotTasks_1079_ = lean_ctor_get(v___x_1070_, 8);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1092_ == 0)
{
lean_object* v_unused_1093_; 
v_unused_1093_ = lean_ctor_get(v___x_1070_, 5);
lean_dec(v_unused_1093_);
v___x_1081_ = v___x_1070_;
v_isShared_1082_ = v_isSharedCheck_1092_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_snapshotTasks_1079_);
lean_inc(v_infoState_1078_);
lean_inc(v_messages_1077_);
lean_inc(v_traceState_1076_);
lean_inc(v_auxDeclNGen_1075_);
lean_inc(v_ngen_1074_);
lean_inc(v_nextMacroScope_1073_);
lean_inc(v_env_1072_);
lean_dec(v___x_1070_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1092_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v_asyncMode_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1088_; 
v_asyncMode_1083_ = lean_ctor_get(v_toEnvExtension_1071_, 2);
v___x_1084_ = lean_box(0);
v___x_1085_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1065_, v_env_1072_, v_entry_1062_, v_asyncMode_1083_, v___x_1067_);
v___x_1086_ = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg___closed__2);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 5, v___x_1086_);
lean_ctor_set(v___x_1081_, 0, v___x_1085_);
v___x_1088_ = v___x_1081_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v_nextMacroScope_1073_);
lean_ctor_set(v_reuseFailAlloc_1091_, 2, v_ngen_1074_);
lean_ctor_set(v_reuseFailAlloc_1091_, 3, v_auxDeclNGen_1075_);
lean_ctor_set(v_reuseFailAlloc_1091_, 4, v_traceState_1076_);
lean_ctor_set(v_reuseFailAlloc_1091_, 5, v___x_1086_);
lean_ctor_set(v_reuseFailAlloc_1091_, 6, v_messages_1077_);
lean_ctor_set(v_reuseFailAlloc_1091_, 7, v_infoState_1078_);
lean_ctor_set(v_reuseFailAlloc_1091_, 8, v_snapshotTasks_1079_);
v___x_1088_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_st_ref_put(v___y_1069_, v___x_1088_);
v___x_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1084_);
return v___x_1090_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___boxed(lean_object* v_mod_1135_, lean_object* v_isMeta_1136_, lean_object* v_hint_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
uint8_t v_isMeta_boxed_1141_; lean_object* v_res_1142_; 
v_isMeta_boxed_1141_ = lean_unbox(v_isMeta_1136_);
v_res_1142_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5(v_mod_1135_, v_isMeta_boxed_1141_, v_hint_1137_, v___y_1138_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__6(lean_object* v___x_1143_, lean_object* v_declName_1144_, lean_object* v_as_1145_, size_t v_sz_1146_, size_t v_i_1147_, lean_object* v_b_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
uint8_t v___x_1152_; 
v___x_1152_ = lean_usize_dec_lt(v_i_1147_, v_sz_1146_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; 
lean_dec(v_declName_1144_);
v___x_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1153_, 0, v_b_1148_);
return v___x_1153_;
}
else
{
lean_object* v___x_1154_; lean_object* v_modules_1155_; lean_object* v___x_1156_; lean_object* v_a_1157_; lean_object* v___x_1158_; lean_object* v_toImport_1159_; lean_object* v_module_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; lean_object* v___x_1163_; 
v___x_1154_ = l_Lean_Environment_header(v___x_1143_);
v_modules_1155_ = lean_ctor_get(v___x_1154_, 3);
lean_inc_ref(v_modules_1155_);
lean_dec_ref(v___x_1154_);
v___x_1156_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_1157_ = lean_array_uget_borrowed(v_as_1145_, v_i_1147_);
v___x_1158_ = lean_array_get(v___x_1156_, v_modules_1155_, v_a_1157_);
lean_dec_ref(v_modules_1155_);
v_toImport_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc_ref(v_toImport_1159_);
lean_dec(v___x_1158_);
v_module_1160_ = lean_ctor_get(v_toImport_1159_, 0);
lean_inc(v_module_1160_);
lean_dec_ref(v_toImport_1159_);
v___x_1161_ = lean_box(0);
v___x_1162_ = 0;
lean_inc(v_declName_1144_);
v___x_1163_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5(v_module_1160_, v___x_1162_, v_declName_1144_, v___y_1149_, v___y_1150_);
if (lean_obj_tag(v___x_1163_) == 0)
{
size_t v___x_1164_; size_t v___x_1165_; 
lean_dec_ref_known(v___x_1163_, 1);
v___x_1164_ = ((size_t)1ULL);
v___x_1165_ = lean_usize_add(v_i_1147_, v___x_1164_);
v_i_1147_ = v___x_1165_;
v_b_1148_ = v___x_1161_;
goto _start;
}
else
{
lean_dec(v_declName_1144_);
return v___x_1163_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__6___boxed(lean_object* v___x_1167_, lean_object* v_declName_1168_, lean_object* v_as_1169_, lean_object* v_sz_1170_, lean_object* v_i_1171_, lean_object* v_b_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
size_t v_sz_boxed_1176_; size_t v_i_boxed_1177_; lean_object* v_res_1178_; 
v_sz_boxed_1176_ = lean_unbox_usize(v_sz_1170_);
lean_dec(v_sz_1170_);
v_i_boxed_1177_ = lean_unbox_usize(v_i_1171_);
lean_dec(v_i_1171_);
v_res_1178_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__6(v___x_1167_, v_declName_1168_, v_as_1169_, v_sz_boxed_1176_, v_i_boxed_1177_, v_b_1172_, v___y_1173_, v___y_1174_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec_ref(v_as_1169_);
lean_dec_ref(v___x_1167_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11___redArg(lean_object* v_a_1179_, lean_object* v_x_1180_){
_start:
{
if (lean_obj_tag(v_x_1180_) == 0)
{
lean_object* v___x_1181_; 
v___x_1181_ = lean_box(0);
return v___x_1181_;
}
else
{
lean_object* v_key_1182_; lean_object* v_value_1183_; lean_object* v_tail_1184_; uint8_t v___x_1185_; 
v_key_1182_ = lean_ctor_get(v_x_1180_, 0);
v_value_1183_ = lean_ctor_get(v_x_1180_, 1);
v_tail_1184_ = lean_ctor_get(v_x_1180_, 2);
v___x_1185_ = lean_name_eq(v_key_1182_, v_a_1179_);
if (v___x_1185_ == 0)
{
v_x_1180_ = v_tail_1184_;
goto _start;
}
else
{
lean_object* v___x_1187_; 
lean_inc(v_value_1183_);
v___x_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1187_, 0, v_value_1183_);
return v___x_1187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11___redArg___boxed(lean_object* v_a_1188_, lean_object* v_x_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11___redArg(v_a_1188_, v_x_1189_);
lean_dec(v_x_1189_);
lean_dec(v_a_1188_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___redArg(lean_object* v_m_1191_, lean_object* v_a_1192_){
_start:
{
lean_object* v_buckets_1193_; lean_object* v___x_1194_; uint64_t v___y_1196_; 
v_buckets_1193_ = lean_ctor_get(v_m_1191_, 1);
v___x_1194_ = lean_array_get_size(v_buckets_1193_);
if (lean_obj_tag(v_a_1192_) == 0)
{
uint64_t v___x_1210_; 
v___x_1210_ = 1723ULL;
v___y_1196_ = v___x_1210_;
goto v___jp_1195_;
}
else
{
uint64_t v_hash_1211_; 
v_hash_1211_ = lean_ctor_get_uint64(v_a_1192_, sizeof(void*)*2);
v___y_1196_ = v_hash_1211_;
goto v___jp_1195_;
}
v___jp_1195_:
{
uint64_t v___x_1197_; uint64_t v___x_1198_; uint64_t v_fold_1199_; uint64_t v___x_1200_; uint64_t v___x_1201_; uint64_t v___x_1202_; size_t v___x_1203_; size_t v___x_1204_; size_t v___x_1205_; size_t v___x_1206_; size_t v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1197_ = 32ULL;
v___x_1198_ = lean_uint64_shift_right(v___y_1196_, v___x_1197_);
v_fold_1199_ = lean_uint64_xor(v___y_1196_, v___x_1198_);
v___x_1200_ = 16ULL;
v___x_1201_ = lean_uint64_shift_right(v_fold_1199_, v___x_1200_);
v___x_1202_ = lean_uint64_xor(v_fold_1199_, v___x_1201_);
v___x_1203_ = lean_uint64_to_usize(v___x_1202_);
v___x_1204_ = lean_usize_of_nat(v___x_1194_);
v___x_1205_ = ((size_t)1ULL);
v___x_1206_ = lean_usize_sub(v___x_1204_, v___x_1205_);
v___x_1207_ = lean_usize_land(v___x_1203_, v___x_1206_);
v___x_1208_ = lean_array_uget_borrowed(v_buckets_1193_, v___x_1207_);
v___x_1209_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11___redArg(v_a_1192_, v___x_1208_);
return v___x_1209_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___redArg___boxed(lean_object* v_m_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___redArg(v_m_1212_, v_a_1213_);
lean_dec(v_a_1213_);
lean_dec_ref(v_m_1212_);
return v_res_1214_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__0(void){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Std_HashMap_instInhabited___redArg();
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3(lean_object* v_declName_1218_, uint8_t v_isMeta_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v_env_1228_; lean_object* v___y_1230_; lean_object* v___x_1243_; 
v___x_1223_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__0);
v___x_1224_ = lean_st_ref_get(v___y_1221_);
v_env_1228_ = lean_ctor_get(v___x_1224_, 0);
lean_inc_ref(v_env_1228_);
lean_dec(v___x_1224_);
v___x_1243_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1228_, v_declName_1218_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_dec_ref(v_env_1228_);
lean_dec(v_declName_1218_);
goto v___jp_1225_;
}
else
{
lean_object* v_val_1244_; lean_object* v___x_1245_; lean_object* v_modules_1246_; lean_object* v___x_1247_; uint8_t v___x_1248_; 
v_val_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_val_1244_);
lean_dec_ref_known(v___x_1243_, 1);
v___x_1245_ = l_Lean_Environment_header(v_env_1228_);
v_modules_1246_ = lean_ctor_get(v___x_1245_, 3);
lean_inc_ref(v_modules_1246_);
lean_dec_ref(v___x_1245_);
v___x_1247_ = lean_array_get_size(v_modules_1246_);
v___x_1248_ = lean_nat_dec_lt(v_val_1244_, v___x_1247_);
if (v___x_1248_ == 0)
{
lean_dec_ref(v_modules_1246_);
lean_dec(v_val_1244_);
lean_dec_ref(v_env_1228_);
lean_dec(v_declName_1218_);
goto v___jp_1225_;
}
else
{
lean_object* v___x_1249_; lean_object* v___x_1250_; uint8_t v___y_1252_; 
v___x_1249_ = lean_array_fget(v_modules_1246_, v_val_1244_);
lean_dec(v_val_1244_);
lean_dec_ref(v_modules_1246_);
v___x_1250_ = lean_st_ref_get(v___y_1221_);
if (v_isMeta_1219_ == 0)
{
lean_dec(v___x_1250_);
v___y_1252_ = v_isMeta_1219_;
goto v___jp_1251_;
}
else
{
lean_object* v_env_1263_; uint8_t v___x_1264_; 
v_env_1263_ = lean_ctor_get(v___x_1250_, 0);
lean_inc_ref(v_env_1263_);
lean_dec(v___x_1250_);
lean_inc(v_declName_1218_);
v___x_1264_ = l_Lean_isMarkedMeta(v_env_1263_, v_declName_1218_);
if (v___x_1264_ == 0)
{
v___y_1252_ = v_isMeta_1219_;
goto v___jp_1251_;
}
else
{
uint8_t v___x_1265_; 
v___x_1265_ = 0;
v___y_1252_ = v___x_1265_;
goto v___jp_1251_;
}
}
v___jp_1251_:
{
lean_object* v_toImport_1253_; lean_object* v_module_1254_; lean_object* v___x_1255_; 
v_toImport_1253_ = lean_ctor_get(v___x_1249_, 0);
lean_inc_ref(v_toImport_1253_);
lean_dec(v___x_1249_);
v_module_1254_ = lean_ctor_get(v_toImport_1253_, 0);
lean_inc(v_module_1254_);
lean_dec_ref(v_toImport_1253_);
lean_inc(v_declName_1218_);
v___x_1255_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5(v_module_1254_, v___y_1252_, v_declName_1218_, v___y_1220_, v___y_1221_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_dec_ref_known(v___x_1255_, 1);
v___x_1256_ = l_Lean_indirectModUseExt;
v___x_1257_ = lean_box(1);
v___x_1258_ = lean_box(0);
lean_inc_ref(v_env_1228_);
v___x_1259_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1223_, v___x_1256_, v_env_1228_, v___x_1257_, v___x_1258_);
v___x_1260_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___redArg(v___x_1259_, v_declName_1218_);
lean_dec(v___x_1259_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v___x_1261_; 
v___x_1261_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___closed__1));
v___y_1230_ = v___x_1261_;
goto v___jp_1229_;
}
else
{
lean_object* v_val_1262_; 
v_val_1262_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_val_1262_);
lean_dec_ref_known(v___x_1260_, 1);
v___y_1230_ = v_val_1262_;
goto v___jp_1229_;
}
}
else
{
lean_dec_ref(v_env_1228_);
lean_dec(v_declName_1218_);
return v___x_1255_;
}
}
}
}
v___jp_1225_:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = lean_box(0);
v___x_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
return v___x_1227_;
}
v___jp_1229_:
{
lean_object* v___x_1231_; size_t v_sz_1232_; size_t v___x_1233_; lean_object* v___x_1234_; 
v___x_1231_ = lean_box(0);
v_sz_1232_ = lean_array_size(v___y_1230_);
v___x_1233_ = ((size_t)0ULL);
v___x_1234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__6(v_env_1228_, v_declName_1218_, v___y_1230_, v_sz_1232_, v___x_1233_, v___x_1231_, v___y_1220_, v___y_1221_);
lean_dec_ref(v___y_1230_);
lean_dec_ref(v_env_1228_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1241_ == 0)
{
lean_object* v_unused_1242_; 
v_unused_1242_ = lean_ctor_get(v___x_1234_, 0);
lean_dec(v_unused_1242_);
v___x_1236_ = v___x_1234_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_dec(v___x_1234_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 0, v___x_1231_);
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1231_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
else
{
return v___x_1234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3___boxed(lean_object* v_declName_1266_, lean_object* v_isMeta_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
uint8_t v_isMeta_boxed_1271_; lean_object* v_res_1272_; 
v_isMeta_boxed_1271_ = lean_unbox(v_isMeta_1267_);
v_res_1272_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3(v_declName_1266_, v_isMeta_boxed_1271_, v___y_1268_, v___y_1269_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
return v_res_1272_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___x_1277_ = l_Lean_stringToMessageData(v___x_1276_);
return v___x_1277_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__5_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__4_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___x_1280_ = l_Lean_stringToMessageData(v___x_1279_);
return v___x_1280_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__7_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__6_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___x_1283_ = l_Lean_stringToMessageData(v___x_1282_);
return v___x_1283_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__9_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__8_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___x_1286_ = l_Lean_stringToMessageData(v___x_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(lean_object* v___x_1287_, lean_object* v___x_1288_, lean_object* v___x_1289_, uint8_t v_builtin_1290_, lean_object* v___x_1291_, lean_object* v_name_1292_, lean_object* v_declName_1293_, lean_object* v_stx_1294_, uint8_t v_kind_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
lean_object* v___y_1300_; lean_object* v___y_1301_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; uint8_t v___y_1361_; lean_object* v___y_1362_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1434_; lean_object* v___y_1435_; uint8_t v___x_1443_; uint8_t v___x_1444_; 
v___x_1443_ = 0;
v___x_1444_ = l_Lean_instBEqAttributeKind_beq(v_kind_1295_, v___x_1443_);
if (v___x_1444_ == 0)
{
lean_object* v___x_1445_; 
lean_dec(v_stx_1294_);
lean_dec(v_declName_1293_);
lean_dec(v___x_1291_);
lean_dec_ref(v___x_1289_);
lean_dec_ref(v___x_1288_);
lean_dec_ref(v___x_1287_);
v___x_1445_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg(v_name_1292_, v_kind_1295_, v___y_1296_, v___y_1297_);
return v___x_1445_;
}
else
{
goto v___jp_1441_;
}
v___jp_1299_:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1305_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___x_1306_ = l_Lean_Name_mkStr4(v___x_1287_, v___x_1288_, v___x_1289_, v___x_1305_);
v___x_1307_ = l_Lean_mkConst(v___x_1306_, v___y_1303_);
v___x_1308_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v___y_1302_);
v___x_1309_ = l_Lean_mkAppB(v___x_1307_, v___x_1308_, v___y_1304_);
v___x_1310_ = l_Lean_declareBuiltin(v_declName_1293_, v___x_1309_, v___y_1300_, v___y_1301_);
return v___x_1310_;
}
v___jp_1311_:
{
if (v_builtin_1290_ == 0)
{
lean_object* v___x_1317_; lean_object* v_toCold_1318_; lean_object* v_env_1319_; lean_object* v_ref_1320_; lean_object* v_options_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
lean_dec_ref(v___y_1313_);
lean_dec_ref(v___x_1289_);
lean_dec_ref(v___x_1288_);
lean_dec_ref(v___x_1287_);
v___x_1317_ = lean_st_ref_get(v___y_1316_);
v_toCold_1318_ = lean_ctor_get(v___y_1315_, 0);
v_env_1319_ = lean_ctor_get(v___x_1317_, 0);
lean_inc_ref(v_env_1319_);
lean_dec(v___x_1317_);
v_ref_1320_ = lean_ctor_get(v___y_1315_, 2);
v_options_1321_ = lean_ctor_get(v_toCold_1318_, 2);
lean_inc_ref(v_options_1321_);
v___x_1322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1322_, 0, v_env_1319_);
lean_ctor_set(v___x_1322_, 1, v_options_1321_);
lean_inc(v_declName_1293_);
v___x_1323_ = l_Lean_Linter_MissingDocs_mkHandlerUnsafe(v_declName_1293_, v___x_1322_);
lean_dec_ref_known(v___x_1322_, 2);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v_a_1324_; lean_object* v___x_1325_; lean_object* v_toEnvExtension_1326_; lean_object* v_asyncMode_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_a_1324_);
lean_dec_ref_known(v___x_1323_, 1);
v___x_1325_ = l_Lean_Linter_MissingDocs_missingDocsExt;
v_toEnvExtension_1326_ = lean_ctor_get(v___x_1325_, 0);
v_asyncMode_1327_ = lean_ctor_get(v_toEnvExtension_1326_, 2);
v___x_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___y_1314_);
lean_ctor_set(v___x_1328_, 1, v_a_1324_);
v___x_1329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1329_, 0, v_declName_1293_);
lean_ctor_set(v___x_1329_, 1, v___x_1328_);
v___x_1330_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1325_, v___y_1312_, v___x_1329_, v_asyncMode_1327_, v___x_1291_);
v___x_1331_ = l_Lean_setEnv___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__2___redArg(v___x_1330_, v___y_1316_);
return v___x_1331_;
}
else
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1343_; 
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1312_);
lean_dec(v_declName_1293_);
lean_dec(v___x_1291_);
v_a_1332_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1334_ = v___x_1323_;
v_isShared_1335_ = v_isSharedCheck_1343_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1323_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1343_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1341_; 
v___x_1336_ = lean_io_error_to_string(v_a_1332_);
v___x_1337_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
v___x_1338_ = l_Lean_MessageData_ofFormat(v___x_1337_);
lean_inc(v_ref_1320_);
v___x_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1339_, 0, v_ref_1320_);
lean_ctor_set(v___x_1339_, 1, v___x_1338_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v___x_1339_);
v___x_1341_ = v___x_1334_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1339_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
else
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; 
lean_dec_ref(v___y_1312_);
lean_dec(v___x_1291_);
v___x_1344_ = l_Lean_ConstantInfo_type(v___y_1313_);
lean_dec_ref(v___y_1313_);
v___x_1345_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__5));
lean_inc_ref(v___x_1289_);
lean_inc_ref(v___x_1288_);
lean_inc_ref(v___x_1287_);
v___x_1346_ = l_Lean_Name_mkStr4(v___x_1287_, v___x_1288_, v___x_1289_, v___x_1345_);
v___x_1347_ = lean_box(0);
v___x_1348_ = l_Lean_Expr_const___override(v___x_1346_, v___x_1347_);
v___x_1349_ = lean_expr_eqv(v___x_1344_, v___x_1348_);
lean_dec_ref(v___x_1348_);
lean_dec_ref(v___x_1344_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; 
lean_inc(v_declName_1293_);
v___x_1350_ = l_Lean_mkConst(v_declName_1293_, v___x_1347_);
v___y_1300_ = v___y_1315_;
v___y_1301_ = v___y_1316_;
v___y_1302_ = v___y_1314_;
v___y_1303_ = v___x_1347_;
v___y_1304_ = v___x_1350_;
goto v___jp_1299_;
}
else
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1351_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
lean_inc_ref(v___x_1289_);
lean_inc_ref(v___x_1288_);
lean_inc_ref(v___x_1287_);
v___x_1352_ = l_Lean_Name_mkStr5(v___x_1287_, v___x_1288_, v___x_1289_, v___x_1345_, v___x_1351_);
v___x_1353_ = l_Lean_mkConst(v___x_1352_, v___x_1347_);
lean_inc(v_declName_1293_);
v___x_1354_ = l_Lean_mkConst(v_declName_1293_, v___x_1347_);
v___x_1355_ = l_Lean_Expr_app___override(v___x_1353_, v___x_1354_);
v___y_1300_ = v___y_1315_;
v___y_1301_ = v___y_1316_;
v___y_1302_ = v___y_1314_;
v___y_1303_ = v___x_1347_;
v___y_1304_ = v___x_1355_;
goto v___jp_1299_;
}
}
}
v___jp_1356_:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1358_);
v___x_1363_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_);
v___x_1364_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__6));
lean_inc_ref(v___x_1289_);
lean_inc_ref(v___x_1288_);
lean_inc_ref(v___x_1287_);
v___x_1365_ = l_Lean_Name_mkStr4(v___x_1287_, v___x_1288_, v___x_1289_, v___x_1364_);
v___x_1366_ = l_Lean_MessageData_ofConstName(v___x_1365_, v___y_1361_);
v___x_1367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1363_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
v___x_1368_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__5_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__5_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__5_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_);
v___x_1369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1367_);
lean_ctor_set(v___x_1369_, 1, v___x_1368_);
v___x_1370_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__5));
v___x_1371_ = l_Lean_Name_mkStr4(v___x_1287_, v___x_1288_, v___x_1289_, v___x_1370_);
v___x_1372_ = l_Lean_MessageData_ofConstName(v___x_1371_, v___y_1361_);
v___x_1373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1369_);
lean_ctor_set(v___x_1373_, 1, v___x_1372_);
v___x_1374_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__7_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__7_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__7_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_);
v___x_1375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1373_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
v___x_1376_ = l_Lean_MessageData_ofName(v_declName_1293_);
v___x_1377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1375_);
lean_ctor_set(v___x_1377_, 1, v___x_1376_);
v___x_1378_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__9_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__9_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1___closed__9_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_);
v___x_1379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1377_);
lean_ctor_set(v___x_1379_, 1, v___x_1378_);
v___x_1380_ = l_Lean_ConstantInfo_type(v___y_1359_);
lean_dec_ref(v___y_1359_);
v___x_1381_ = l_Lean_indentExpr(v___x_1380_);
v___x_1382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1379_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
v___x_1383_ = l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0___redArg(v___x_1382_, v___y_1357_, v___y_1362_);
return v___x_1383_;
}
v___jp_1384_:
{
lean_object* v___x_1388_; 
lean_inc(v_declName_1293_);
v___x_1388_ = l_Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1(v_declName_1293_, v___y_1386_, v___y_1387_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; lean_object* v___x_1390_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_a_1389_);
lean_dec_ref_known(v___x_1388_, 1);
v___x_1390_ = l_Lean_Attribute_Builtin_getIdent(v_stx_1294_, v___y_1386_, v___y_1387_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_a_1391_);
lean_dec_ref_known(v___x_1390_, 1);
v___x_1392_ = lean_box(0);
v___x_1393_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_a_1391_, v___x_1392_, v___y_1386_, v___y_1387_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; uint8_t v___x_1395_; lean_object* v___x_1396_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc_n(v_a_1394_, 2);
lean_dec_ref_known(v___x_1393_, 1);
v___x_1395_ = 0;
v___x_1396_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3(v_a_1394_, v___x_1395_, v___y_1386_, v___y_1387_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v___x_1397_; uint8_t v___x_1398_; 
lean_dec_ref_known(v___x_1396_, 1);
v___x_1397_ = l_Lean_ConstantInfo_levelParams(v_a_1389_);
v___x_1398_ = l_List_isEmpty___redArg(v___x_1397_);
lean_dec(v___x_1397_);
if (v___x_1398_ == 0)
{
lean_dec(v___x_1291_);
v___y_1357_ = v___y_1386_;
v___y_1358_ = v___y_1385_;
v___y_1359_ = v_a_1389_;
v___y_1360_ = v_a_1394_;
v___y_1361_ = v___x_1395_;
v___y_1362_ = v___y_1387_;
goto v___jp_1356_;
}
else
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; 
v___x_1399_ = l_Lean_ConstantInfo_type(v_a_1389_);
v___x_1400_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__6));
lean_inc_ref(v___x_1289_);
lean_inc_ref(v___x_1288_);
lean_inc_ref(v___x_1287_);
v___x_1401_ = l_Lean_Name_mkStr4(v___x_1287_, v___x_1288_, v___x_1289_, v___x_1400_);
v___x_1402_ = lean_box(0);
v___x_1403_ = l_Lean_Expr_const___override(v___x_1401_, v___x_1402_);
v___x_1404_ = lean_expr_eqv(v___x_1399_, v___x_1403_);
lean_dec_ref(v___x_1403_);
if (v___x_1404_ == 0)
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; 
v___x_1405_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__5));
lean_inc_ref(v___x_1289_);
lean_inc_ref(v___x_1288_);
lean_inc_ref(v___x_1287_);
v___x_1406_ = l_Lean_Name_mkStr4(v___x_1287_, v___x_1288_, v___x_1289_, v___x_1405_);
v___x_1407_ = l_Lean_Expr_const___override(v___x_1406_, v___x_1402_);
v___x_1408_ = lean_expr_eqv(v___x_1399_, v___x_1407_);
lean_dec_ref(v___x_1407_);
lean_dec_ref(v___x_1399_);
if (v___x_1408_ == 0)
{
lean_dec(v___x_1291_);
v___y_1357_ = v___y_1386_;
v___y_1358_ = v___y_1385_;
v___y_1359_ = v_a_1389_;
v___y_1360_ = v_a_1394_;
v___y_1361_ = v___x_1395_;
v___y_1362_ = v___y_1387_;
goto v___jp_1356_;
}
else
{
v___y_1312_ = v___y_1385_;
v___y_1313_ = v_a_1389_;
v___y_1314_ = v_a_1394_;
v___y_1315_ = v___y_1386_;
v___y_1316_ = v___y_1387_;
goto v___jp_1311_;
}
}
else
{
lean_dec_ref(v___x_1399_);
v___y_1312_ = v___y_1385_;
v___y_1313_ = v_a_1389_;
v___y_1314_ = v_a_1394_;
v___y_1315_ = v___y_1386_;
v___y_1316_ = v___y_1387_;
goto v___jp_1311_;
}
}
}
else
{
lean_dec(v_a_1394_);
lean_dec(v_a_1389_);
lean_dec_ref(v___y_1385_);
lean_dec(v_declName_1293_);
lean_dec(v___x_1291_);
lean_dec_ref(v___x_1289_);
lean_dec_ref(v___x_1288_);
lean_dec_ref(v___x_1287_);
return v___x_1396_;
}
}
else
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1416_; 
lean_dec(v_a_1389_);
lean_dec_ref(v___y_1385_);
lean_dec(v_declName_1293_);
lean_dec(v___x_1291_);
lean_dec_ref(v___x_1289_);
lean_dec_ref(v___x_1288_);
lean_dec_ref(v___x_1287_);
v_a_1409_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1411_ = v___x_1393_;
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1393_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1412_ == 0)
{
v___x_1414_ = v___x_1411_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1409_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
else
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
lean_dec(v_a_1389_);
lean_dec_ref(v___y_1385_);
lean_dec(v_declName_1293_);
lean_dec(v___x_1291_);
lean_dec_ref(v___x_1289_);
lean_dec_ref(v___x_1288_);
lean_dec_ref(v___x_1287_);
v_a_1417_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1390_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1390_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1417_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec_ref(v___y_1385_);
lean_dec(v_stx_1294_);
lean_dec(v_declName_1293_);
lean_dec(v___x_1291_);
lean_dec_ref(v___x_1289_);
lean_dec_ref(v___x_1288_);
lean_dec_ref(v___x_1287_);
v_a_1425_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1388_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1388_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
v___jp_1433_:
{
lean_object* v___x_1436_; 
v___x_1436_ = lean_st_ref_get(v___y_1435_);
if (v_builtin_1290_ == 0)
{
lean_object* v_env_1437_; lean_object* v___x_1438_; 
v_env_1437_ = lean_ctor_get(v___x_1436_, 0);
lean_inc_ref(v_env_1437_);
lean_dec(v___x_1436_);
v___x_1438_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1437_, v_declName_1293_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_dec(v_name_1292_);
v___y_1385_ = v_env_1437_;
v___y_1386_ = v___y_1434_;
v___y_1387_ = v___y_1435_;
goto v___jp_1384_;
}
else
{
lean_object* v___x_1439_; 
lean_dec_ref_known(v___x_1438_, 1);
lean_dec_ref(v_env_1437_);
lean_dec(v_stx_1294_);
lean_dec(v___x_1291_);
lean_dec_ref(v___x_1289_);
lean_dec_ref(v___x_1288_);
lean_dec_ref(v___x_1287_);
v___x_1439_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg(v_name_1292_, v_declName_1293_, v___y_1434_, v___y_1435_);
return v___x_1439_;
}
}
else
{
lean_object* v_env_1440_; 
lean_dec(v_name_1292_);
v_env_1440_ = lean_ctor_get(v___x_1436_, 0);
lean_inc_ref(v_env_1440_);
lean_dec(v___x_1436_);
v___y_1385_ = v_env_1440_;
v___y_1386_ = v___y_1434_;
v___y_1387_ = v___y_1435_;
goto v___jp_1384_;
}
}
v___jp_1441_:
{
if (v_builtin_1290_ == 0)
{
lean_object* v___x_1442_; 
lean_inc(v_declName_1293_);
lean_inc(v_name_1292_);
v___x_1442_ = l_Lean_ensureAttrDeclIsMeta(v_name_1292_, v_declName_1293_, v_kind_1295_, v___y_1296_, v___y_1297_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_dec_ref_known(v___x_1442_, 1);
v___y_1434_ = v___y_1296_;
v___y_1435_ = v___y_1297_;
goto v___jp_1433_;
}
else
{
lean_dec(v_stx_1294_);
lean_dec(v_declName_1293_);
lean_dec(v_name_1292_);
lean_dec(v___x_1291_);
lean_dec_ref(v___x_1289_);
lean_dec_ref(v___x_1288_);
lean_dec_ref(v___x_1287_);
return v___x_1442_;
}
}
else
{
v___y_1434_ = v___y_1296_;
v___y_1435_ = v___y_1297_;
goto v___jp_1433_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2____boxed(lean_object* v___x_1446_, lean_object* v___x_1447_, lean_object* v___x_1448_, lean_object* v_builtin_1449_, lean_object* v___x_1450_, lean_object* v_name_1451_, lean_object* v_declName_1452_, lean_object* v_stx_1453_, lean_object* v_kind_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
uint8_t v_builtin_boxed_1458_; uint8_t v_kind_boxed_1459_; lean_object* v_res_1460_; 
v_builtin_boxed_1458_ = lean_unbox(v_builtin_1449_);
v_kind_boxed_1459_ = lean_unbox(v_kind_1454_);
v_res_1460_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(v___x_1446_, v___x_1447_, v___x_1448_, v_builtin_boxed_1458_, v___x_1450_, v_name_1451_, v_declName_1452_, v_stx_1453_, v_kind_boxed_1459_, v___y_1455_, v___y_1456_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(uint8_t v_builtin_1519_, lean_object* v_name_1520_){
_start:
{
lean_object* v___f_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___f_1528_; lean_object* v___x_1529_; lean_object* v___y_1531_; 
lean_inc_n(v_name_1520_, 2);
v___f_1522_ = lean_alloc_closure((void*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__0_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_1522_, 0, v_name_1520_);
v___x_1523_ = lean_box(0);
v___x_1524_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_));
v___x_1525_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_));
v___x_1526_ = ((lean_object*)(l_Lean_Linter_MissingDocs_mkHandlerUnsafe___closed__4));
v___x_1527_ = lean_box(v_builtin_1519_);
v___f_1528_ = lean_alloc_closure((void*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2____boxed), 12, 6);
lean_closure_set(v___f_1528_, 0, v___x_1524_);
lean_closure_set(v___f_1528_, 1, v___x_1525_);
lean_closure_set(v___f_1528_, 2, v___x_1526_);
lean_closure_set(v___f_1528_, 3, v___x_1527_);
lean_closure_set(v___f_1528_, 4, v___x_1523_);
lean_closure_set(v___f_1528_, 5, v_name_1520_);
v___x_1529_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__21_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
if (v_builtin_1519_ == 0)
{
lean_object* v___x_1538_; 
v___x_1538_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__1));
v___y_1531_ = v___x_1538_;
goto v___jp_1530_;
}
else
{
lean_object* v___x_1539_; 
v___x_1539_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__23_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___y_1531_ = v___x_1539_;
goto v___jp_1530_;
}
v___jp_1530_:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1532_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2___closed__22_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
lean_inc_ref(v___y_1531_);
v___x_1533_ = lean_string_append(v___y_1531_, v___x_1532_);
v___x_1534_ = 1;
v___x_1535_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1535_, 0, v___x_1529_);
lean_ctor_set(v___x_1535_, 1, v_name_1520_);
lean_ctor_set(v___x_1535_, 2, v___x_1533_);
lean_ctor_set_uint8(v___x_1535_, sizeof(void*)*3, v___x_1534_);
v___x_1536_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1535_);
lean_ctor_set(v___x_1536_, 1, v___f_1528_);
lean_ctor_set(v___x_1536_, 2, v___f_1522_);
v___x_1537_ = l_Lean_registerBuiltinAttribute(v___x_1536_);
return v___x_1537_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2____boxed(lean_object* v_builtin_1540_, lean_object* v_name_1541_, lean_object* v___y_1542_){
_start:
{
uint8_t v_builtin_boxed_1543_; lean_object* v_res_1544_; 
v_builtin_boxed_1543_ = lean_unbox(v_builtin_1540_);
v_res_1544_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(v_builtin_boxed_1543_, v_name_1541_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(){
_start:
{
uint8_t v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1552_ = 1;
v___x_1553_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__1_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___x_1554_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(v___x_1552_, v___x_1553_);
if (lean_obj_tag(v___x_1554_) == 0)
{
uint8_t v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
lean_dec_ref_known(v___x_1554_, 1);
v___x_1555_ = 0;
v___x_1556_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___closed__3_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_));
v___x_1557_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn___lam__2_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_(v___x_1555_, v___x_1556_);
return v___x_1557_;
}
else
{
return v___x_1554_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2____boxed(lean_object* v_a_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2_();
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_1560_, lean_object* v_msg_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0___redArg(v_msg_1561_, v___y_1562_, v___y_1563_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_1566_, lean_object* v_msg_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0(v_00_u03b1_1566_, v_msg_1567_, v___y_1568_, v___y_1569_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4(lean_object* v_00_u03b1_1572_, lean_object* v_attrName_1573_, lean_object* v_declName_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___redArg(v_attrName_1573_, v_declName_1574_, v___y_1575_, v___y_1576_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4___boxed(lean_object* v_00_u03b1_1579_, lean_object* v_attrName_1580_, lean_object* v_declName_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_throwAttrDeclInImportedModule___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__4(v_00_u03b1_1579_, v_attrName_1580_, v_declName_1581_, v___y_1582_, v___y_1583_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5(lean_object* v_00_u03b1_1586_, lean_object* v_name_1587_, uint8_t v_kind_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___redArg(v_name_1587_, v_kind_1588_, v___y_1589_, v___y_1590_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5___boxed(lean_object* v_00_u03b1_1593_, lean_object* v_name_1594_, lean_object* v_kind_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
uint8_t v_kind_boxed_1599_; lean_object* v_res_1600_; 
v_kind_boxed_1599_ = lean_unbox(v_kind_1595_);
v_res_1600_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__5(v_00_u03b1_1593_, v_name_1594_, v_kind_boxed_1599_, v___y_1596_, v___y_1597_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b1_1601_, lean_object* v_constName_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2___redArg(v_constName_1602_, v___y_1603_, v___y_1604_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b1_1607_, lean_object* v_constName_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b1_1607_, v_constName_1608_, v___y_1609_, v___y_1610_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7(lean_object* v_00_u03b2_1613_, lean_object* v_m_1614_, lean_object* v_a_1615_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___redArg(v_m_1614_, v_a_1615_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7___boxed(lean_object* v_00_u03b2_1617_, lean_object* v_m_1618_, lean_object* v_a_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7(v_00_u03b2_1617_, v_m_1618_, v_a_1619_);
lean_dec(v_a_1619_);
lean_dec_ref(v_m_1618_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1621_, lean_object* v_ref_1622_, lean_object* v_constName_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_ref_1622_, v_constName_1623_, v___y_1624_, v___y_1625_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1628_, lean_object* v_ref_1629_, lean_object* v_constName_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_00_u03b1_1628_, v_ref_1629_, v_constName_1630_, v___y_1631_, v___y_1632_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v_ref_1629_);
return v_res_1634_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7(lean_object* v_00_u03b2_1635_, lean_object* v_x_1636_, lean_object* v_x_1637_){
_start:
{
uint8_t v___x_1638_; 
v___x_1638_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7___redArg(v_x_1636_, v_x_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b2_1639_, lean_object* v_x_1640_, lean_object* v_x_1641_){
_start:
{
uint8_t v_res_1642_; lean_object* v_r_1643_; 
v_res_1642_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7(v_00_u03b2_1639_, v_x_1640_, v_x_1641_);
lean_dec_ref(v_x_1641_);
lean_dec_ref(v_x_1640_);
v_r_1643_ = lean_box(v_res_1642_);
return v_r_1643_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11(lean_object* v_00_u03b2_1644_, lean_object* v_a_1645_, lean_object* v_x_1646_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11___redArg(v_a_1645_, v_x_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11___boxed(lean_object* v_00_u03b2_1648_, lean_object* v_a_1649_, lean_object* v_x_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__7_spec__11(v_00_u03b2_1648_, v_a_1649_, v_x_1650_);
lean_dec(v_x_1650_);
lean_dec(v_a_1649_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b1_1652_, lean_object* v_ref_1653_, lean_object* v_msg_1654_, lean_object* v_declHint_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8___redArg(v_ref_1653_, v_msg_1654_, v_declHint_1655_, v___y_1656_, v___y_1657_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b1_1660_, lean_object* v_ref_1661_, lean_object* v_msg_1662_, lean_object* v_declHint_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8(v_00_u03b1_1660_, v_ref_1661_, v_msg_1662_, v_declHint_1663_, v___y_1664_, v___y_1665_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec(v_ref_1661_);
return v_res_1667_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11(lean_object* v_00_u03b2_1668_, lean_object* v_x_1669_, size_t v_x_1670_, lean_object* v_x_1671_){
_start:
{
uint8_t v___x_1672_; 
v___x_1672_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___redArg(v_x_1669_, v_x_1670_, v_x_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11___boxed(lean_object* v_00_u03b2_1673_, lean_object* v_x_1674_, lean_object* v_x_1675_, lean_object* v_x_1676_){
_start:
{
size_t v_x_10039__boxed_1677_; uint8_t v_res_1678_; lean_object* v_r_1679_; 
v_x_10039__boxed_1677_ = lean_unbox_usize(v_x_1675_);
lean_dec(v_x_1675_);
v_res_1678_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11(v_00_u03b2_1673_, v_x_1674_, v_x_10039__boxed_1677_, v_x_1676_);
lean_dec_ref(v_x_1676_);
lean_dec_ref(v_x_1674_);
v_r_1679_ = lean_box(v_res_1678_);
return v_r_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16(lean_object* v_msg_1680_, lean_object* v_declHint_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___redArg(v_msg_1680_, v_declHint_1681_, v___y_1683_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16___boxed(lean_object* v_msg_1686_, lean_object* v_declHint_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__12_spec__16(v_msg_1686_, v_declHint_1687_, v___y_1688_, v___y_1689_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__13(lean_object* v_00_u03b1_1692_, lean_object* v_ref_1693_, lean_object* v_msg_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__13___redArg(v_ref_1693_, v_msg_1694_, v___y_1695_, v___y_1696_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__13___boxed(lean_object* v_00_u03b1_1699_, lean_object* v_ref_1700_, lean_object* v_msg_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4_spec__8_spec__13(v_00_u03b1_1699_, v_ref_1700_, v_msg_1701_, v___y_1702_, v___y_1703_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v_ref_1700_);
return v_res_1705_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16(lean_object* v_00_u03b2_1706_, lean_object* v_keys_1707_, lean_object* v_vals_1708_, lean_object* v_heq_1709_, lean_object* v_i_1710_, lean_object* v_k_1711_){
_start:
{
uint8_t v___x_1712_; 
v___x_1712_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16___redArg(v_keys_1707_, v_i_1710_, v_k_1711_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16___boxed(lean_object* v_00_u03b2_1713_, lean_object* v_keys_1714_, lean_object* v_vals_1715_, lean_object* v_heq_1716_, lean_object* v_i_1717_, lean_object* v_k_1718_){
_start:
{
uint8_t v_res_1719_; lean_object* v_r_1720_; 
v_res_1719_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__7_spec__11_spec__16(v_00_u03b2_1713_, v_keys_1714_, v_vals_1715_, v_heq_1716_, v_i_1717_, v_k_1718_);
lean_dec_ref(v_k_1718_);
lean_dec_ref(v_vals_1715_);
lean_dec_ref(v_keys_1714_);
v_r_1720_ = lean_box(v_res_1719_);
return v_r_1720_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__3(lean_object* v_opts_1721_, lean_object* v_opt_1722_){
_start:
{
lean_object* v_name_1723_; lean_object* v_defValue_1724_; lean_object* v_map_1725_; lean_object* v___x_1726_; 
v_name_1723_ = lean_ctor_get(v_opt_1722_, 0);
v_defValue_1724_ = lean_ctor_get(v_opt_1722_, 1);
v_map_1725_ = lean_ctor_get(v_opts_1721_, 0);
v___x_1726_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1725_, v_name_1723_);
if (lean_obj_tag(v___x_1726_) == 0)
{
uint8_t v___x_1727_; 
v___x_1727_ = lean_unbox(v_defValue_1724_);
return v___x_1727_;
}
else
{
lean_object* v_val_1728_; 
v_val_1728_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_val_1728_);
lean_dec_ref_known(v___x_1726_, 1);
if (lean_obj_tag(v_val_1728_) == 1)
{
uint8_t v_v_1729_; 
v_v_1729_ = lean_ctor_get_uint8(v_val_1728_, 0);
lean_dec_ref_known(v_val_1728_, 0);
return v_v_1729_;
}
else
{
uint8_t v___x_1730_; 
lean_dec(v_val_1728_);
v___x_1730_ = lean_unbox(v_defValue_1724_);
return v___x_1730_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_opts_1731_, lean_object* v_opt_1732_){
_start:
{
uint8_t v_res_1733_; lean_object* v_r_1734_; 
v_res_1733_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__3(v_opts_1731_, v_opt_1732_);
lean_dec_ref(v_opt_1732_);
lean_dec_ref(v_opts_1731_);
v_r_1734_ = lean_box(v_res_1733_);
return v_r_1734_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_1735_, uint8_t v___y_1736_, lean_object* v_x_1737_){
_start:
{
if (lean_obj_tag(v_x_1737_) == 1)
{
lean_object* v_pre_1738_; 
v_pre_1738_ = lean_ctor_get(v_x_1737_, 0);
if (lean_obj_tag(v_pre_1738_) == 0)
{
lean_object* v_str_1739_; lean_object* v___x_1740_; uint8_t v___x_1741_; 
v_str_1739_ = lean_ctor_get(v_x_1737_, 1);
v___x_1740_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__8));
v___x_1741_ = lean_string_dec_eq(v_str_1739_, v___x_1740_);
if (v___x_1741_ == 0)
{
return v___x_1741_;
}
else
{
return v_suppressElabErrors_1735_;
}
}
else
{
return v___y_1736_;
}
}
else
{
return v___y_1736_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_1742_, lean_object* v___y_1743_, lean_object* v_x_1744_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1745_; uint8_t v___y_2284__boxed_1746_; uint8_t v_res_1747_; lean_object* v_r_1748_; 
v_suppressElabErrors_boxed_1745_ = lean_unbox(v_suppressElabErrors_1742_);
v___y_2284__boxed_1746_ = lean_unbox(v___y_1743_);
v_res_1747_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_1745_, v___y_2284__boxed_1746_, v_x_1744_);
lean_dec(v_x_1744_);
v_r_1748_ = lean_box(v_res_1747_);
return v_r_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_msgData_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v___x_1752_; lean_object* v_env_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v_scopes_1756_; lean_object* v___x_1757_; lean_object* v_opts_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1752_ = lean_st_ref_get(v___y_1750_);
v_env_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc_ref(v_env_1753_);
lean_dec(v___x_1752_);
v___x_1754_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1755_ = lean_st_ref_get(v___y_1750_);
v_scopes_1756_ = lean_ctor_get(v___x_1755_, 2);
lean_inc(v_scopes_1756_);
lean_dec(v___x_1755_);
v___x_1757_ = l_List_head_x21___redArg(v___x_1754_, v_scopes_1756_);
lean_dec(v_scopes_1756_);
v_opts_1758_ = lean_ctor_get(v___x_1757_, 1);
lean_inc_ref(v_opts_1758_);
lean_dec(v___x_1757_);
v___x_1759_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_1760_ = lean_unsigned_to_nat(32u);
v___x_1761_ = lean_mk_empty_array_with_capacity(v___x_1760_);
lean_dec_ref(v___x_1761_);
v___x_1762_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_1763_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1763_, 0, v_env_1753_);
lean_ctor_set(v___x_1763_, 1, v___x_1759_);
lean_ctor_set(v___x_1763_, 2, v___x_1762_);
lean_ctor_set(v___x_1763_, 3, v_opts_1758_);
v___x_1764_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1763_);
lean_ctor_set(v___x_1764_, 1, v_msgData_1749_);
v___x_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2___redArg(v_msgData_1766_, v___y_1767_);
lean_dec(v___y_1767_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1(lean_object* v_ref_1770_, lean_object* v_msgData_1771_, uint8_t v_severity_1772_, uint8_t v_isSilent_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; uint8_t v___y_1782_; uint8_t v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; uint8_t v___y_1843_; lean_object* v___y_1844_; uint8_t v___y_1845_; uint8_t v___y_1846_; lean_object* v___y_1847_; uint8_t v___y_1871_; lean_object* v___y_1872_; uint8_t v___y_1873_; uint8_t v___y_1874_; lean_object* v___y_1875_; uint8_t v___y_1879_; uint8_t v___y_1880_; uint8_t v___y_1881_; uint8_t v___x_1896_; uint8_t v___y_1898_; uint8_t v___y_1899_; uint8_t v___y_1900_; uint8_t v___y_1902_; uint8_t v___x_1914_; 
v___x_1896_ = 2;
v___x_1914_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1772_, v___x_1896_);
if (v___x_1914_ == 0)
{
v___y_1902_ = v___x_1914_;
goto v___jp_1901_;
}
else
{
uint8_t v___x_1915_; 
lean_inc_ref(v_msgData_1771_);
v___x_1915_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1771_);
v___y_1902_ = v___x_1915_;
goto v___jp_1901_;
}
v___jp_1777_:
{
lean_object* v___x_1786_; 
v___x_1786_ = l_Lean_Elab_Command_getScope___redArg(v___y_1785_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; lean_object* v_currNamespace_1788_; lean_object* v___x_1789_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_a_1787_);
lean_dec_ref_known(v___x_1786_, 1);
v_currNamespace_1788_ = lean_ctor_get(v_a_1787_, 2);
lean_inc(v_currNamespace_1788_);
lean_dec(v_a_1787_);
v___x_1789_ = l_Lean_Elab_Command_getScope___redArg(v___y_1785_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1825_; 
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1792_ = v___x_1789_;
v_isShared_1793_ = v_isSharedCheck_1825_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1789_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1825_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v_openDecls_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v_env_1799_; lean_object* v_messages_1800_; lean_object* v_scopes_1801_; lean_object* v_usedQuotCtxts_1802_; lean_object* v_nextMacroScope_1803_; lean_object* v_maxRecDepth_1804_; lean_object* v_ngen_1805_; lean_object* v_auxDeclNGen_1806_; lean_object* v_infoState_1807_; lean_object* v_traceState_1808_; lean_object* v_snapshotTasks_1809_; lean_object* v_prevLinterStates_1810_; lean_object* v_codeQualityEntryTasks_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1824_; 
v_openDecls_1794_ = lean_ctor_get(v_a_1790_, 3);
lean_inc(v_openDecls_1794_);
lean_dec(v_a_1790_);
v___x_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1795_, 0, v_currNamespace_1788_);
lean_ctor_set(v___x_1795_, 1, v_openDecls_1794_);
v___x_1796_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
lean_ctor_set(v___x_1796_, 1, v___y_1780_);
lean_inc_ref(v___y_1781_);
lean_inc_ref(v___y_1784_);
v___x_1797_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1797_, 0, v___y_1784_);
lean_ctor_set(v___x_1797_, 1, v___y_1778_);
lean_ctor_set(v___x_1797_, 2, v___y_1779_);
lean_ctor_set(v___x_1797_, 3, v___y_1781_);
lean_ctor_set(v___x_1797_, 4, v___x_1796_);
lean_ctor_set_uint8(v___x_1797_, sizeof(void*)*5, v___y_1783_);
lean_ctor_set_uint8(v___x_1797_, sizeof(void*)*5 + 1, v___y_1782_);
lean_ctor_set_uint8(v___x_1797_, sizeof(void*)*5 + 2, v_isSilent_1773_);
v___x_1798_ = lean_st_ref_take(v___y_1785_);
v_env_1799_ = lean_ctor_get(v___x_1798_, 0);
v_messages_1800_ = lean_ctor_get(v___x_1798_, 1);
v_scopes_1801_ = lean_ctor_get(v___x_1798_, 2);
v_usedQuotCtxts_1802_ = lean_ctor_get(v___x_1798_, 3);
v_nextMacroScope_1803_ = lean_ctor_get(v___x_1798_, 4);
v_maxRecDepth_1804_ = lean_ctor_get(v___x_1798_, 5);
v_ngen_1805_ = lean_ctor_get(v___x_1798_, 6);
v_auxDeclNGen_1806_ = lean_ctor_get(v___x_1798_, 7);
v_infoState_1807_ = lean_ctor_get(v___x_1798_, 8);
v_traceState_1808_ = lean_ctor_get(v___x_1798_, 9);
v_snapshotTasks_1809_ = lean_ctor_get(v___x_1798_, 10);
v_prevLinterStates_1810_ = lean_ctor_get(v___x_1798_, 11);
v_codeQualityEntryTasks_1811_ = lean_ctor_get(v___x_1798_, 12);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1813_ = v___x_1798_;
v_isShared_1814_ = v_isSharedCheck_1824_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1811_);
lean_inc(v_prevLinterStates_1810_);
lean_inc(v_snapshotTasks_1809_);
lean_inc(v_traceState_1808_);
lean_inc(v_infoState_1807_);
lean_inc(v_auxDeclNGen_1806_);
lean_inc(v_ngen_1805_);
lean_inc(v_maxRecDepth_1804_);
lean_inc(v_nextMacroScope_1803_);
lean_inc(v_usedQuotCtxts_1802_);
lean_inc(v_scopes_1801_);
lean_inc(v_messages_1800_);
lean_inc(v_env_1799_);
lean_dec(v___x_1798_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1824_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1818_; 
v___x_1815_ = lean_box(0);
v___x_1816_ = l_Lean_MessageLog_add(v___x_1797_, v_messages_1800_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 1, v___x_1816_);
v___x_1818_ = v___x_1813_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_env_1799_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v___x_1816_);
lean_ctor_set(v_reuseFailAlloc_1823_, 2, v_scopes_1801_);
lean_ctor_set(v_reuseFailAlloc_1823_, 3, v_usedQuotCtxts_1802_);
lean_ctor_set(v_reuseFailAlloc_1823_, 4, v_nextMacroScope_1803_);
lean_ctor_set(v_reuseFailAlloc_1823_, 5, v_maxRecDepth_1804_);
lean_ctor_set(v_reuseFailAlloc_1823_, 6, v_ngen_1805_);
lean_ctor_set(v_reuseFailAlloc_1823_, 7, v_auxDeclNGen_1806_);
lean_ctor_set(v_reuseFailAlloc_1823_, 8, v_infoState_1807_);
lean_ctor_set(v_reuseFailAlloc_1823_, 9, v_traceState_1808_);
lean_ctor_set(v_reuseFailAlloc_1823_, 10, v_snapshotTasks_1809_);
lean_ctor_set(v_reuseFailAlloc_1823_, 11, v_prevLinterStates_1810_);
lean_ctor_set(v_reuseFailAlloc_1823_, 12, v_codeQualityEntryTasks_1811_);
v___x_1818_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
lean_object* v___x_1819_; lean_object* v___x_1821_; 
v___x_1819_ = lean_st_ref_put(v___y_1785_, v___x_1818_);
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 0, v___x_1815_);
v___x_1821_ = v___x_1792_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1815_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
}
}
else
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
lean_dec(v_currNamespace_1788_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
v_a_1826_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1789_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1789_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
else
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1841_; 
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
v_a_1834_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1836_ = v___x_1786_;
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1786_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1839_; 
if (v_isShared_1837_ == 0)
{
v___x_1839_ = v___x_1836_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1834_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
}
v___jp_1842_:
{
lean_object* v_fileName_1848_; lean_object* v_fileMap_1849_; uint8_t v_suppressElabErrors_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___f_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1869_; 
v_fileName_1848_ = lean_ctor_get(v___y_1774_, 0);
v_fileMap_1849_ = lean_ctor_get(v___y_1774_, 1);
v_suppressElabErrors_1850_ = lean_ctor_get_uint8(v___y_1774_, sizeof(void*)*10);
v___x_1851_ = lean_box(v_suppressElabErrors_1850_);
v___x_1852_ = lean_box(v___y_1843_);
v___f_1853_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1853_, 0, v___x_1851_);
lean_closure_set(v___f_1853_, 1, v___x_1852_);
v___x_1854_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1771_);
v___x_1855_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2___redArg(v___x_1854_, v___y_1775_);
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1858_ = v___x_1855_;
v_isShared_1859_ = v_isSharedCheck_1869_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1855_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1869_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
lean_inc_ref_n(v_fileMap_1849_, 2);
v___x_1860_ = l_Lean_FileMap_toPosition(v_fileMap_1849_, v___y_1844_);
lean_dec(v___y_1844_);
v___x_1861_ = l_Lean_FileMap_toPosition(v_fileMap_1849_, v___y_1847_);
lean_dec(v___y_1847_);
v___x_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1861_);
v___x_1863_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5_spec__8___closed__1));
if (v_suppressElabErrors_1850_ == 0)
{
lean_del_object(v___x_1858_);
lean_dec_ref(v___f_1853_);
v___y_1778_ = v___x_1860_;
v___y_1779_ = v___x_1862_;
v___y_1780_ = v_a_1856_;
v___y_1781_ = v___x_1863_;
v___y_1782_ = v___y_1845_;
v___y_1783_ = v___y_1846_;
v___y_1784_ = v_fileName_1848_;
v___y_1785_ = v___y_1775_;
goto v___jp_1777_;
}
else
{
uint8_t v___x_1864_; 
lean_inc(v_a_1856_);
v___x_1864_ = l_Lean_MessageData_hasTag(v___f_1853_, v_a_1856_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; lean_object* v___x_1867_; 
lean_dec_ref_known(v___x_1862_, 1);
lean_dec_ref(v___x_1860_);
lean_dec(v_a_1856_);
v___x_1865_ = lean_box(0);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 0, v___x_1865_);
v___x_1867_ = v___x_1858_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
else
{
lean_del_object(v___x_1858_);
v___y_1778_ = v___x_1860_;
v___y_1779_ = v___x_1862_;
v___y_1780_ = v_a_1856_;
v___y_1781_ = v___x_1863_;
v___y_1782_ = v___y_1845_;
v___y_1783_ = v___y_1846_;
v___y_1784_ = v_fileName_1848_;
v___y_1785_ = v___y_1775_;
goto v___jp_1777_;
}
}
}
}
v___jp_1870_:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Lean_Syntax_getTailPos_x3f(v___y_1872_, v___y_1874_);
lean_dec(v___y_1872_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_inc(v___y_1875_);
v___y_1843_ = v___y_1871_;
v___y_1844_ = v___y_1875_;
v___y_1845_ = v___y_1873_;
v___y_1846_ = v___y_1874_;
v___y_1847_ = v___y_1875_;
goto v___jp_1842_;
}
else
{
lean_object* v_val_1877_; 
v_val_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_val_1877_);
lean_dec_ref_known(v___x_1876_, 1);
v___y_1843_ = v___y_1871_;
v___y_1844_ = v___y_1875_;
v___y_1845_ = v___y_1873_;
v___y_1846_ = v___y_1874_;
v___y_1847_ = v_val_1877_;
goto v___jp_1842_;
}
}
v___jp_1878_:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_Lean_Elab_Command_getRef___redArg(v___y_1774_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v_ref_1884_; lean_object* v___x_1885_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_a_1883_);
lean_dec_ref_known(v___x_1882_, 1);
v_ref_1884_ = l_Lean_replaceRef(v_ref_1770_, v_a_1883_);
lean_dec(v_a_1883_);
v___x_1885_ = l_Lean_Syntax_getPos_x3f(v_ref_1884_, v___y_1880_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v___x_1886_; 
v___x_1886_ = lean_unsigned_to_nat(0u);
v___y_1871_ = v___y_1879_;
v___y_1872_ = v_ref_1884_;
v___y_1873_ = v___y_1881_;
v___y_1874_ = v___y_1880_;
v___y_1875_ = v___x_1886_;
goto v___jp_1870_;
}
else
{
lean_object* v_val_1887_; 
v_val_1887_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_val_1887_);
lean_dec_ref_known(v___x_1885_, 1);
v___y_1871_ = v___y_1879_;
v___y_1872_ = v_ref_1884_;
v___y_1873_ = v___y_1881_;
v___y_1874_ = v___y_1880_;
v___y_1875_ = v_val_1887_;
goto v___jp_1870_;
}
}
else
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
lean_dec_ref(v_msgData_1771_);
v_a_1888_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1882_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1882_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
v___jp_1897_:
{
if (v___y_1900_ == 0)
{
v___y_1879_ = v___y_1898_;
v___y_1880_ = v___y_1899_;
v___y_1881_ = v_severity_1772_;
goto v___jp_1878_;
}
else
{
v___y_1879_ = v___y_1898_;
v___y_1880_ = v___y_1899_;
v___y_1881_ = v___x_1896_;
goto v___jp_1878_;
}
}
v___jp_1901_:
{
if (v___y_1902_ == 0)
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v_scopes_1905_; lean_object* v___x_1906_; lean_object* v_opts_1907_; uint8_t v___x_1908_; uint8_t v___x_1909_; 
v___x_1903_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_1904_ = lean_st_ref_get(v___y_1775_);
v_scopes_1905_ = lean_ctor_get(v___x_1904_, 2);
lean_inc(v_scopes_1905_);
lean_dec(v___x_1904_);
v___x_1906_ = l_List_head_x21___redArg(v___x_1903_, v_scopes_1905_);
lean_dec(v_scopes_1905_);
v_opts_1907_ = lean_ctor_get(v___x_1906_, 1);
lean_inc_ref(v_opts_1907_);
lean_dec(v___x_1906_);
v___x_1908_ = 1;
v___x_1909_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1772_, v___x_1908_);
if (v___x_1909_ == 0)
{
lean_dec_ref(v_opts_1907_);
v___y_1898_ = v___y_1902_;
v___y_1899_ = v___y_1902_;
v___y_1900_ = v___x_1909_;
goto v___jp_1897_;
}
else
{
lean_object* v___x_1910_; uint8_t v___x_1911_; 
v___x_1910_ = l_Lean_warningAsError;
v___x_1911_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__3(v_opts_1907_, v___x_1910_);
lean_dec_ref(v_opts_1907_);
v___y_1898_ = v___y_1902_;
v___y_1899_ = v___y_1902_;
v___y_1900_ = v___x_1911_;
goto v___jp_1897_;
}
}
else
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
lean_dec_ref(v_msgData_1771_);
v___x_1912_ = lean_box(0);
v___x_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1912_);
return v___x_1913_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_1916_, lean_object* v_msgData_1917_, lean_object* v_severity_1918_, lean_object* v_isSilent_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
uint8_t v_severity_boxed_1923_; uint8_t v_isSilent_boxed_1924_; lean_object* v_res_1925_; 
v_severity_boxed_1923_ = lean_unbox(v_severity_1918_);
v_isSilent_boxed_1924_ = lean_unbox(v_isSilent_1919_);
v_res_1925_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1(v_ref_1916_, v_msgData_1917_, v_severity_boxed_1923_, v_isSilent_boxed_1924_, v___y_1920_, v___y_1921_);
lean_dec(v___y_1921_);
lean_dec_ref(v___y_1920_);
lean_dec(v_ref_1916_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0(lean_object* v_ref_1926_, lean_object* v_msgData_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
uint8_t v___x_1931_; uint8_t v___x_1932_; lean_object* v___x_1933_; 
v___x_1931_ = 1;
v___x_1932_ = 0;
v___x_1933_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1(v_ref_1926_, v_msgData_1927_, v___x_1931_, v___x_1932_, v___y_1928_, v___y_1929_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0___boxed(lean_object* v_ref_1934_, lean_object* v_msgData_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0(v_ref_1934_, v_msgData_1935_, v___y_1936_, v___y_1937_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v_ref_1934_);
return v_res_1939_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1941_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__0));
v___x_1942_ = l_Lean_stringToMessageData(v___x_1941_);
return v___x_1942_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1944_ = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__2));
v___x_1945_ = l_Lean_stringToMessageData(v___x_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0(lean_object* v_linterOption_1946_, lean_object* v_stx_1947_, lean_object* v_msg_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
lean_object* v_name_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1970_; 
v_name_1952_ = lean_ctor_get(v_linterOption_1946_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v_linterOption_1946_);
if (v_isSharedCheck_1970_ == 0)
{
lean_object* v_unused_1971_; 
v_unused_1971_ = lean_ctor_get(v_linterOption_1946_, 1);
lean_dec(v_unused_1971_);
v___x_1954_ = v_linterOption_1946_;
v_isShared_1955_ = v_isSharedCheck_1970_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_name_1952_);
lean_dec(v_linterOption_1946_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1970_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1959_; 
v___x_1956_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__1);
lean_inc(v_name_1952_);
v___x_1957_ = l_Lean_MessageData_ofName(v_name_1952_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set_tag(v___x_1954_, 7);
lean_ctor_set(v___x_1954_, 1, v___x_1957_);
lean_ctor_set(v___x_1954_, 0, v___x_1956_);
v___x_1959_ = v___x_1954_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___x_1956_);
lean_ctor_set(v_reuseFailAlloc_1969_, 1, v___x_1957_);
v___x_1959_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v_disable_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1960_ = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___closed__3);
v___x_1961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1959_);
lean_ctor_set(v___x_1961_, 1, v___x_1960_);
v_disable_1962_ = l_Lean_MessageData_note(v___x_1961_);
v___x_1963_ = l_Lean_Linter_linterMessageTag;
v___x_1964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1964_, 0, v_msg_1948_);
lean_ctor_set(v___x_1964_, 1, v_disable_1962_);
v___x_1965_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1963_);
lean_ctor_set(v___x_1965_, 1, v___x_1964_);
v___x_1966_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1966_, 0, v_name_1952_);
lean_ctor_set(v___x_1966_, 1, v___x_1965_);
lean_inc(v_stx_1947_);
v___x_1967_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_1967_, 0, v_stx_1947_);
lean_ctor_set(v___x_1967_, 1, v___x_1966_);
v___x_1968_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0(v_stx_1947_, v___x_1967_, v___y_1949_, v___y_1950_);
lean_dec(v_stx_1947_);
return v___x_1968_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0___boxed(lean_object* v_linterOption_1972_, lean_object* v_stx_1973_, lean_object* v_msg_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0(v_linterOption_1972_, v_stx_1973_, v_msg_1974_, v___y_1975_, v___y_1976_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
return v_res_1978_;
}
}
static lean_object* _init_l_Lean_Linter_MissingDocs_lint___closed__1(void){
_start:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1980_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lint___closed__0));
v___x_1981_ = l_Lean_stringToMessageData(v___x_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lint(lean_object* v_stx_1982_, lean_object* v_msg_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_){
_start:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1987_ = l_Lean_Linter_linter_missingDocs;
v___x_1988_ = lean_obj_once(&l_Lean_Linter_MissingDocs_lint___closed__1, &l_Lean_Linter_MissingDocs_lint___closed__1_once, _init_l_Lean_Linter_MissingDocs_lint___closed__1);
v___x_1989_ = l_Lean_stringToMessageData(v_msg_1983_);
v___x_1990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1988_);
lean_ctor_set(v___x_1990_, 1, v___x_1989_);
v___x_1991_ = l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0(v___x_1987_, v_stx_1982_, v___x_1990_, v_a_1984_, v_a_1985_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lint___boxed(lean_object* v_stx_1992_, lean_object* v_msg_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_){
_start:
{
lean_object* v_res_1997_; 
v_res_1997_ = l_Lean_Linter_MissingDocs_lint(v_stx_1992_, v_msg_1993_, v_a_1994_, v_a_1995_);
lean_dec(v_a_1995_);
lean_dec_ref(v_a_1994_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v___x_2002_; 
v___x_2002_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2___redArg(v_msgData_1998_, v___y_2000_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2(v_msgData_2003_, v___y_2004_, v___y_2005_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
return v_res_2007_;
}
}
static lean_object* _init_l_Lean_Linter_MissingDocs_lintEmpty___closed__1(void){
_start:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2009_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintEmpty___closed__0));
v___x_2010_ = l_Lean_stringToMessageData(v___x_2009_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintEmpty(lean_object* v_stx_2011_, lean_object* v_msg_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_){
_start:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2016_ = l_Lean_Linter_linter_missingDocs;
v___x_2017_ = lean_obj_once(&l_Lean_Linter_MissingDocs_lintEmpty___closed__1, &l_Lean_Linter_MissingDocs_lintEmpty___closed__1_once, _init_l_Lean_Linter_MissingDocs_lintEmpty___closed__1);
v___x_2018_ = l_Lean_stringToMessageData(v_msg_2012_);
v___x_2019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2017_);
lean_ctor_set(v___x_2019_, 1, v___x_2018_);
v___x_2020_ = l_Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0(v___x_2016_, v_stx_2011_, v___x_2019_, v_a_2013_, v_a_2014_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintEmpty___boxed(lean_object* v_stx_2021_, lean_object* v_msg_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Lean_Linter_MissingDocs_lintEmpty(v_stx_2021_, v_msg_2022_, v_a_2023_, v_a_2024_);
lean_dec(v_a_2024_);
lean_dec_ref(v_a_2023_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintNamed(lean_object* v_stx_2027_, lean_object* v_msg_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_){
_start:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; uint8_t v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2032_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__13));
v___x_2033_ = lean_string_append(v_msg_2028_, v___x_2032_);
v___x_2034_ = l_Lean_Syntax_getId(v_stx_2027_);
v___x_2035_ = 1;
v___x_2036_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2034_, v___x_2035_);
v___x_2037_ = lean_string_append(v___x_2033_, v___x_2036_);
lean_dec_ref(v___x_2036_);
v___x_2038_ = l_Lean_Linter_MissingDocs_lint(v_stx_2027_, v___x_2037_, v_a_2029_, v_a_2030_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintNamed___boxed(lean_object* v_stx_2039_, lean_object* v_msg_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_Lean_Linter_MissingDocs_lintNamed(v_stx_2039_, v_msg_2040_, v_a_2041_, v_a_2042_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintEmptyNamed(lean_object* v_stx_2045_, lean_object* v_msg_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2050_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__13));
v___x_2051_ = lean_string_append(v_msg_2046_, v___x_2050_);
v___x_2052_ = l_Lean_Syntax_getId(v_stx_2045_);
v___x_2053_ = 1;
v___x_2054_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2052_, v___x_2053_);
v___x_2055_ = lean_string_append(v___x_2051_, v___x_2054_);
lean_dec_ref(v___x_2054_);
v___x_2056_ = l_Lean_Linter_MissingDocs_lintEmpty(v_stx_2045_, v___x_2055_, v_a_2047_, v_a_2048_);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintEmptyNamed___boxed(lean_object* v_stx_2057_, lean_object* v_msg_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l_Lean_Linter_MissingDocs_lintEmptyNamed(v_stx_2057_, v_msg_2058_, v_a_2059_, v_a_2060_);
lean_dec(v_a_2060_);
lean_dec_ref(v_a_2059_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintField(lean_object* v_parent_2064_, lean_object* v_stx_2065_, lean_object* v_msg_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_){
_start:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2070_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__13));
v___x_2071_ = lean_string_append(v_msg_2066_, v___x_2070_);
v___x_2072_ = l_Lean_Syntax_getId(v_parent_2064_);
v___x_2073_ = 1;
v___x_2074_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2072_, v___x_2073_);
v___x_2075_ = lean_string_append(v___x_2071_, v___x_2074_);
lean_dec_ref(v___x_2074_);
v___x_2076_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintField___closed__0));
v___x_2077_ = lean_string_append(v___x_2075_, v___x_2076_);
v___x_2078_ = l_Lean_Syntax_getId(v_stx_2065_);
v___x_2079_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2078_, v___x_2073_);
v___x_2080_ = lean_string_append(v___x_2077_, v___x_2079_);
lean_dec_ref(v___x_2079_);
v___x_2081_ = l_Lean_Linter_MissingDocs_lint(v_stx_2065_, v___x_2080_, v_a_2067_, v_a_2068_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintField___boxed(lean_object* v_parent_2082_, lean_object* v_stx_2083_, lean_object* v_msg_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = l_Lean_Linter_MissingDocs_lintField(v_parent_2082_, v_stx_2083_, v_msg_2084_, v_a_2085_, v_a_2086_);
lean_dec(v_a_2086_);
lean_dec_ref(v_a_2085_);
lean_dec(v_parent_2082_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintEmptyField(lean_object* v_parent_2089_, lean_object* v_stx_2090_, lean_object* v_msg_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_){
_start:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; uint8_t v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2095_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__13));
v___x_2096_ = lean_string_append(v_msg_2091_, v___x_2095_);
v___x_2097_ = l_Lean_Syntax_getId(v_parent_2089_);
v___x_2098_ = 1;
v___x_2099_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2097_, v___x_2098_);
v___x_2100_ = lean_string_append(v___x_2096_, v___x_2099_);
lean_dec_ref(v___x_2099_);
v___x_2101_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintField___closed__0));
v___x_2102_ = lean_string_append(v___x_2100_, v___x_2101_);
v___x_2103_ = l_Lean_Syntax_getId(v_stx_2090_);
v___x_2104_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2103_, v___x_2098_);
v___x_2105_ = lean_string_append(v___x_2102_, v___x_2104_);
lean_dec_ref(v___x_2104_);
v___x_2106_ = l_Lean_Linter_MissingDocs_lintEmpty(v_stx_2090_, v___x_2105_, v_a_2092_, v_a_2093_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintEmptyField___boxed(lean_object* v_parent_2107_, lean_object* v_stx_2108_, lean_object* v_msg_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l_Lean_Linter_MissingDocs_lintEmptyField(v_parent_2107_, v_stx_2108_, v_msg_2109_, v_a_2110_, v_a_2111_);
lean_dec(v_a_2111_);
lean_dec_ref(v_a_2110_);
lean_dec(v_parent_2107_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintStructField(lean_object* v_parent_2114_, lean_object* v_stx_2115_, lean_object* v_msg_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_){
_start:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; uint8_t v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2120_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__13));
v___x_2121_ = lean_string_append(v_msg_2116_, v___x_2120_);
v___x_2122_ = l_Lean_Syntax_getId(v_parent_2114_);
v___x_2123_ = 1;
v___x_2124_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2122_, v___x_2123_);
v___x_2125_ = lean_string_append(v___x_2121_, v___x_2124_);
lean_dec_ref(v___x_2124_);
v___x_2126_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintField___closed__0));
v___x_2127_ = lean_string_append(v___x_2125_, v___x_2126_);
v___x_2128_ = l_Lean_Syntax_getId(v_stx_2115_);
v___x_2129_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2128_, v___x_2123_);
v___x_2130_ = lean_string_append(v___x_2127_, v___x_2129_);
lean_dec_ref(v___x_2129_);
v___x_2131_ = l_Lean_Linter_MissingDocs_lint(v_stx_2115_, v___x_2130_, v_a_2117_, v_a_2118_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintStructField___boxed(lean_object* v_parent_2132_, lean_object* v_stx_2133_, lean_object* v_msg_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_Lean_Linter_MissingDocs_lintStructField(v_parent_2132_, v_stx_2133_, v_msg_2134_, v_a_2135_, v_a_2136_);
lean_dec(v_a_2136_);
lean_dec_ref(v_a_2135_);
lean_dec(v_parent_2132_);
return v_res_2138_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2139_ = lean_box(1);
v___x_2140_ = l_Lean_MessageData_ofFormat(v___x_2139_);
return v___x_2140_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__2));
v___x_2145_ = l_Lean_MessageData_ofFormat(v___x_2144_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_x_2146_, lean_object* v_x_2147_){
_start:
{
if (lean_obj_tag(v_x_2147_) == 0)
{
return v_x_2146_;
}
else
{
lean_object* v_head_2148_; lean_object* v_tail_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2171_; 
v_head_2148_ = lean_ctor_get(v_x_2147_, 0);
v_tail_2149_ = lean_ctor_get(v_x_2147_, 1);
v_isSharedCheck_2171_ = !lean_is_exclusive(v_x_2147_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2151_ = v_x_2147_;
v_isShared_2152_ = v_isSharedCheck_2171_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_tail_2149_);
lean_inc(v_head_2148_);
lean_dec(v_x_2147_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2171_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v_before_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2169_; 
v_before_2153_ = lean_ctor_get(v_head_2148_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v_head_2148_);
if (v_isSharedCheck_2169_ == 0)
{
lean_object* v_unused_2170_; 
v_unused_2170_ = lean_ctor_get(v_head_2148_, 1);
lean_dec(v_unused_2170_);
v___x_2155_ = v_head_2148_;
v_isShared_2156_ = v_isSharedCheck_2169_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_before_2153_);
lean_dec(v_head_2148_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2169_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2157_; lean_object* v___x_2159_; 
v___x_2157_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__0);
if (v_isShared_2156_ == 0)
{
lean_ctor_set_tag(v___x_2155_, 7);
lean_ctor_set(v___x_2155_, 1, v___x_2157_);
lean_ctor_set(v___x_2155_, 0, v_x_2146_);
v___x_2159_ = v___x_2155_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_x_2146_);
lean_ctor_set(v_reuseFailAlloc_2168_, 1, v___x_2157_);
v___x_2159_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
lean_object* v___x_2160_; lean_object* v___x_2162_; 
v___x_2160_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__3);
if (v_isShared_2152_ == 0)
{
lean_ctor_set_tag(v___x_2151_, 7);
lean_ctor_set(v___x_2151_, 1, v___x_2160_);
lean_ctor_set(v___x_2151_, 0, v___x_2159_);
v___x_2162_ = v___x_2151_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2159_);
lean_ctor_set(v_reuseFailAlloc_2167_, 1, v___x_2160_);
v___x_2162_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2163_ = l_Lean_MessageData_ofSyntax(v_before_2153_);
v___x_2164_ = l_Lean_indentD(v___x_2163_);
v___x_2165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2162_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v_x_2146_ = v___x_2165_;
v_x_2147_ = v_tail_2149_;
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
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg___closed__1));
v___x_2176_ = l_Lean_MessageData_ofFormat(v___x_2175_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_msgData_2177_, lean_object* v_macroStack_2178_, lean_object* v___y_2179_){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v_scopes_2183_; lean_object* v___x_2184_; lean_object* v_opts_2185_; lean_object* v___x_2186_; uint8_t v___x_2187_; 
v___x_2181_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2182_ = lean_st_ref_get(v___y_2179_);
v_scopes_2183_ = lean_ctor_get(v___x_2182_, 2);
lean_inc(v_scopes_2183_);
lean_dec(v___x_2182_);
v___x_2184_ = l_List_head_x21___redArg(v___x_2181_, v_scopes_2183_);
lean_dec(v_scopes_2183_);
v_opts_2185_ = lean_ctor_get(v___x_2184_, 1);
lean_inc_ref(v_opts_2185_);
lean_dec(v___x_2184_);
v___x_2186_ = l_Lean_Elab_pp_macroStack;
v___x_2187_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__3(v_opts_2185_, v___x_2186_);
lean_dec_ref(v_opts_2185_);
if (v___x_2187_ == 0)
{
lean_object* v___x_2188_; 
lean_dec(v_macroStack_2178_);
v___x_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2188_, 0, v_msgData_2177_);
return v___x_2188_;
}
else
{
if (lean_obj_tag(v_macroStack_2178_) == 0)
{
lean_object* v___x_2189_; 
v___x_2189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2189_, 0, v_msgData_2177_);
return v___x_2189_;
}
else
{
lean_object* v_head_2190_; lean_object* v_after_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2206_; 
v_head_2190_ = lean_ctor_get(v_macroStack_2178_, 0);
lean_inc(v_head_2190_);
v_after_2191_ = lean_ctor_get(v_head_2190_, 1);
v_isSharedCheck_2206_ = !lean_is_exclusive(v_head_2190_);
if (v_isSharedCheck_2206_ == 0)
{
lean_object* v_unused_2207_; 
v_unused_2207_ = lean_ctor_get(v_head_2190_, 0);
lean_dec(v_unused_2207_);
v___x_2193_ = v_head_2190_;
v_isShared_2194_ = v_isSharedCheck_2206_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_after_2191_);
lean_dec(v_head_2190_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2206_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2195_; lean_object* v___x_2197_; 
v___x_2195_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3___closed__0);
if (v_isShared_2194_ == 0)
{
lean_ctor_set_tag(v___x_2193_, 7);
lean_ctor_set(v___x_2193_, 1, v___x_2195_);
lean_ctor_set(v___x_2193_, 0, v_msgData_2177_);
v___x_2197_ = v___x_2193_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_msgData_2177_);
lean_ctor_set(v_reuseFailAlloc_2205_, 1, v___x_2195_);
v___x_2197_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v_msgData_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2198_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg___closed__2);
v___x_2199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2197_);
lean_ctor_set(v___x_2199_, 1, v___x_2198_);
v___x_2200_ = l_Lean_MessageData_ofSyntax(v_after_2191_);
v___x_2201_ = l_Lean_indentD(v___x_2200_);
v_msgData_2202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2202_, 0, v___x_2199_);
lean_ctor_set(v_msgData_2202_, 1, v___x_2201_);
v___x_2203_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2_spec__3(v_msgData_2202_, v_macroStack_2178_);
v___x_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
return v___x_2204_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_2208_, lean_object* v_macroStack_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg(v_msgData_2208_, v_macroStack_2209_, v___y_2210_);
lean_dec(v___y_2210_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v___x_2217_; 
v___x_2217_ = l_Lean_Elab_Command_getRef___redArg(v___y_2214_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; lean_object* v_macroStack_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v_a_2222_; lean_object* v___x_2223_; lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2232_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2218_);
lean_dec_ref_known(v___x_2217_, 1);
v_macroStack_2219_ = lean_ctor_get(v___y_2214_, 4);
v___x_2220_ = l_Lean_Elab_getBetterRef(v_a_2218_, v_macroStack_2219_);
lean_dec(v_a_2218_);
v___x_2221_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_MissingDocs_lint_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_2213_, v___y_2215_);
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_a_2222_);
lean_dec_ref(v___x_2221_);
lean_inc(v_macroStack_2219_);
v___x_2223_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg(v_a_2222_, v_macroStack_2219_, v___y_2215_);
v_a_2224_ = lean_ctor_get(v___x_2223_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2226_ = v___x_2223_;
v_isShared_2227_ = v_isSharedCheck_2232_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2223_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2232_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2228_; lean_object* v___x_2230_; 
v___x_2228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2220_);
lean_ctor_set(v___x_2228_, 1, v_a_2224_);
if (v_isShared_2227_ == 0)
{
lean_ctor_set_tag(v___x_2226_, 1);
lean_ctor_set(v___x_2226_, 0, v___x_2228_);
v___x_2230_ = v___x_2226_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v___x_2228_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
lean_dec_ref(v_msg_2213_);
v_a_2233_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___x_2217_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2217_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg(v_msg_2241_, v___y_2242_, v___y_2243_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0___redArg(lean_object* v_ref_2246_, lean_object* v_msg_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
lean_object* v___x_2251_; 
v___x_2251_ = l_Lean_Elab_Command_getRef___redArg(v___y_2248_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_a_2252_; lean_object* v_fileName_2253_; lean_object* v_fileMap_2254_; lean_object* v_currRecDepth_2255_; lean_object* v_cmdPos_2256_; lean_object* v_macroStack_2257_; lean_object* v_quotContext_x3f_2258_; lean_object* v_currMacroScope_2259_; lean_object* v_snap_x3f_2260_; lean_object* v_cancelTk_x3f_2261_; uint8_t v_suppressElabErrors_2262_; lean_object* v_ref_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_a_2252_);
lean_dec_ref_known(v___x_2251_, 1);
v_fileName_2253_ = lean_ctor_get(v___y_2248_, 0);
v_fileMap_2254_ = lean_ctor_get(v___y_2248_, 1);
v_currRecDepth_2255_ = lean_ctor_get(v___y_2248_, 2);
v_cmdPos_2256_ = lean_ctor_get(v___y_2248_, 3);
v_macroStack_2257_ = lean_ctor_get(v___y_2248_, 4);
v_quotContext_x3f_2258_ = lean_ctor_get(v___y_2248_, 5);
v_currMacroScope_2259_ = lean_ctor_get(v___y_2248_, 6);
v_snap_x3f_2260_ = lean_ctor_get(v___y_2248_, 8);
v_cancelTk_x3f_2261_ = lean_ctor_get(v___y_2248_, 9);
v_suppressElabErrors_2262_ = lean_ctor_get_uint8(v___y_2248_, sizeof(void*)*10);
v_ref_2263_ = l_Lean_replaceRef(v_ref_2246_, v_a_2252_);
lean_dec(v_a_2252_);
lean_inc(v_cancelTk_x3f_2261_);
lean_inc(v_snap_x3f_2260_);
lean_inc(v_currMacroScope_2259_);
lean_inc(v_quotContext_x3f_2258_);
lean_inc(v_macroStack_2257_);
lean_inc(v_cmdPos_2256_);
lean_inc(v_currRecDepth_2255_);
lean_inc_ref(v_fileMap_2254_);
lean_inc_ref(v_fileName_2253_);
v___x_2264_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_2264_, 0, v_fileName_2253_);
lean_ctor_set(v___x_2264_, 1, v_fileMap_2254_);
lean_ctor_set(v___x_2264_, 2, v_currRecDepth_2255_);
lean_ctor_set(v___x_2264_, 3, v_cmdPos_2256_);
lean_ctor_set(v___x_2264_, 4, v_macroStack_2257_);
lean_ctor_set(v___x_2264_, 5, v_quotContext_x3f_2258_);
lean_ctor_set(v___x_2264_, 6, v_currMacroScope_2259_);
lean_ctor_set(v___x_2264_, 7, v_ref_2263_);
lean_ctor_set(v___x_2264_, 8, v_snap_x3f_2260_);
lean_ctor_set(v___x_2264_, 9, v_cancelTk_x3f_2261_);
lean_ctor_set_uint8(v___x_2264_, sizeof(void*)*10, v_suppressElabErrors_2262_);
v___x_2265_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg(v_msg_2247_, v___x_2264_, v___y_2249_);
lean_dec_ref_known(v___x_2264_, 10);
return v___x_2265_;
}
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
lean_dec_ref(v_msg_2247_);
v_a_2266_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2251_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2251_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0___redArg___boxed(lean_object* v_ref_2274_, lean_object* v_msg_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0___redArg(v_ref_2274_, v_msg_2275_, v___y_2276_, v___y_2277_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v_ref_2274_);
return v_res_2279_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2281_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__0));
v___x_2282_ = l_Lean_stringToMessageData(v___x_2281_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0(lean_object* v_stx_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v_val_2297_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2304_ = lean_unsigned_to_nat(1u);
v___x_2305_ = l_Lean_Syntax_getArg(v_stx_2286_, v___x_2304_);
switch(lean_obj_tag(v___x_2305_))
{
case 2:
{
lean_object* v_val_2306_; 
lean_dec(v_stx_2286_);
v_val_2306_ = lean_ctor_get(v___x_2305_, 1);
lean_inc_ref(v_val_2306_);
lean_dec_ref_known(v___x_2305_, 2);
v_val_2297_ = v_val_2306_;
goto v___jp_2296_;
}
case 1:
{
lean_object* v_kind_2307_; 
v_kind_2307_ = lean_ctor_get(v___x_2305_, 1);
lean_inc(v_kind_2307_);
if (lean_obj_tag(v_kind_2307_) == 1)
{
lean_object* v_pre_2308_; 
v_pre_2308_ = lean_ctor_get(v_kind_2307_, 0);
lean_inc(v_pre_2308_);
if (lean_obj_tag(v_pre_2308_) == 1)
{
lean_object* v_pre_2309_; 
v_pre_2309_ = lean_ctor_get(v_pre_2308_, 0);
lean_inc(v_pre_2309_);
if (lean_obj_tag(v_pre_2309_) == 1)
{
lean_object* v_pre_2310_; 
v_pre_2310_ = lean_ctor_get(v_pre_2309_, 0);
lean_inc(v_pre_2310_);
if (lean_obj_tag(v_pre_2310_) == 1)
{
lean_object* v_pre_2311_; 
v_pre_2311_ = lean_ctor_get(v_pre_2310_, 0);
if (lean_obj_tag(v_pre_2311_) == 0)
{
lean_object* v_str_2312_; lean_object* v_str_2313_; lean_object* v_str_2314_; lean_object* v_str_2315_; lean_object* v___x_2316_; uint8_t v___x_2317_; 
v_str_2312_ = lean_ctor_get(v_kind_2307_, 1);
lean_inc_ref(v_str_2312_);
lean_dec_ref_known(v_kind_2307_, 2);
v_str_2313_ = lean_ctor_get(v_pre_2308_, 1);
lean_inc_ref(v_str_2313_);
lean_dec_ref_known(v_pre_2308_, 2);
v_str_2314_ = lean_ctor_get(v_pre_2309_, 1);
lean_inc_ref(v_str_2314_);
lean_dec_ref_known(v_pre_2309_, 2);
v_str_2315_ = lean_ctor_get(v_pre_2310_, 1);
lean_inc_ref(v_str_2315_);
lean_dec_ref_known(v_pre_2310_, 2);
v___x_2316_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_));
v___x_2317_ = lean_string_dec_eq(v_str_2315_, v___x_2316_);
lean_dec_ref(v_str_2315_);
if (v___x_2317_ == 0)
{
lean_dec_ref(v_str_2314_);
lean_dec_ref(v_str_2313_);
lean_dec_ref(v_str_2312_);
lean_dec_ref_known(v___x_2305_, 3);
goto v___jp_2290_;
}
else
{
lean_object* v___x_2318_; uint8_t v___x_2319_; 
v___x_2318_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2));
v___x_2319_ = lean_string_dec_eq(v_str_2314_, v___x_2318_);
lean_dec_ref(v_str_2314_);
if (v___x_2319_ == 0)
{
lean_dec_ref(v_str_2313_);
lean_dec_ref(v_str_2312_);
lean_dec_ref_known(v___x_2305_, 3);
goto v___jp_2290_;
}
else
{
lean_object* v___x_2320_; uint8_t v___x_2321_; 
v___x_2320_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3));
v___x_2321_ = lean_string_dec_eq(v_str_2313_, v___x_2320_);
lean_dec_ref(v_str_2313_);
if (v___x_2321_ == 0)
{
lean_dec_ref(v_str_2312_);
lean_dec_ref_known(v___x_2305_, 3);
goto v___jp_2290_;
}
else
{
lean_object* v___x_2322_; uint8_t v___x_2323_; 
v___x_2322_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__4));
v___x_2323_ = lean_string_dec_eq(v_str_2312_, v___x_2322_);
lean_dec_ref(v_str_2312_);
if (v___x_2323_ == 0)
{
lean_dec_ref_known(v___x_2305_, 3);
goto v___jp_2290_;
}
else
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2324_ = lean_unsigned_to_nat(0u);
v___x_2325_ = l_Lean_Syntax_getArg(v___x_2305_, v___x_2324_);
lean_dec_ref_known(v___x_2305_, 3);
if (lean_obj_tag(v___x_2325_) == 2)
{
lean_object* v_val_2326_; 
lean_dec(v_stx_2286_);
v_val_2326_ = lean_ctor_get(v___x_2325_, 1);
lean_inc_ref(v_val_2326_);
lean_dec_ref_known(v___x_2325_, 2);
v_val_2297_ = v_val_2326_;
goto v___jp_2296_;
}
else
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
lean_dec(v___x_2325_);
v___x_2327_ = lean_obj_once(&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__1, &l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__1_once, _init_l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__1);
lean_inc(v_stx_2286_);
v___x_2328_ = l_Lean_MessageData_ofSyntax(v_stx_2286_);
v___x_2329_ = l_Lean_indentD(v___x_2328_);
v___x_2330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2327_);
lean_ctor_set(v___x_2330_, 1, v___x_2329_);
v___x_2331_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0___redArg(v_stx_2286_, v___x_2330_, v___y_2287_, v___y_2288_);
lean_dec(v_stx_2286_);
return v___x_2331_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_2310_, 2);
lean_dec_ref_known(v_pre_2309_, 2);
lean_dec_ref_known(v_pre_2308_, 2);
lean_dec_ref_known(v_kind_2307_, 2);
lean_dec_ref_known(v___x_2305_, 3);
goto v___jp_2290_;
}
}
else
{
lean_dec_ref_known(v_pre_2309_, 2);
lean_dec(v_pre_2310_);
lean_dec_ref_known(v_pre_2308_, 2);
lean_dec_ref_known(v_kind_2307_, 2);
lean_dec_ref_known(v___x_2305_, 3);
goto v___jp_2290_;
}
}
else
{
lean_dec_ref_known(v_pre_2308_, 2);
lean_dec(v_pre_2309_);
lean_dec_ref_known(v_kind_2307_, 2);
lean_dec_ref_known(v___x_2305_, 3);
goto v___jp_2290_;
}
}
else
{
lean_dec_ref_known(v_kind_2307_, 2);
lean_dec(v_pre_2308_);
lean_dec_ref_known(v___x_2305_, 3);
goto v___jp_2290_;
}
}
else
{
lean_dec(v_kind_2307_);
lean_dec_ref_known(v___x_2305_, 3);
goto v___jp_2290_;
}
}
default: 
{
lean_dec(v___x_2305_);
goto v___jp_2290_;
}
}
v___jp_2290_:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2291_ = lean_obj_once(&l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__1, &l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__1_once, _init_l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__1);
lean_inc(v_stx_2286_);
v___x_2292_ = l_Lean_MessageData_ofSyntax(v_stx_2286_);
v___x_2293_ = l_Lean_indentD(v___x_2292_);
v___x_2294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2291_);
lean_ctor_set(v___x_2294_, 1, v___x_2293_);
v___x_2295_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0___redArg(v_stx_2286_, v___x_2294_, v___y_2287_, v___y_2288_);
lean_dec(v_stx_2286_);
return v___x_2295_;
}
v___jp_2296_:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2298_ = lean_unsigned_to_nat(0u);
v___x_2299_ = lean_string_utf8_byte_size(v_val_2297_);
v___x_2300_ = lean_unsigned_to_nat(2u);
v___x_2301_ = lean_nat_sub(v___x_2299_, v___x_2300_);
v___x_2302_ = lean_string_utf8_extract(v_val_2297_, v___x_2298_, v___x_2301_);
lean_dec(v___x_2301_);
lean_dec_ref(v_val_2297_);
v___x_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
return v___x_2303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___boxed(lean_object* v_stx_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
lean_object* v_res_2336_; 
v_res_2336_ = l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0(v_stx_2332_, v___y_2333_, v___y_2334_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString(lean_object* v_docOpt_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_){
_start:
{
uint8_t v___x_2341_; 
v___x_2341_ = l_Lean_Syntax_isNone(v_docOpt_2337_);
if (v___x_2341_ == 0)
{
lean_object* v___x_2342_; lean_object* v_docStx_2343_; lean_object* v___y_2345_; lean_object* v___y_2346_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2342_ = lean_unsigned_to_nat(0u);
v_docStx_2343_ = l_Lean_Syntax_getArg(v_docOpt_2337_, v___x_2342_);
v___x_2372_ = lean_unsigned_to_nat(1u);
v___x_2373_ = l_Lean_Syntax_getArg(v_docStx_2343_, v___x_2372_);
if (lean_obj_tag(v___x_2373_) == 1)
{
lean_object* v_kind_2374_; 
v_kind_2374_ = lean_ctor_get(v___x_2373_, 1);
lean_inc(v_kind_2374_);
if (lean_obj_tag(v_kind_2374_) == 1)
{
lean_object* v_pre_2375_; 
v_pre_2375_ = lean_ctor_get(v_kind_2374_, 0);
lean_inc(v_pre_2375_);
if (lean_obj_tag(v_pre_2375_) == 1)
{
lean_object* v_pre_2376_; 
v_pre_2376_ = lean_ctor_get(v_pre_2375_, 0);
lean_inc(v_pre_2376_);
if (lean_obj_tag(v_pre_2376_) == 1)
{
lean_object* v_pre_2377_; 
v_pre_2377_ = lean_ctor_get(v_pre_2376_, 0);
lean_inc(v_pre_2377_);
if (lean_obj_tag(v_pre_2377_) == 1)
{
lean_object* v_pre_2378_; 
v_pre_2378_ = lean_ctor_get(v_pre_2377_, 0);
if (lean_obj_tag(v_pre_2378_) == 0)
{
lean_object* v_str_2379_; lean_object* v_str_2380_; lean_object* v_str_2381_; lean_object* v_str_2382_; lean_object* v___x_2383_; uint8_t v___x_2384_; 
v_str_2379_ = lean_ctor_get(v_kind_2374_, 1);
lean_inc_ref(v_str_2379_);
lean_dec_ref_known(v_kind_2374_, 2);
v_str_2380_ = lean_ctor_get(v_pre_2375_, 1);
lean_inc_ref(v_str_2380_);
lean_dec_ref_known(v_pre_2375_, 2);
v_str_2381_ = lean_ctor_get(v_pre_2376_, 1);
lean_inc_ref(v_str_2381_);
lean_dec_ref_known(v_pre_2376_, 2);
v_str_2382_ = lean_ctor_get(v_pre_2377_, 1);
lean_inc_ref(v_str_2382_);
lean_dec_ref_known(v_pre_2377_, 2);
v___x_2383_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_MissingDocs_3645095946____hygCtx___hyg_4_));
v___x_2384_ = lean_string_dec_eq(v_str_2382_, v___x_2383_);
lean_dec_ref(v_str_2382_);
if (v___x_2384_ == 0)
{
lean_dec_ref(v_str_2381_);
lean_dec_ref(v_str_2380_);
lean_dec_ref(v_str_2379_);
lean_dec_ref_known(v___x_2373_, 3);
v___y_2345_ = v_a_2338_;
v___y_2346_ = v_a_2339_;
goto v___jp_2344_;
}
else
{
lean_object* v___x_2385_; uint8_t v___x_2386_; 
v___x_2385_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__2));
v___x_2386_ = lean_string_dec_eq(v_str_2381_, v___x_2385_);
lean_dec_ref(v_str_2381_);
if (v___x_2386_ == 0)
{
lean_dec_ref(v_str_2380_);
lean_dec_ref(v_str_2379_);
lean_dec_ref_known(v___x_2373_, 3);
v___y_2345_ = v_a_2338_;
v___y_2346_ = v_a_2339_;
goto v___jp_2344_;
}
else
{
lean_object* v___x_2387_; uint8_t v___x_2388_; 
v___x_2387_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__3));
v___x_2388_ = lean_string_dec_eq(v_str_2380_, v___x_2387_);
lean_dec_ref(v_str_2380_);
if (v___x_2388_ == 0)
{
lean_dec_ref(v_str_2379_);
lean_dec_ref_known(v___x_2373_, 3);
v___y_2345_ = v_a_2338_;
v___y_2346_ = v_a_2339_;
goto v___jp_2344_;
}
else
{
lean_object* v___x_2389_; uint8_t v___x_2390_; 
v___x_2389_ = ((lean_object*)(l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0___closed__4));
v___x_2390_ = lean_string_dec_eq(v_str_2379_, v___x_2389_);
lean_dec_ref(v_str_2379_);
if (v___x_2390_ == 0)
{
lean_dec_ref_known(v___x_2373_, 3);
v___y_2345_ = v_a_2338_;
v___y_2346_ = v_a_2339_;
goto v___jp_2344_;
}
else
{
lean_object* v___x_2391_; uint8_t v___x_2392_; 
v___x_2391_ = l_Lean_Syntax_getArg(v___x_2373_, v___x_2342_);
lean_dec_ref_known(v___x_2373_, 3);
v___x_2392_ = l_Lean_Syntax_isAtom(v___x_2391_);
lean_dec(v___x_2391_);
if (v___x_2392_ == 0)
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
lean_dec(v_docStx_2343_);
v___x_2393_ = lean_box(v___x_2341_);
v___x_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2393_);
return v___x_2394_;
}
else
{
if (v___x_2341_ == 0)
{
v___y_2345_ = v_a_2338_;
v___y_2346_ = v_a_2339_;
goto v___jp_2344_;
}
else
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
lean_dec(v_docStx_2343_);
v___x_2395_ = lean_box(v___x_2341_);
v___x_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2395_);
return v___x_2396_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_2377_, 2);
lean_dec_ref_known(v_pre_2376_, 2);
lean_dec_ref_known(v_pre_2375_, 2);
lean_dec_ref_known(v_kind_2374_, 2);
lean_dec_ref_known(v___x_2373_, 3);
v___y_2345_ = v_a_2338_;
v___y_2346_ = v_a_2339_;
goto v___jp_2344_;
}
}
else
{
lean_dec_ref_known(v_pre_2376_, 2);
lean_dec(v_pre_2377_);
lean_dec_ref_known(v_pre_2375_, 2);
lean_dec_ref_known(v_kind_2374_, 2);
lean_dec_ref_known(v___x_2373_, 3);
v___y_2345_ = v_a_2338_;
v___y_2346_ = v_a_2339_;
goto v___jp_2344_;
}
}
else
{
lean_dec(v_pre_2376_);
lean_dec_ref_known(v_pre_2375_, 2);
lean_dec_ref_known(v_kind_2374_, 2);
lean_dec_ref_known(v___x_2373_, 3);
v___y_2345_ = v_a_2338_;
v___y_2346_ = v_a_2339_;
goto v___jp_2344_;
}
}
else
{
lean_dec_ref_known(v_kind_2374_, 2);
lean_dec(v_pre_2375_);
lean_dec_ref_known(v___x_2373_, 3);
v___y_2345_ = v_a_2338_;
v___y_2346_ = v_a_2339_;
goto v___jp_2344_;
}
}
else
{
lean_dec(v_kind_2374_);
lean_dec_ref_known(v___x_2373_, 3);
v___y_2345_ = v_a_2338_;
v___y_2346_ = v_a_2339_;
goto v___jp_2344_;
}
}
else
{
lean_dec(v___x_2373_);
v___y_2345_ = v_a_2338_;
v___y_2346_ = v_a_2339_;
goto v___jp_2344_;
}
v___jp_2344_:
{
lean_object* v___x_2347_; 
v___x_2347_ = l_Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0(v_docStx_2343_, v___y_2345_, v___y_2346_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2363_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2350_ = v___x_2347_;
v_isShared_2351_ = v_isSharedCheck_2363_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2347_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2363_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v_startInclusive_2355_; lean_object* v_endExclusive_2356_; lean_object* v___x_2357_; uint8_t v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2361_; 
v___x_2352_ = lean_string_utf8_byte_size(v_a_2348_);
v___x_2353_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2353_, 0, v_a_2348_);
lean_ctor_set(v___x_2353_, 1, v___x_2342_);
lean_ctor_set(v___x_2353_, 2, v___x_2352_);
v___x_2354_ = l_String_Slice_trimAscii(v___x_2353_);
v_startInclusive_2355_ = lean_ctor_get(v___x_2354_, 1);
lean_inc(v_startInclusive_2355_);
v_endExclusive_2356_ = lean_ctor_get(v___x_2354_, 2);
lean_inc(v_endExclusive_2356_);
lean_dec_ref(v___x_2354_);
v___x_2357_ = lean_nat_sub(v_endExclusive_2356_, v_startInclusive_2355_);
lean_dec(v_startInclusive_2355_);
lean_dec(v_endExclusive_2356_);
v___x_2358_ = lean_nat_dec_eq(v___x_2357_, v___x_2342_);
lean_dec(v___x_2357_);
v___x_2359_ = lean_box(v___x_2358_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v___x_2359_);
v___x_2361_ = v___x_2350_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2359_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
v_a_2364_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2347_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2347_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
}
else
{
uint8_t v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2397_ = 0;
v___x_2398_ = lean_box(v___x_2397_);
v___x_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2398_);
return v___x_2399_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString___boxed(lean_object* v_docOpt_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString(v_docOpt_2400_, v_a_2401_, v_a_2402_);
lean_dec(v_a_2402_);
lean_dec_ref(v_a_2401_);
lean_dec(v_docOpt_2400_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0(lean_object* v_00_u03b1_2405_, lean_object* v_ref_2406_, lean_object* v_msg_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_){
_start:
{
lean_object* v___x_2411_; 
v___x_2411_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0___redArg(v_ref_2406_, v_msg_2407_, v___y_2408_, v___y_2409_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2412_, lean_object* v_ref_2413_, lean_object* v_msg_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0(v_00_u03b1_2412_, v_ref_2413_, v_msg_2414_, v___y_2415_, v___y_2416_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v_ref_2413_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2419_, lean_object* v_msg_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v___x_2424_; 
v___x_2424_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg(v_msg_2420_, v___y_2421_, v___y_2422_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2425_, lean_object* v_msg_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1(v_00_u03b1_2425_, v_msg_2426_, v___y_2427_, v___y_2428_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2(lean_object* v_msgData_2431_, lean_object* v_macroStack_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___redArg(v_msgData_2431_, v_macroStack_2432_, v___y_2434_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_msgData_2437_, lean_object* v_macroStack_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1_spec__2(v_msgData_2437_, v_macroStack_2438_, v___y_2439_, v___y_2440_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_isMissingDoc(lean_object* v_docOpt_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_){
_start:
{
lean_object* v___x_2447_; 
v___x_2447_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString(v_docOpt_2443_, v_a_2444_, v_a_2445_);
if (lean_obj_tag(v___x_2447_) == 0)
{
uint8_t v___x_2448_; 
v___x_2448_ = l_Lean_Syntax_isNone(v_docOpt_2443_);
if (v___x_2448_ == 0)
{
return v___x_2447_;
}
else
{
lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2456_; 
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2456_ == 0)
{
lean_object* v_unused_2457_; 
v_unused_2457_ = lean_ctor_get(v___x_2447_, 0);
lean_dec(v_unused_2457_);
v___x_2450_ = v___x_2447_;
v_isShared_2451_ = v_isSharedCheck_2456_;
goto v_resetjp_2449_;
}
else
{
lean_dec(v___x_2447_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2456_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2452_; lean_object* v___x_2454_; 
v___x_2452_ = lean_box(v___x_2448_);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 0, v___x_2452_);
v___x_2454_ = v___x_2450_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v___x_2452_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
else
{
return v___x_2447_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_isMissingDoc___boxed(lean_object* v_docOpt_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l_Lean_Linter_MissingDocs_isMissingDoc(v_docOpt_2458_, v_a_2459_, v_a_2460_);
lean_dec(v_a_2460_);
lean_dec_ref(v_a_2459_);
lean_dec(v_docOpt_2458_);
return v_res_2462_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0(lean_object* v_as_2473_, size_t v_i_2474_, size_t v_stop_2475_){
_start:
{
uint8_t v___x_2476_; 
v___x_2476_ = lean_usize_dec_eq(v_i_2474_, v_stop_2475_);
if (v___x_2476_ == 0)
{
lean_object* v___x_2477_; uint8_t v___x_2478_; uint8_t v___y_2480_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; uint8_t v___x_2487_; 
v___x_2477_ = lean_unsigned_to_nat(1u);
v___x_2478_ = 1;
v___x_2484_ = lean_array_uget_borrowed(v_as_2473_, v_i_2474_);
v___x_2485_ = l_Lean_Syntax_getArg(v___x_2484_, v___x_2477_);
v___x_2486_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__2));
lean_inc(v___x_2485_);
v___x_2487_ = l_Lean_Syntax_isOfKind(v___x_2485_, v___x_2486_);
if (v___x_2487_ == 0)
{
lean_dec(v___x_2485_);
v___y_2480_ = v___x_2487_;
goto v___jp_2479_;
}
else
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; uint8_t v___x_2493_; 
v___x_2488_ = lean_unsigned_to_nat(0u);
v___x_2489_ = l_Lean_Syntax_getArg(v___x_2485_, v___x_2488_);
lean_dec(v___x_2485_);
v___x_2490_ = l_Lean_Syntax_getId(v___x_2489_);
lean_dec(v___x_2489_);
v___x_2491_ = l_Lean_Name_eraseMacroScopes(v___x_2490_);
lean_dec(v___x_2490_);
v___x_2492_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___closed__4));
v___x_2493_ = lean_name_eq(v___x_2491_, v___x_2492_);
lean_dec(v___x_2491_);
v___y_2480_ = v___x_2493_;
goto v___jp_2479_;
}
v___jp_2479_:
{
if (v___y_2480_ == 0)
{
size_t v___x_2481_; size_t v___x_2482_; 
v___x_2481_ = ((size_t)1ULL);
v___x_2482_ = lean_usize_add(v_i_2474_, v___x_2481_);
v_i_2474_ = v___x_2482_;
goto _start;
}
else
{
return v___x_2478_;
}
}
}
else
{
uint8_t v___x_2494_; 
v___x_2494_ = 0;
return v___x_2494_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0___boxed(lean_object* v_as_2495_, lean_object* v_i_2496_, lean_object* v_stop_2497_){
_start:
{
size_t v_i_boxed_2498_; size_t v_stop_boxed_2499_; uint8_t v_res_2500_; lean_object* v_r_2501_; 
v_i_boxed_2498_ = lean_unbox_usize(v_i_2496_);
lean_dec(v_i_2496_);
v_stop_boxed_2499_ = lean_unbox_usize(v_stop_2497_);
lean_dec(v_stop_2497_);
v_res_2500_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0(v_as_2495_, v_i_boxed_2498_, v_stop_boxed_2499_);
lean_dec_ref(v_as_2495_);
v_r_2501_ = lean_box(v_res_2500_);
return v_r_2501_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_MissingDocs_hasInheritDoc(lean_object* v_attrs_2502_){
_start:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; uint8_t v___x_2509_; 
v___x_2503_ = lean_unsigned_to_nat(0u);
v___x_2504_ = l_Lean_Syntax_getArg(v_attrs_2502_, v___x_2503_);
v___x_2505_ = lean_unsigned_to_nat(1u);
v___x_2506_ = l_Lean_Syntax_getArg(v___x_2504_, v___x_2505_);
lean_dec(v___x_2504_);
v___x_2507_ = l_Lean_Syntax_getSepArgs(v___x_2506_);
lean_dec(v___x_2506_);
v___x_2508_ = lean_array_get_size(v___x_2507_);
v___x_2509_ = lean_nat_dec_lt(v___x_2503_, v___x_2508_);
if (v___x_2509_ == 0)
{
lean_dec_ref(v___x_2507_);
return v___x_2509_;
}
else
{
if (v___x_2509_ == 0)
{
lean_dec_ref(v___x_2507_);
return v___x_2509_;
}
else
{
size_t v___x_2510_; size_t v___x_2511_; uint8_t v___x_2512_; 
v___x_2510_ = ((size_t)0ULL);
v___x_2511_ = lean_usize_of_nat(v___x_2508_);
v___x_2512_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasInheritDoc_spec__0(v___x_2507_, v___x_2510_, v___x_2511_);
lean_dec_ref(v___x_2507_);
return v___x_2512_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_hasInheritDoc___boxed(lean_object* v_attrs_2513_){
_start:
{
uint8_t v_res_2514_; lean_object* v_r_2515_; 
v_res_2514_ = l_Lean_Linter_MissingDocs_hasInheritDoc(v_attrs_2513_);
lean_dec(v_attrs_2513_);
v_r_2515_ = lean_box(v_res_2514_);
return v_r_2515_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0(lean_object* v_as_2522_, size_t v_i_2523_, size_t v_stop_2524_){
_start:
{
uint8_t v___x_2525_; 
v___x_2525_ = lean_usize_dec_eq(v_i_2523_, v_stop_2524_);
if (v___x_2525_ == 0)
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; uint8_t v___x_2530_; 
v___x_2526_ = lean_unsigned_to_nat(1u);
v___x_2527_ = lean_array_uget_borrowed(v_as_2522_, v_i_2523_);
v___x_2528_ = l_Lean_Syntax_getArg(v___x_2527_, v___x_2526_);
v___x_2529_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0___closed__1));
v___x_2530_ = l_Lean_Syntax_isOfKind(v___x_2528_, v___x_2529_);
if (v___x_2530_ == 0)
{
size_t v___x_2531_; size_t v___x_2532_; 
v___x_2531_ = ((size_t)1ULL);
v___x_2532_ = lean_usize_add(v_i_2523_, v___x_2531_);
v_i_2523_ = v___x_2532_;
goto _start;
}
else
{
return v___x_2530_;
}
}
else
{
uint8_t v___x_2534_; 
v___x_2534_ = 0;
return v___x_2534_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0___boxed(lean_object* v_as_2535_, lean_object* v_i_2536_, lean_object* v_stop_2537_){
_start:
{
size_t v_i_boxed_2538_; size_t v_stop_boxed_2539_; uint8_t v_res_2540_; lean_object* v_r_2541_; 
v_i_boxed_2538_ = lean_unbox_usize(v_i_2536_);
lean_dec(v_i_2536_);
v_stop_boxed_2539_ = lean_unbox_usize(v_stop_2537_);
lean_dec(v_stop_2537_);
v_res_2540_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0(v_as_2535_, v_i_boxed_2538_, v_stop_boxed_2539_);
lean_dec_ref(v_as_2535_);
v_r_2541_ = lean_box(v_res_2540_);
return v_r_2541_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_MissingDocs_hasTacticAlt(lean_object* v_attrs_2542_){
_start:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; uint8_t v___x_2549_; 
v___x_2543_ = lean_unsigned_to_nat(0u);
v___x_2544_ = l_Lean_Syntax_getArg(v_attrs_2542_, v___x_2543_);
v___x_2545_ = lean_unsigned_to_nat(1u);
v___x_2546_ = l_Lean_Syntax_getArg(v___x_2544_, v___x_2545_);
lean_dec(v___x_2544_);
v___x_2547_ = l_Lean_Syntax_getSepArgs(v___x_2546_);
lean_dec(v___x_2546_);
v___x_2548_ = lean_array_get_size(v___x_2547_);
v___x_2549_ = lean_nat_dec_lt(v___x_2543_, v___x_2548_);
if (v___x_2549_ == 0)
{
lean_dec_ref(v___x_2547_);
return v___x_2549_;
}
else
{
if (v___x_2549_ == 0)
{
lean_dec_ref(v___x_2547_);
return v___x_2549_;
}
else
{
size_t v___x_2550_; size_t v___x_2551_; uint8_t v___x_2552_; 
v___x_2550_ = ((size_t)0ULL);
v___x_2551_ = lean_usize_of_nat(v___x_2548_);
v___x_2552_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_MissingDocs_hasTacticAlt_spec__0(v___x_2547_, v___x_2550_, v___x_2551_);
lean_dec_ref(v___x_2547_);
return v___x_2552_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_hasTacticAlt___boxed(lean_object* v_attrs_2553_){
_start:
{
uint8_t v_res_2554_; lean_object* v_r_2555_; 
v_res_2554_ = l_Lean_Linter_MissingDocs_hasTacticAlt(v_attrs_2553_);
lean_dec(v_attrs_2553_);
v_r_2555_ = lean_box(v_res_2554_);
return v_r_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_declModifiersDocStatus(lean_object* v_mods_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_){
_start:
{
lean_object* v___x_2570_; lean_object* v_env_2571_; lean_object* v___x_2572_; 
v___x_2570_ = lean_st_ref_get(v_a_2568_);
v_env_2571_ = lean_ctor_get(v___x_2570_, 0);
lean_inc_ref(v_env_2571_);
lean_dec(v___x_2570_);
v___x_2572_ = l_Lean_Elab_Command_getScope___redArg(v_a_2568_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2636_; 
v_a_2573_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2575_ = v___x_2572_;
v_isShared_2576_ = v_isSharedCheck_2636_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2572_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2636_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
uint8_t v___y_2583_; lean_object* v___x_2626_; uint8_t v_isModule_2627_; 
v___x_2626_ = l_Lean_Environment_header(v_env_2571_);
lean_dec_ref(v_env_2571_);
v_isModule_2627_ = lean_ctor_get_uint8(v___x_2626_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_2626_);
if (v_isModule_2627_ == 0)
{
lean_dec(v_a_2573_);
goto v___jp_2617_;
}
else
{
uint8_t v_isPublic_2628_; 
v_isPublic_2628_ = lean_ctor_get_uint8(v_a_2573_, sizeof(void*)*10 + 1);
lean_dec(v_a_2573_);
if (v_isPublic_2628_ == 0)
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; uint8_t v___x_2635_; 
v___x_2629_ = lean_unsigned_to_nat(2u);
v___x_2630_ = l_Lean_Syntax_getArg(v_mods_2566_, v___x_2629_);
v___x_2631_ = lean_unsigned_to_nat(0u);
v___x_2632_ = l_Lean_Syntax_getArg(v___x_2630_, v___x_2631_);
lean_dec(v___x_2630_);
v___x_2633_ = l_Lean_Syntax_getKind(v___x_2632_);
v___x_2634_ = ((lean_object*)(l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__1));
v___x_2635_ = lean_name_eq(v___x_2633_, v___x_2634_);
lean_dec(v___x_2633_);
if (v___x_2635_ == 0)
{
goto v___jp_2577_;
}
else
{
v___y_2583_ = v_isModule_2627_;
goto v___jp_2582_;
}
}
else
{
goto v___jp_2617_;
}
}
v___jp_2577_:
{
lean_object* v___x_2578_; lean_object* v___x_2580_; 
v___x_2578_ = lean_box(0);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 0, v___x_2578_);
v___x_2580_ = v___x_2575_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2578_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
v___jp_2582_:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; uint8_t v___x_2586_; 
v___x_2584_ = lean_unsigned_to_nat(1u);
v___x_2585_ = l_Lean_Syntax_getArg(v_mods_2566_, v___x_2584_);
v___x_2586_ = l_Lean_Linter_MissingDocs_hasInheritDoc(v___x_2585_);
lean_dec(v___x_2585_);
if (v___x_2586_ == 0)
{
lean_object* v___x_2587_; lean_object* v___x_2588_; uint8_t v___x_2589_; 
lean_del_object(v___x_2575_);
v___x_2587_ = lean_unsigned_to_nat(0u);
v___x_2588_ = l_Lean_Syntax_getArg(v_mods_2566_, v___x_2587_);
v___x_2589_ = l_Lean_Syntax_isNone(v___x_2588_);
if (v___x_2589_ == 0)
{
lean_object* v___x_2590_; 
v___x_2590_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString(v___x_2588_, v_a_2567_, v_a_2568_);
lean_dec(v___x_2588_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2605_; 
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2593_ = v___x_2590_;
v_isShared_2594_ = v_isSharedCheck_2605_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2590_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2605_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
uint8_t v___x_2595_; 
v___x_2595_ = lean_unbox(v_a_2591_);
lean_dec(v_a_2591_);
if (v___x_2595_ == 0)
{
lean_object* v___x_2596_; lean_object* v___x_2598_; 
v___x_2596_ = lean_box(0);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 0, v___x_2596_);
v___x_2598_ = v___x_2593_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2596_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
else
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2603_; 
v___x_2600_ = lean_box(v___y_2583_);
v___x_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 0, v___x_2601_);
v___x_2603_ = v___x_2593_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2601_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
else
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2613_; 
v_a_2606_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2590_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2590_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2606_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
else
{
lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
lean_dec(v___x_2588_);
v___x_2614_ = lean_box(v___x_2586_);
v___x_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2614_);
v___x_2616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2615_);
return v___x_2616_;
}
}
else
{
goto v___jp_2577_;
}
}
v___jp_2617_:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; uint8_t v___x_2624_; 
v___x_2618_ = lean_unsigned_to_nat(2u);
v___x_2619_ = l_Lean_Syntax_getArg(v_mods_2566_, v___x_2618_);
v___x_2620_ = lean_unsigned_to_nat(0u);
v___x_2621_ = l_Lean_Syntax_getArg(v___x_2619_, v___x_2620_);
lean_dec(v___x_2619_);
v___x_2622_ = l_Lean_Syntax_getKind(v___x_2621_);
v___x_2623_ = ((lean_object*)(l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__0));
v___x_2624_ = lean_name_eq(v___x_2622_, v___x_2623_);
lean_dec(v___x_2622_);
if (v___x_2624_ == 0)
{
uint8_t v___x_2625_; 
v___x_2625_ = 1;
v___y_2583_ = v___x_2625_;
goto v___jp_2582_;
}
else
{
goto v___jp_2577_;
}
}
}
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
lean_dec_ref(v_env_2571_);
v_a_2637_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2572_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2572_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_declModifiersDocStatus___boxed(lean_object* v_mods_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v_mods_2645_, v_a_2646_, v_a_2647_);
lean_dec(v_a_2647_);
lean_dec_ref(v_a_2646_);
lean_dec(v_mods_2645_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_declModifiersPubNoDoc(lean_object* v_mods_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_){
_start:
{
lean_object* v___x_2654_; 
v___x_2654_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v_mods_2650_, v_a_2651_, v_a_2652_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2669_; 
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2657_ = v___x_2654_;
v_isShared_2658_ = v_isSharedCheck_2669_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_a_2655_);
lean_dec(v___x_2654_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2669_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
if (lean_obj_tag(v_a_2655_) == 0)
{
uint8_t v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2662_; 
v___x_2659_ = 0;
v___x_2660_ = lean_box(v___x_2659_);
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 0, v___x_2660_);
v___x_2662_ = v___x_2657_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2660_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
else
{
uint8_t v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2667_; 
lean_dec_ref_known(v_a_2655_, 1);
v___x_2664_ = 1;
v___x_2665_ = lean_box(v___x_2664_);
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 0, v___x_2665_);
v___x_2667_ = v___x_2657_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v___x_2665_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
}
else
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2677_; 
v_a_2670_ = lean_ctor_get(v___x_2654_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2672_ = v___x_2654_;
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2654_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2670_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_declModifiersPubNoDoc___boxed(lean_object* v_mods_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_){
_start:
{
lean_object* v_res_2682_; 
v_res_2682_ = l_Lean_Linter_MissingDocs_declModifiersPubNoDoc(v_mods_2678_, v_a_2679_, v_a_2680_);
lean_dec(v_a_2680_);
lean_dec_ref(v_a_2679_);
lean_dec(v_mods_2678_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus(uint8_t v_isEmpty_2683_, lean_object* v_stx_2684_, lean_object* v_msg_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_){
_start:
{
if (v_isEmpty_2683_ == 0)
{
lean_object* v___x_2689_; 
v___x_2689_ = l_Lean_Linter_MissingDocs_lint(v_stx_2684_, v_msg_2685_, v_a_2686_, v_a_2687_);
return v___x_2689_;
}
else
{
lean_object* v___x_2690_; 
v___x_2690_ = l_Lean_Linter_MissingDocs_lintEmpty(v_stx_2684_, v_msg_2685_, v_a_2686_, v_a_2687_);
return v___x_2690_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus___boxed(lean_object* v_isEmpty_2691_, lean_object* v_stx_2692_, lean_object* v_msg_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_){
_start:
{
uint8_t v_isEmpty_boxed_2697_; lean_object* v_res_2698_; 
v_isEmpty_boxed_2697_ = lean_unbox(v_isEmpty_2691_);
v_res_2698_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus(v_isEmpty_boxed_2697_, v_stx_2692_, v_msg_2693_, v_a_2694_, v_a_2695_);
lean_dec(v_a_2695_);
lean_dec_ref(v_a_2694_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(uint8_t v_isEmpty_2699_, lean_object* v_stx_2700_, lean_object* v_msg_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_){
_start:
{
if (v_isEmpty_2699_ == 0)
{
lean_object* v___x_2705_; 
v___x_2705_ = l_Lean_Linter_MissingDocs_lintNamed(v_stx_2700_, v_msg_2701_, v_a_2702_, v_a_2703_);
return v___x_2705_;
}
else
{
lean_object* v___x_2706_; 
v___x_2706_ = l_Lean_Linter_MissingDocs_lintEmptyNamed(v_stx_2700_, v_msg_2701_, v_a_2702_, v_a_2703_);
return v___x_2706_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed___boxed(lean_object* v_isEmpty_2707_, lean_object* v_stx_2708_, lean_object* v_msg_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_){
_start:
{
uint8_t v_isEmpty_boxed_2713_; lean_object* v_res_2714_; 
v_isEmpty_boxed_2713_ = lean_unbox(v_isEmpty_2707_);
v_res_2714_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v_isEmpty_boxed_2713_, v_stx_2708_, v_msg_2709_, v_a_2710_, v_a_2711_);
lean_dec(v_a_2711_);
lean_dec_ref(v_a_2710_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(uint8_t v_isEmpty_2715_, lean_object* v_parent_2716_, lean_object* v_stx_2717_, lean_object* v_msg_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_){
_start:
{
if (v_isEmpty_2715_ == 0)
{
lean_object* v___x_2722_; 
v___x_2722_ = l_Lean_Linter_MissingDocs_lintField(v_parent_2716_, v_stx_2717_, v_msg_2718_, v_a_2719_, v_a_2720_);
return v___x_2722_;
}
else
{
lean_object* v___x_2723_; 
v___x_2723_ = l_Lean_Linter_MissingDocs_lintEmptyField(v_parent_2716_, v_stx_2717_, v_msg_2718_, v_a_2719_, v_a_2720_);
return v___x_2723_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField___boxed(lean_object* v_isEmpty_2724_, lean_object* v_parent_2725_, lean_object* v_stx_2726_, lean_object* v_msg_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_){
_start:
{
uint8_t v_isEmpty_boxed_2731_; lean_object* v_res_2732_; 
v_isEmpty_boxed_2731_ = lean_unbox(v_isEmpty_2724_);
v_res_2732_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(v_isEmpty_boxed_2731_, v_parent_2725_, v_stx_2726_, v_msg_2727_, v_a_2728_, v_a_2729_);
lean_dec(v_a_2729_);
lean_dec_ref(v_a_2728_);
lean_dec(v_parent_2725_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintDeclHead(lean_object* v_k_2781_, lean_object* v_id_2782_, uint8_t v_isEmpty_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_){
_start:
{
lean_object* v___x_2787_; uint8_t v___x_2788_; 
v___x_2787_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__1));
v___x_2788_ = lean_name_eq(v_k_2781_, v___x_2787_);
if (v___x_2788_ == 0)
{
lean_object* v___x_2789_; uint8_t v___x_2790_; 
v___x_2789_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__3));
v___x_2790_ = lean_name_eq(v_k_2781_, v___x_2789_);
if (v___x_2790_ == 0)
{
lean_object* v___x_2791_; uint8_t v___x_2792_; 
v___x_2791_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__5));
v___x_2792_ = lean_name_eq(v_k_2781_, v___x_2791_);
if (v___x_2792_ == 0)
{
lean_object* v___x_2793_; uint8_t v___x_2794_; 
v___x_2793_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__7));
v___x_2794_ = lean_name_eq(v_k_2781_, v___x_2793_);
if (v___x_2794_ == 0)
{
lean_object* v___x_2795_; uint8_t v___x_2796_; 
v___x_2795_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__9));
v___x_2796_ = lean_name_eq(v_k_2781_, v___x_2795_);
if (v___x_2796_ == 0)
{
lean_object* v___x_2797_; uint8_t v___x_2798_; 
v___x_2797_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__11));
v___x_2798_ = lean_name_eq(v_k_2781_, v___x_2797_);
if (v___x_2798_ == 0)
{
lean_object* v___x_2799_; uint8_t v___x_2800_; 
v___x_2799_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__13));
v___x_2800_ = lean_name_eq(v_k_2781_, v___x_2799_);
if (v___x_2800_ == 0)
{
lean_object* v___x_2801_; lean_object* v___x_2802_; 
lean_dec(v_id_2782_);
v___x_2801_ = lean_box(0);
v___x_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2801_);
return v___x_2802_;
}
else
{
lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2803_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__14));
v___x_2804_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v_isEmpty_2783_, v_id_2782_, v___x_2803_, v_a_2784_, v_a_2785_);
return v___x_2804_;
}
}
else
{
lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2805_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__15));
v___x_2806_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v_isEmpty_2783_, v_id_2782_, v___x_2805_, v_a_2784_, v_a_2785_);
return v___x_2806_;
}
}
else
{
lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2807_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__15));
v___x_2808_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v_isEmpty_2783_, v_id_2782_, v___x_2807_, v_a_2784_, v_a_2785_);
return v___x_2808_;
}
}
else
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2809_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__16));
v___x_2810_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v_isEmpty_2783_, v_id_2782_, v___x_2809_, v_a_2784_, v_a_2785_);
return v___x_2810_;
}
}
else
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2811_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__17));
v___x_2812_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v_isEmpty_2783_, v_id_2782_, v___x_2811_, v_a_2784_, v_a_2785_);
return v___x_2812_;
}
}
else
{
lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2813_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__18));
v___x_2814_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v_isEmpty_2783_, v_id_2782_, v___x_2813_, v_a_2784_, v_a_2785_);
return v___x_2814_;
}
}
else
{
lean_object* v___x_2815_; lean_object* v___x_2816_; 
v___x_2815_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__19));
v___x_2816_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v_isEmpty_2783_, v_id_2782_, v___x_2815_, v_a_2784_, v_a_2785_);
return v___x_2816_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_lintDeclHead___boxed(lean_object* v_k_2817_, lean_object* v_id_2818_, lean_object* v_isEmpty_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_){
_start:
{
uint8_t v_isEmpty_boxed_2823_; lean_object* v_res_2824_; 
v_isEmpty_boxed_2823_ = lean_unbox(v_isEmpty_2819_);
v_res_2824_ = l_Lean_Linter_MissingDocs_lintDeclHead(v_k_2817_, v_id_2818_, v_isEmpty_boxed_2823_, v_a_2820_, v_a_2821_);
lean_dec(v_a_2821_);
lean_dec_ref(v_a_2820_);
lean_dec(v_k_2817_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus(lean_object* v_docOpt_2828_, lean_object* v_attrs_2829_, uint8_t v_checkTacticAlt_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_){
_start:
{
uint8_t v___x_2834_; 
v___x_2834_ = l_Lean_Linter_MissingDocs_hasInheritDoc(v_attrs_2829_);
if (v___x_2834_ == 0)
{
uint8_t v___y_2836_; 
if (v_checkTacticAlt_2830_ == 0)
{
v___y_2836_ = v___x_2834_;
goto v___jp_2835_;
}
else
{
uint8_t v___x_2866_; 
v___x_2866_ = l_Lean_Linter_MissingDocs_hasTacticAlt(v_attrs_2829_);
v___y_2836_ = v___x_2866_;
goto v___jp_2835_;
}
v___jp_2835_:
{
if (v___y_2836_ == 0)
{
uint8_t v___x_2837_; 
v___x_2837_ = l_Lean_Syntax_isNone(v_docOpt_2828_);
if (v___x_2837_ == 0)
{
lean_object* v___x_2838_; 
v___x_2838_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString(v_docOpt_2828_, v_a_2831_, v_a_2832_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2852_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2841_ = v___x_2838_;
v_isShared_2842_ = v_isSharedCheck_2852_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2838_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2852_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
uint8_t v___x_2843_; 
v___x_2843_ = lean_unbox(v_a_2839_);
lean_dec(v_a_2839_);
if (v___x_2843_ == 0)
{
lean_object* v___x_2844_; lean_object* v___x_2846_; 
v___x_2844_ = lean_box(0);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 0, v___x_2844_);
v___x_2846_ = v___x_2841_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v___x_2844_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
else
{
lean_object* v___x_2848_; lean_object* v___x_2850_; 
v___x_2848_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus___closed__0));
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 0, v___x_2848_);
v___x_2850_ = v___x_2841_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v___x_2848_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
}
else
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2860_; 
v_a_2853_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2855_ = v___x_2838_;
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2838_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2860_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2858_; 
if (v_isShared_2856_ == 0)
{
v___x_2858_ = v___x_2855_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2853_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
}
else
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
v___x_2861_ = lean_box(v___y_2836_);
v___x_2862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2861_);
v___x_2863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2862_);
return v___x_2863_;
}
}
else
{
lean_object* v___x_2864_; lean_object* v___x_2865_; 
v___x_2864_ = lean_box(0);
v___x_2865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2864_);
return v___x_2865_;
}
}
}
else
{
lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2867_ = lean_box(0);
v___x_2868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2867_);
return v___x_2868_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus___boxed(lean_object* v_docOpt_2869_, lean_object* v_attrs_2870_, lean_object* v_checkTacticAlt_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_){
_start:
{
uint8_t v_checkTacticAlt_boxed_2875_; lean_object* v_res_2876_; 
v_checkTacticAlt_boxed_2875_ = lean_unbox(v_checkTacticAlt_2871_);
v_res_2876_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus(v_docOpt_2869_, v_attrs_2870_, v_checkTacticAlt_boxed_2875_, v_a_2872_, v_a_2873_);
lean_dec(v_a_2873_);
lean_dec_ref(v_a_2872_);
lean_dec(v_attrs_2870_);
lean_dec(v_docOpt_2869_);
return v_res_2876_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__1(lean_object* v_rest_2878_, lean_object* v_as_2879_, size_t v_sz_2880_, size_t v_i_2881_, lean_object* v_b_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
lean_object* v_a_2887_; uint8_t v___x_2891_; 
v___x_2891_ = lean_usize_dec_lt(v_i_2881_, v_sz_2880_);
if (v___x_2891_ == 0)
{
lean_object* v___x_2892_; 
v___x_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2892_, 0, v_b_2882_);
return v___x_2892_;
}
else
{
lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v_a_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2893_ = lean_unsigned_to_nat(0u);
v___x_2894_ = lean_unsigned_to_nat(1u);
v___x_2895_ = lean_box(0);
v_a_2896_ = lean_array_uget_borrowed(v_as_2879_, v_i_2881_);
v___x_2897_ = l_Lean_Syntax_getArg(v_a_2896_, v___x_2893_);
v___x_2898_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v___x_2897_, v___y_2883_, v___y_2884_);
lean_dec(v___x_2897_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v_a_2899_; 
v_a_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc(v_a_2899_);
lean_dec_ref_known(v___x_2898_, 1);
if (lean_obj_tag(v_a_2899_) == 1)
{
lean_object* v_val_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; uint8_t v___x_2905_; lean_object* v___x_2906_; 
v_val_2900_ = lean_ctor_get(v_a_2899_, 0);
lean_inc(v_val_2900_);
lean_dec_ref_known(v_a_2899_, 1);
v___x_2901_ = l_Lean_Syntax_getArg(v_rest_2878_, v___x_2894_);
v___x_2902_ = l_Lean_Syntax_getArg(v___x_2901_, v___x_2893_);
lean_dec(v___x_2901_);
v___x_2903_ = l_Lean_Syntax_getArg(v_a_2896_, v___x_2894_);
v___x_2904_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__1___closed__0));
v___x_2905_ = lean_unbox(v_val_2900_);
lean_dec(v_val_2900_);
v___x_2906_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(v___x_2905_, v___x_2902_, v___x_2903_, v___x_2904_, v___y_2883_, v___y_2884_);
lean_dec(v___x_2902_);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_dec_ref_known(v___x_2906_, 1);
v_a_2887_ = v___x_2895_;
goto v___jp_2886_;
}
else
{
return v___x_2906_;
}
}
else
{
lean_dec(v_a_2899_);
v_a_2887_ = v___x_2895_;
goto v___jp_2886_;
}
}
else
{
lean_object* v_a_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2914_; 
v_a_2907_ = lean_ctor_get(v___x_2898_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2909_ = v___x_2898_;
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_a_2907_);
lean_dec(v___x_2898_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2912_; 
if (v_isShared_2910_ == 0)
{
v___x_2912_ = v___x_2909_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2907_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
}
v___jp_2886_:
{
size_t v___x_2888_; size_t v___x_2889_; 
v___x_2888_ = ((size_t)1ULL);
v___x_2889_ = lean_usize_add(v_i_2881_, v___x_2888_);
v_i_2881_ = v___x_2889_;
v_b_2882_ = v_a_2887_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__1___boxed(lean_object* v_rest_2915_, lean_object* v_as_2916_, lean_object* v_sz_2917_, lean_object* v_i_2918_, lean_object* v_b_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
size_t v_sz_boxed_2923_; size_t v_i_boxed_2924_; lean_object* v_res_2925_; 
v_sz_boxed_2923_ = lean_unbox_usize(v_sz_2917_);
lean_dec(v_sz_2917_);
v_i_boxed_2924_ = lean_unbox_usize(v_i_2918_);
lean_dec(v_i_2918_);
v_res_2925_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__1(v_rest_2915_, v_as_2916_, v_sz_boxed_2923_, v_i_boxed_2924_, v_b_2919_, v___y_2920_, v___y_2921_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec_ref(v_as_2916_);
lean_dec(v_rest_2915_);
return v_res_2925_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4_spec__9___redArg(lean_object* v_x_2926_, lean_object* v_x_2927_){
_start:
{
if (lean_obj_tag(v_x_2927_) == 0)
{
return v_x_2926_;
}
else
{
lean_object* v_key_2928_; lean_object* v_value_2929_; lean_object* v_tail_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2953_; 
v_key_2928_ = lean_ctor_get(v_x_2927_, 0);
v_value_2929_ = lean_ctor_get(v_x_2927_, 1);
v_tail_2930_ = lean_ctor_get(v_x_2927_, 2);
v_isSharedCheck_2953_ = !lean_is_exclusive(v_x_2927_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2932_ = v_x_2927_;
v_isShared_2933_ = v_isSharedCheck_2953_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_tail_2930_);
lean_inc(v_value_2929_);
lean_inc(v_key_2928_);
lean_dec(v_x_2927_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2953_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2934_; uint64_t v___x_2935_; uint64_t v___x_2936_; uint64_t v___x_2937_; uint64_t v_fold_2938_; uint64_t v___x_2939_; uint64_t v___x_2940_; uint64_t v___x_2941_; size_t v___x_2942_; size_t v___x_2943_; size_t v___x_2944_; size_t v___x_2945_; size_t v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2949_; 
v___x_2934_ = lean_array_get_size(v_x_2926_);
v___x_2935_ = l_String_instHashableRaw_hash(v_key_2928_);
v___x_2936_ = 32ULL;
v___x_2937_ = lean_uint64_shift_right(v___x_2935_, v___x_2936_);
v_fold_2938_ = lean_uint64_xor(v___x_2935_, v___x_2937_);
v___x_2939_ = 16ULL;
v___x_2940_ = lean_uint64_shift_right(v_fold_2938_, v___x_2939_);
v___x_2941_ = lean_uint64_xor(v_fold_2938_, v___x_2940_);
v___x_2942_ = lean_uint64_to_usize(v___x_2941_);
v___x_2943_ = lean_usize_of_nat(v___x_2934_);
v___x_2944_ = ((size_t)1ULL);
v___x_2945_ = lean_usize_sub(v___x_2943_, v___x_2944_);
v___x_2946_ = lean_usize_land(v___x_2942_, v___x_2945_);
v___x_2947_ = lean_array_uget_borrowed(v_x_2926_, v___x_2946_);
lean_inc(v___x_2947_);
if (v_isShared_2933_ == 0)
{
lean_ctor_set(v___x_2932_, 2, v___x_2947_);
v___x_2949_ = v___x_2932_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_key_2928_);
lean_ctor_set(v_reuseFailAlloc_2952_, 1, v_value_2929_);
lean_ctor_set(v_reuseFailAlloc_2952_, 2, v___x_2947_);
v___x_2949_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
lean_object* v___x_2950_; 
v___x_2950_ = lean_array_uset(v_x_2926_, v___x_2946_, v___x_2949_);
v_x_2926_ = v___x_2950_;
v_x_2927_ = v_tail_2930_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4___redArg(lean_object* v_i_2954_, lean_object* v_source_2955_, lean_object* v_target_2956_){
_start:
{
lean_object* v___x_2957_; uint8_t v___x_2958_; 
v___x_2957_ = lean_array_get_size(v_source_2955_);
v___x_2958_ = lean_nat_dec_lt(v_i_2954_, v___x_2957_);
if (v___x_2958_ == 0)
{
lean_dec_ref(v_source_2955_);
lean_dec(v_i_2954_);
return v_target_2956_;
}
else
{
lean_object* v_es_2959_; lean_object* v___x_2960_; lean_object* v_source_2961_; lean_object* v_target_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v_es_2959_ = lean_array_fget(v_source_2955_, v_i_2954_);
v___x_2960_ = lean_box(0);
v_source_2961_ = lean_array_fset(v_source_2955_, v_i_2954_, v___x_2960_);
v_target_2962_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4_spec__9___redArg(v_target_2956_, v_es_2959_);
v___x_2963_ = lean_unsigned_to_nat(1u);
v___x_2964_ = lean_nat_add(v_i_2954_, v___x_2963_);
lean_dec(v_i_2954_);
v_i_2954_ = v___x_2964_;
v_source_2955_ = v_source_2961_;
v_target_2956_ = v_target_2962_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3___redArg(lean_object* v_data_2966_){
_start:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v_nbuckets_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2967_ = lean_array_get_size(v_data_2966_);
v___x_2968_ = lean_unsigned_to_nat(2u);
v_nbuckets_2969_ = lean_nat_mul(v___x_2967_, v___x_2968_);
v___x_2970_ = lean_unsigned_to_nat(0u);
v___x_2971_ = lean_box(0);
v___x_2972_ = lean_mk_array(v_nbuckets_2969_, v___x_2971_);
v___x_2973_ = lean_array_propagate_mark(v_data_2966_, v___x_2972_);
v___x_2974_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4___redArg(v___x_2970_, v_data_2966_, v___x_2973_);
return v___x_2974_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2___redArg(lean_object* v_a_2975_, lean_object* v_x_2976_){
_start:
{
if (lean_obj_tag(v_x_2976_) == 0)
{
uint8_t v___x_2977_; 
v___x_2977_ = 0;
return v___x_2977_;
}
else
{
lean_object* v_key_2978_; lean_object* v_tail_2979_; uint8_t v_decide_2980_; 
v_key_2978_ = lean_ctor_get(v_x_2976_, 0);
v_tail_2979_ = lean_ctor_get(v_x_2976_, 2);
v_decide_2980_ = lean_nat_dec_eq(v_key_2978_, v_a_2975_);
if (v_decide_2980_ == 0)
{
v_x_2976_ = v_tail_2979_;
goto _start;
}
else
{
return v_decide_2980_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2___redArg___boxed(lean_object* v_a_2982_, lean_object* v_x_2983_){
_start:
{
uint8_t v_res_2984_; lean_object* v_r_2985_; 
v_res_2984_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2___redArg(v_a_2982_, v_x_2983_);
lean_dec(v_x_2983_);
lean_dec(v_a_2982_);
v_r_2985_ = lean_box(v_res_2984_);
return v_r_2985_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2___redArg(lean_object* v_m_2986_, lean_object* v_a_2987_, lean_object* v_b_2988_){
_start:
{
lean_object* v_size_2989_; lean_object* v_buckets_2990_; lean_object* v___x_2991_; uint64_t v___x_2992_; uint64_t v___x_2993_; uint64_t v___x_2994_; uint64_t v_fold_2995_; uint64_t v___x_2996_; uint64_t v___x_2997_; uint64_t v___x_2998_; size_t v___x_2999_; size_t v___x_3000_; size_t v___x_3001_; size_t v___x_3002_; size_t v___x_3003_; lean_object* v_bkt_3004_; uint8_t v___x_3005_; 
v_size_2989_ = lean_ctor_get(v_m_2986_, 0);
v_buckets_2990_ = lean_ctor_get(v_m_2986_, 1);
v___x_2991_ = lean_array_get_size(v_buckets_2990_);
v___x_2992_ = l_String_instHashableRaw_hash(v_a_2987_);
v___x_2993_ = 32ULL;
v___x_2994_ = lean_uint64_shift_right(v___x_2992_, v___x_2993_);
v_fold_2995_ = lean_uint64_xor(v___x_2992_, v___x_2994_);
v___x_2996_ = 16ULL;
v___x_2997_ = lean_uint64_shift_right(v_fold_2995_, v___x_2996_);
v___x_2998_ = lean_uint64_xor(v_fold_2995_, v___x_2997_);
v___x_2999_ = lean_uint64_to_usize(v___x_2998_);
v___x_3000_ = lean_usize_of_nat(v___x_2991_);
v___x_3001_ = ((size_t)1ULL);
v___x_3002_ = lean_usize_sub(v___x_3000_, v___x_3001_);
v___x_3003_ = lean_usize_land(v___x_2999_, v___x_3002_);
v_bkt_3004_ = lean_array_uget_borrowed(v_buckets_2990_, v___x_3003_);
v___x_3005_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2___redArg(v_a_2987_, v_bkt_3004_);
if (v___x_3005_ == 0)
{
lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3026_; 
lean_inc_ref(v_buckets_2990_);
lean_inc(v_size_2989_);
v_isSharedCheck_3026_ = !lean_is_exclusive(v_m_2986_);
if (v_isSharedCheck_3026_ == 0)
{
lean_object* v_unused_3027_; lean_object* v_unused_3028_; 
v_unused_3027_ = lean_ctor_get(v_m_2986_, 1);
lean_dec(v_unused_3027_);
v_unused_3028_ = lean_ctor_get(v_m_2986_, 0);
lean_dec(v_unused_3028_);
v___x_3007_ = v_m_2986_;
v_isShared_3008_ = v_isSharedCheck_3026_;
goto v_resetjp_3006_;
}
else
{
lean_dec(v_m_2986_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3026_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3009_; lean_object* v_size_x27_3010_; lean_object* v___x_3011_; lean_object* v_buckets_x27_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; uint8_t v___x_3018_; 
v___x_3009_ = lean_unsigned_to_nat(1u);
v_size_x27_3010_ = lean_nat_add(v_size_2989_, v___x_3009_);
lean_dec(v_size_2989_);
lean_inc(v_bkt_3004_);
v___x_3011_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3011_, 0, v_a_2987_);
lean_ctor_set(v___x_3011_, 1, v_b_2988_);
lean_ctor_set(v___x_3011_, 2, v_bkt_3004_);
v_buckets_x27_3012_ = lean_array_uset(v_buckets_2990_, v___x_3003_, v___x_3011_);
v___x_3013_ = lean_unsigned_to_nat(4u);
v___x_3014_ = lean_nat_mul(v_size_x27_3010_, v___x_3013_);
v___x_3015_ = lean_unsigned_to_nat(3u);
v___x_3016_ = lean_nat_div(v___x_3014_, v___x_3015_);
lean_dec(v___x_3014_);
v___x_3017_ = lean_array_get_size(v_buckets_x27_3012_);
v___x_3018_ = lean_nat_dec_le(v___x_3016_, v___x_3017_);
lean_dec(v___x_3016_);
if (v___x_3018_ == 0)
{
lean_object* v_val_3019_; lean_object* v___x_3021_; 
v_val_3019_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3___redArg(v_buckets_x27_3012_);
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 1, v_val_3019_);
lean_ctor_set(v___x_3007_, 0, v_size_x27_3010_);
v___x_3021_ = v___x_3007_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_size_x27_3010_);
lean_ctor_set(v_reuseFailAlloc_3022_, 1, v_val_3019_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
else
{
lean_object* v___x_3024_; 
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 1, v_buckets_x27_3012_);
lean_ctor_set(v___x_3007_, 0, v_size_x27_3010_);
v___x_3024_ = v___x_3007_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_size_x27_3010_);
lean_ctor_set(v_reuseFailAlloc_3025_, 1, v_buckets_x27_3012_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
else
{
lean_dec(v_b_2988_);
lean_dec(v_a_2987_);
return v_m_2986_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6___lam__0(uint8_t v___x_3029_, lean_object* v_x_3030_, lean_object* v_info_3031_, lean_object* v_s_3032_){
_start:
{
if (lean_obj_tag(v_info_3031_) == 12)
{
lean_object* v_i_3033_; lean_object* v___x_3034_; 
v_i_3033_ = lean_ctor_get(v_info_3031_, 0);
v___x_3034_ = l_Lean_Syntax_getRange_x3f(v_i_3033_, v___x_3029_);
if (lean_obj_tag(v___x_3034_) == 1)
{
lean_object* v_val_3035_; lean_object* v_start_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v_val_3035_ = lean_ctor_get(v___x_3034_, 0);
lean_inc(v_val_3035_);
lean_dec_ref_known(v___x_3034_, 1);
v_start_3036_ = lean_ctor_get(v_val_3035_, 0);
lean_inc(v_start_3036_);
lean_dec(v_val_3035_);
v___x_3037_ = lean_box(0);
v___x_3038_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2___redArg(v_s_3032_, v_start_3036_, v___x_3037_);
return v___x_3038_;
}
else
{
lean_dec(v___x_3034_);
return v_s_3032_;
}
}
else
{
return v_s_3032_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6___lam__0___boxed(lean_object* v___x_3039_, lean_object* v_x_3040_, lean_object* v_info_3041_, lean_object* v_s_3042_){
_start:
{
uint8_t v___x_8549__boxed_3043_; lean_object* v_res_3044_; 
v___x_8549__boxed_3043_ = lean_unbox(v___x_3039_);
v_res_3044_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6___lam__0(v___x_8549__boxed_3043_, v_x_3040_, v_info_3041_, v_s_3042_);
lean_dec_ref(v_info_3041_);
lean_dec_ref(v_x_3040_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(uint8_t v___x_3045_, lean_object* v_as_3046_, size_t v_i_3047_, size_t v_stop_3048_, lean_object* v_b_3049_){
_start:
{
uint8_t v___x_3050_; 
v___x_3050_ = lean_usize_dec_eq(v_i_3047_, v_stop_3048_);
if (v___x_3050_ == 0)
{
lean_object* v___x_3051_; lean_object* v___f_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; size_t v___x_3055_; size_t v___x_3056_; 
v___x_3051_ = lean_box(v___x_3045_);
v___f_3052_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6___lam__0___boxed), 4, 1);
lean_closure_set(v___f_3052_, 0, v___x_3051_);
v___x_3053_ = lean_array_uget_borrowed(v_as_3046_, v_i_3047_);
lean_inc(v___x_3053_);
v___x_3054_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_3052_, v_b_3049_, v___x_3053_);
v___x_3055_ = ((size_t)1ULL);
v___x_3056_ = lean_usize_add(v_i_3047_, v___x_3055_);
v_i_3047_ = v___x_3056_;
v_b_3049_ = v___x_3054_;
goto _start;
}
else
{
return v_b_3049_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6___boxed(lean_object* v___x_3058_, lean_object* v_as_3059_, lean_object* v_i_3060_, lean_object* v_stop_3061_, lean_object* v_b_3062_){
_start:
{
uint8_t v___x_8565__boxed_3063_; size_t v_i_boxed_3064_; size_t v_stop_boxed_3065_; lean_object* v_res_3066_; 
v___x_8565__boxed_3063_ = lean_unbox(v___x_3058_);
v_i_boxed_3064_ = lean_unbox_usize(v_i_3060_);
lean_dec(v_i_3060_);
v_stop_boxed_3065_ = lean_unbox_usize(v_stop_3061_);
lean_dec(v_stop_3061_);
v_res_3066_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(v___x_8565__boxed_3063_, v_as_3059_, v_i_boxed_3064_, v_stop_boxed_3065_, v_b_3062_);
lean_dec_ref(v_as_3059_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__7(uint8_t v___x_3067_, lean_object* v_x_3068_, lean_object* v_x_3069_){
_start:
{
if (lean_obj_tag(v_x_3068_) == 0)
{
lean_object* v_cs_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; uint8_t v___x_3073_; 
v_cs_3070_ = lean_ctor_get(v_x_3068_, 0);
v___x_3071_ = lean_unsigned_to_nat(0u);
v___x_3072_ = lean_array_get_size(v_cs_3070_);
v___x_3073_ = lean_nat_dec_lt(v___x_3071_, v___x_3072_);
if (v___x_3073_ == 0)
{
return v_x_3069_;
}
else
{
size_t v___x_3074_; size_t v___x_3075_; lean_object* v___x_3076_; 
v___x_3074_ = ((size_t)0ULL);
v___x_3075_ = lean_usize_of_nat(v___x_3072_);
v___x_3076_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5_spec__7(v___x_3067_, v_cs_3070_, v___x_3074_, v___x_3075_, v_x_3069_);
return v___x_3076_;
}
}
else
{
lean_object* v_vs_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; uint8_t v___x_3080_; 
v_vs_3077_ = lean_ctor_get(v_x_3068_, 0);
v___x_3078_ = lean_unsigned_to_nat(0u);
v___x_3079_ = lean_array_get_size(v_vs_3077_);
v___x_3080_ = lean_nat_dec_lt(v___x_3078_, v___x_3079_);
if (v___x_3080_ == 0)
{
return v_x_3069_;
}
else
{
size_t v___x_3081_; size_t v___x_3082_; lean_object* v___x_3083_; 
v___x_3081_ = ((size_t)0ULL);
v___x_3082_ = lean_usize_of_nat(v___x_3079_);
v___x_3083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(v___x_3067_, v_vs_3077_, v___x_3081_, v___x_3082_, v_x_3069_);
return v___x_3083_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5_spec__7(uint8_t v___x_3084_, lean_object* v_as_3085_, size_t v_i_3086_, size_t v_stop_3087_, lean_object* v_b_3088_){
_start:
{
uint8_t v___x_3089_; 
v___x_3089_ = lean_usize_dec_eq(v_i_3086_, v_stop_3087_);
if (v___x_3089_ == 0)
{
lean_object* v___x_3090_; lean_object* v___x_3091_; size_t v___x_3092_; size_t v___x_3093_; 
v___x_3090_ = lean_array_uget_borrowed(v_as_3085_, v_i_3086_);
v___x_3091_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__7(v___x_3084_, v___x_3090_, v_b_3088_);
v___x_3092_ = ((size_t)1ULL);
v___x_3093_ = lean_usize_add(v_i_3086_, v___x_3092_);
v_i_3086_ = v___x_3093_;
v_b_3088_ = v___x_3091_;
goto _start;
}
else
{
return v_b_3088_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5_spec__7___boxed(lean_object* v___x_3095_, lean_object* v_as_3096_, lean_object* v_i_3097_, lean_object* v_stop_3098_, lean_object* v_b_3099_){
_start:
{
uint8_t v___x_8584__boxed_3100_; size_t v_i_boxed_3101_; size_t v_stop_boxed_3102_; lean_object* v_res_3103_; 
v___x_8584__boxed_3100_ = lean_unbox(v___x_3095_);
v_i_boxed_3101_ = lean_unbox_usize(v_i_3097_);
lean_dec(v_i_3097_);
v_stop_boxed_3102_ = lean_unbox_usize(v_stop_3098_);
lean_dec(v_stop_3098_);
v_res_3103_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5_spec__7(v___x_8584__boxed_3100_, v_as_3096_, v_i_boxed_3101_, v_stop_boxed_3102_, v_b_3099_);
lean_dec_ref(v_as_3096_);
return v_res_3103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__7___boxed(lean_object* v___x_3104_, lean_object* v_x_3105_, lean_object* v_x_3106_){
_start:
{
uint8_t v___x_8591__boxed_3107_; lean_object* v_res_3108_; 
v___x_8591__boxed_3107_ = lean_unbox(v___x_3104_);
v_res_3108_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__7(v___x_8591__boxed_3107_, v_x_3105_, v_x_3106_);
lean_dec_ref(v_x_3105_);
return v_res_3108_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_3109_; 
v___x_3109_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5(uint8_t v___x_3110_, lean_object* v_x_3111_, size_t v_x_3112_, size_t v_x_3113_, lean_object* v_x_3114_){
_start:
{
if (lean_obj_tag(v_x_3111_) == 0)
{
lean_object* v_cs_3115_; lean_object* v___x_3116_; size_t v___x_3117_; lean_object* v_j_3118_; lean_object* v___x_3119_; size_t v___x_3120_; size_t v___x_3121_; size_t v___x_3122_; size_t v___x_3123_; size_t v___x_3124_; size_t v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; uint8_t v___x_3130_; 
v_cs_3115_ = lean_ctor_get(v_x_3111_, 0);
v___x_3116_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5___closed__0);
v___x_3117_ = lean_usize_shift_right(v_x_3112_, v_x_3113_);
v_j_3118_ = lean_usize_to_nat(v___x_3117_);
v___x_3119_ = lean_array_get_borrowed(v___x_3116_, v_cs_3115_, v_j_3118_);
v___x_3120_ = ((size_t)1ULL);
v___x_3121_ = lean_usize_shift_left(v___x_3120_, v_x_3113_);
v___x_3122_ = lean_usize_sub(v___x_3121_, v___x_3120_);
v___x_3123_ = lean_usize_land(v_x_3112_, v___x_3122_);
v___x_3124_ = ((size_t)5ULL);
v___x_3125_ = lean_usize_sub(v_x_3113_, v___x_3124_);
v___x_3126_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5(v___x_3110_, v___x_3119_, v___x_3123_, v___x_3125_, v_x_3114_);
v___x_3127_ = lean_unsigned_to_nat(1u);
v___x_3128_ = lean_nat_add(v_j_3118_, v___x_3127_);
lean_dec(v_j_3118_);
v___x_3129_ = lean_array_get_size(v_cs_3115_);
v___x_3130_ = lean_nat_dec_lt(v___x_3128_, v___x_3129_);
if (v___x_3130_ == 0)
{
lean_dec(v___x_3128_);
return v___x_3126_;
}
else
{
size_t v___x_3131_; size_t v___x_3132_; lean_object* v___x_3133_; 
v___x_3131_ = lean_usize_of_nat(v___x_3128_);
lean_dec(v___x_3128_);
v___x_3132_ = lean_usize_of_nat(v___x_3129_);
v___x_3133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5_spec__7(v___x_3110_, v_cs_3115_, v___x_3131_, v___x_3132_, v___x_3126_);
return v___x_3133_;
}
}
else
{
lean_object* v_vs_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; uint8_t v___x_3137_; 
v_vs_3134_ = lean_ctor_get(v_x_3111_, 0);
v___x_3135_ = lean_usize_to_nat(v_x_3112_);
v___x_3136_ = lean_array_get_size(v_vs_3134_);
v___x_3137_ = lean_nat_dec_lt(v___x_3135_, v___x_3136_);
if (v___x_3137_ == 0)
{
lean_dec(v___x_3135_);
return v_x_3114_;
}
else
{
size_t v___x_3138_; size_t v___x_3139_; lean_object* v___x_3140_; 
v___x_3138_ = lean_usize_of_nat(v___x_3135_);
lean_dec(v___x_3135_);
v___x_3139_ = lean_usize_of_nat(v___x_3136_);
v___x_3140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(v___x_3110_, v_vs_3134_, v___x_3138_, v___x_3139_, v_x_3114_);
return v___x_3140_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5___boxed(lean_object* v___x_3141_, lean_object* v_x_3142_, lean_object* v_x_3143_, lean_object* v_x_3144_, lean_object* v_x_3145_){
_start:
{
uint8_t v___x_8638__boxed_3146_; size_t v_x_8640__boxed_3147_; size_t v_x_8641__boxed_3148_; lean_object* v_res_3149_; 
v___x_8638__boxed_3146_ = lean_unbox(v___x_3141_);
v_x_8640__boxed_3147_ = lean_unbox_usize(v_x_3143_);
lean_dec(v_x_3143_);
v_x_8641__boxed_3148_ = lean_unbox_usize(v_x_3144_);
lean_dec(v_x_3144_);
v_res_3149_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5(v___x_8638__boxed_3146_, v_x_3142_, v_x_8640__boxed_3147_, v_x_8641__boxed_3148_, v_x_3145_);
lean_dec_ref(v_x_3142_);
return v_res_3149_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3(uint8_t v___x_3150_, lean_object* v_t_3151_, lean_object* v_init_3152_, lean_object* v_start_3153_){
_start:
{
lean_object* v___x_3154_; uint8_t v___x_3155_; 
v___x_3154_ = lean_unsigned_to_nat(0u);
v___x_3155_ = lean_nat_dec_eq(v_start_3153_, v___x_3154_);
if (v___x_3155_ == 0)
{
lean_object* v_root_3156_; lean_object* v_tail_3157_; size_t v_shift_3158_; lean_object* v_tailOff_3159_; uint8_t v___x_3160_; 
v_root_3156_ = lean_ctor_get(v_t_3151_, 0);
v_tail_3157_ = lean_ctor_get(v_t_3151_, 1);
v_shift_3158_ = lean_ctor_get_usize(v_t_3151_, 4);
v_tailOff_3159_ = lean_ctor_get(v_t_3151_, 3);
v___x_3160_ = lean_nat_dec_le(v_tailOff_3159_, v_start_3153_);
if (v___x_3160_ == 0)
{
size_t v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; uint8_t v___x_3164_; 
v___x_3161_ = lean_usize_of_nat(v_start_3153_);
v___x_3162_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__5(v___x_3150_, v_root_3156_, v___x_3161_, v_shift_3158_, v_init_3152_);
v___x_3163_ = lean_array_get_size(v_tail_3157_);
v___x_3164_ = lean_nat_dec_lt(v___x_3154_, v___x_3163_);
if (v___x_3164_ == 0)
{
return v___x_3162_;
}
else
{
size_t v___x_3165_; size_t v___x_3166_; lean_object* v___x_3167_; 
v___x_3165_ = ((size_t)0ULL);
v___x_3166_ = lean_usize_of_nat(v___x_3163_);
v___x_3167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(v___x_3150_, v_tail_3157_, v___x_3165_, v___x_3166_, v___x_3162_);
return v___x_3167_;
}
}
else
{
lean_object* v___x_3168_; lean_object* v___x_3169_; uint8_t v___x_3170_; 
v___x_3168_ = lean_nat_sub(v_start_3153_, v_tailOff_3159_);
v___x_3169_ = lean_array_get_size(v_tail_3157_);
v___x_3170_ = lean_nat_dec_lt(v___x_3168_, v___x_3169_);
if (v___x_3170_ == 0)
{
lean_dec(v___x_3168_);
return v_init_3152_;
}
else
{
size_t v___x_3171_; size_t v___x_3172_; lean_object* v___x_3173_; 
v___x_3171_ = lean_usize_of_nat(v___x_3168_);
lean_dec(v___x_3168_);
v___x_3172_ = lean_usize_of_nat(v___x_3169_);
v___x_3173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(v___x_3150_, v_tail_3157_, v___x_3171_, v___x_3172_, v_init_3152_);
return v___x_3173_;
}
}
}
else
{
lean_object* v_root_3174_; lean_object* v_tail_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; uint8_t v___x_3178_; 
v_root_3174_ = lean_ctor_get(v_t_3151_, 0);
v_tail_3175_ = lean_ctor_get(v_t_3151_, 1);
v___x_3176_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__7(v___x_3150_, v_root_3174_, v_init_3152_);
v___x_3177_ = lean_array_get_size(v_tail_3175_);
v___x_3178_ = lean_nat_dec_lt(v___x_3154_, v___x_3177_);
if (v___x_3178_ == 0)
{
return v___x_3176_;
}
else
{
size_t v___x_3179_; size_t v___x_3180_; lean_object* v___x_3181_; 
v___x_3179_ = ((size_t)0ULL);
v___x_3180_ = lean_usize_of_nat(v___x_3177_);
v___x_3181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3_spec__6(v___x_3150_, v_tail_3175_, v___x_3179_, v___x_3180_, v___x_3176_);
return v___x_3181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3___boxed(lean_object* v___x_3182_, lean_object* v_t_3183_, lean_object* v_init_3184_, lean_object* v_start_3185_){
_start:
{
uint8_t v___x_8704__boxed_3186_; lean_object* v_res_3187_; 
v___x_8704__boxed_3186_ = lean_unbox(v___x_3182_);
v_res_3187_ = l_Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3(v___x_8704__boxed_3186_, v_t_3183_, v_init_3184_, v_start_3185_);
lean_dec(v_start_3185_);
lean_dec_ref(v_t_3183_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__0(lean_object* v_rest_3189_, uint8_t v___x_3190_, uint8_t v___y_3191_, lean_object* v_as_3192_, size_t v_sz_3193_, size_t v_i_3194_, lean_object* v_b_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_){
_start:
{
lean_object* v_a_3200_; uint8_t v___x_3204_; 
v___x_3204_ = lean_usize_dec_lt(v_i_3194_, v_sz_3193_);
if (v___x_3204_ == 0)
{
lean_object* v___x_3205_; 
v___x_3205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3205_, 0, v_b_3195_);
return v___x_3205_;
}
else
{
lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v_a_3210_; uint8_t v___y_3212_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3206_ = lean_unsigned_to_nat(2u);
v___x_3207_ = lean_unsigned_to_nat(0u);
v___x_3208_ = lean_box(0);
v___x_3209_ = lean_unsigned_to_nat(1u);
v_a_3210_ = lean_array_uget_borrowed(v_as_3192_, v_i_3194_);
v___x_3219_ = l_Lean_Syntax_getArg(v_a_3210_, v___x_3206_);
v___x_3220_ = l_Lean_Syntax_getArg(v_a_3210_, v___x_3207_);
v___x_3221_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString(v___x_3220_, v___y_3196_, v___y_3197_);
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_object* v_a_3222_; uint8_t v___y_3224_; uint8_t v___y_3239_; uint8_t v___x_3241_; 
v_a_3222_ = lean_ctor_get(v___x_3221_, 0);
lean_inc(v_a_3222_);
lean_dec_ref_known(v___x_3221_, 1);
v___x_3241_ = l_Lean_Syntax_isNone(v___x_3220_);
lean_dec(v___x_3220_);
if (v___x_3241_ == 0)
{
v___y_3239_ = v___y_3191_;
goto v___jp_3238_;
}
else
{
v___y_3239_ = v___x_3190_;
goto v___jp_3238_;
}
v___jp_3223_:
{
if (v___y_3224_ == 0)
{
lean_object* v___x_3225_; 
v___x_3225_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v___x_3219_, v___y_3196_, v___y_3197_);
lean_dec(v___x_3219_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v_a_3226_; 
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
lean_inc(v_a_3226_);
lean_dec_ref_known(v___x_3225_, 1);
if (lean_obj_tag(v_a_3226_) == 1)
{
uint8_t v___x_3227_; 
v___x_3227_ = lean_unbox(v_a_3222_);
lean_dec(v_a_3222_);
if (v___x_3227_ == 0)
{
lean_object* v_val_3228_; uint8_t v___x_3229_; 
v_val_3228_ = lean_ctor_get(v_a_3226_, 0);
lean_inc(v_val_3228_);
lean_dec_ref_known(v_a_3226_, 1);
v___x_3229_ = lean_unbox(v_val_3228_);
lean_dec(v_val_3228_);
v___y_3212_ = v___x_3229_;
goto v___jp_3211_;
}
else
{
lean_dec_ref_known(v_a_3226_, 1);
v___y_3212_ = v___x_3204_;
goto v___jp_3211_;
}
}
else
{
lean_dec(v_a_3226_);
lean_dec(v_a_3222_);
v_a_3200_ = v___x_3208_;
goto v___jp_3199_;
}
}
else
{
lean_object* v_a_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3237_; 
lean_dec(v_a_3222_);
v_a_3230_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3232_ = v___x_3225_;
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_a_3230_);
lean_dec(v___x_3225_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3235_; 
if (v_isShared_3233_ == 0)
{
v___x_3235_ = v___x_3232_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_a_3230_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
return v___x_3235_;
}
}
}
}
else
{
lean_dec(v_a_3222_);
lean_dec(v___x_3219_);
v_a_3200_ = v___x_3208_;
goto v___jp_3199_;
}
}
v___jp_3238_:
{
if (v___y_3239_ == 0)
{
v___y_3224_ = v___x_3190_;
goto v___jp_3223_;
}
else
{
uint8_t v___x_3240_; 
v___x_3240_ = lean_unbox(v_a_3222_);
if (v___x_3240_ == 0)
{
lean_dec(v_a_3222_);
lean_dec(v___x_3219_);
v_a_3200_ = v___x_3208_;
goto v___jp_3199_;
}
else
{
v___y_3224_ = v___x_3190_;
goto v___jp_3223_;
}
}
}
}
else
{
lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3249_; 
lean_dec(v___x_3220_);
lean_dec(v___x_3219_);
v_a_3242_ = lean_ctor_get(v___x_3221_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3244_ = v___x_3221_;
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___x_3221_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3247_; 
if (v_isShared_3245_ == 0)
{
v___x_3247_ = v___x_3244_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_a_3242_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
v___jp_3211_:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3213_ = l_Lean_Syntax_getArg(v_rest_3189_, v___x_3209_);
v___x_3214_ = l_Lean_Syntax_getArg(v___x_3213_, v___x_3207_);
lean_dec(v___x_3213_);
v___x_3215_ = lean_unsigned_to_nat(3u);
v___x_3216_ = l_Lean_Syntax_getArg(v_a_3210_, v___x_3215_);
v___x_3217_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__0___closed__0));
v___x_3218_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(v___y_3212_, v___x_3214_, v___x_3216_, v___x_3217_, v___y_3196_, v___y_3197_);
lean_dec(v___x_3214_);
if (lean_obj_tag(v___x_3218_) == 0)
{
lean_dec_ref_known(v___x_3218_, 1);
v_a_3200_ = v___x_3208_;
goto v___jp_3199_;
}
else
{
return v___x_3218_;
}
}
}
v___jp_3199_:
{
size_t v___x_3201_; size_t v___x_3202_; 
v___x_3201_ = ((size_t)1ULL);
v___x_3202_ = lean_usize_add(v_i_3194_, v___x_3201_);
v_i_3194_ = v___x_3202_;
v_b_3195_ = v_a_3200_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__0___boxed(lean_object* v_rest_3250_, lean_object* v___x_3251_, lean_object* v___y_3252_, lean_object* v_as_3253_, lean_object* v_sz_3254_, lean_object* v_i_3255_, lean_object* v_b_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_){
_start:
{
uint8_t v___x_8753__boxed_3260_; uint8_t v___y_8754__boxed_3261_; size_t v_sz_boxed_3262_; size_t v_i_boxed_3263_; lean_object* v_res_3264_; 
v___x_8753__boxed_3260_ = lean_unbox(v___x_3251_);
v___y_8754__boxed_3261_ = lean_unbox(v___y_3252_);
v_sz_boxed_3262_ = lean_unbox_usize(v_sz_3254_);
lean_dec(v_sz_3254_);
v_i_boxed_3263_ = lean_unbox_usize(v_i_3255_);
lean_dec(v_i_3255_);
v_res_3264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__0(v_rest_3250_, v___x_8753__boxed_3260_, v___y_8754__boxed_3261_, v_as_3253_, v_sz_boxed_3262_, v_i_boxed_3263_, v_b_3256_, v___y_3257_, v___y_3258_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
lean_dec_ref(v_as_3253_);
lean_dec(v_rest_3250_);
return v_res_3264_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg(lean_object* v_m_3265_, lean_object* v_a_3266_){
_start:
{
lean_object* v_buckets_3267_; lean_object* v___x_3268_; uint64_t v___x_3269_; uint64_t v___x_3270_; uint64_t v___x_3271_; uint64_t v_fold_3272_; uint64_t v___x_3273_; uint64_t v___x_3274_; uint64_t v___x_3275_; size_t v___x_3276_; size_t v___x_3277_; size_t v___x_3278_; size_t v___x_3279_; size_t v___x_3280_; lean_object* v___x_3281_; uint8_t v___x_3282_; 
v_buckets_3267_ = lean_ctor_get(v_m_3265_, 1);
v___x_3268_ = lean_array_get_size(v_buckets_3267_);
v___x_3269_ = l_String_instHashableRaw_hash(v_a_3266_);
v___x_3270_ = 32ULL;
v___x_3271_ = lean_uint64_shift_right(v___x_3269_, v___x_3270_);
v_fold_3272_ = lean_uint64_xor(v___x_3269_, v___x_3271_);
v___x_3273_ = 16ULL;
v___x_3274_ = lean_uint64_shift_right(v_fold_3272_, v___x_3273_);
v___x_3275_ = lean_uint64_xor(v_fold_3272_, v___x_3274_);
v___x_3276_ = lean_uint64_to_usize(v___x_3275_);
v___x_3277_ = lean_usize_of_nat(v___x_3268_);
v___x_3278_ = ((size_t)1ULL);
v___x_3279_ = lean_usize_sub(v___x_3277_, v___x_3278_);
v___x_3280_ = lean_usize_land(v___x_3276_, v___x_3279_);
v___x_3281_ = lean_array_uget_borrowed(v_buckets_3267_, v___x_3280_);
v___x_3282_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2___redArg(v_a_3266_, v___x_3281_);
return v___x_3282_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg___boxed(lean_object* v_m_3283_, lean_object* v_a_3284_){
_start:
{
uint8_t v_res_3285_; lean_object* v_r_3286_; 
v_res_3285_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg(v_m_3283_, v_a_3284_);
lean_dec(v_a_3284_);
lean_dec_ref(v_m_3283_);
v_r_3286_ = lean_box(v_res_3285_);
return v_r_3286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10(uint8_t v_val_3288_, lean_object* v___x_3289_, uint8_t v___x_3290_, lean_object* v___x_3291_, lean_object* v_as_3292_, size_t v_sz_3293_, size_t v_i_3294_, lean_object* v_b_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_){
_start:
{
lean_object* v_a_3300_; uint8_t v___x_3304_; 
v___x_3304_ = lean_usize_dec_lt(v_i_3294_, v_sz_3293_);
if (v___x_3304_ == 0)
{
lean_object* v___x_3305_; 
v___x_3305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3305_, 0, v_b_3295_);
return v___x_3305_;
}
else
{
lean_object* v___x_3306_; lean_object* v_a_3307_; lean_object* v___y_3309_; lean_object* v___y_3310_; lean_object* v___x_3313_; 
v___x_3306_ = lean_box(0);
v_a_3307_ = lean_array_uget_borrowed(v_as_3292_, v_i_3294_);
v___x_3313_ = l_Lean_Syntax_getRange_x3f(v_a_3307_, v___x_3290_);
if (lean_obj_tag(v___x_3313_) == 1)
{
lean_object* v_val_3314_; lean_object* v_start_3315_; uint8_t v___x_3316_; 
v_val_3314_ = lean_ctor_get(v___x_3313_, 0);
lean_inc(v_val_3314_);
lean_dec_ref_known(v___x_3313_, 1);
v_start_3315_ = lean_ctor_get(v_val_3314_, 0);
lean_inc(v_start_3315_);
lean_dec(v_val_3314_);
v___x_3316_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg(v___x_3291_, v_start_3315_);
lean_dec(v_start_3315_);
if (v___x_3316_ == 0)
{
v___y_3309_ = v___y_3296_;
v___y_3310_ = v___y_3297_;
goto v___jp_3308_;
}
else
{
v_a_3300_ = v___x_3306_;
goto v___jp_3299_;
}
}
else
{
lean_dec(v___x_3313_);
v___y_3309_ = v___y_3296_;
v___y_3310_ = v___y_3297_;
goto v___jp_3308_;
}
v___jp_3308_:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3311_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10___closed__0));
lean_inc(v_a_3307_);
v___x_3312_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(v_val_3288_, v___x_3289_, v_a_3307_, v___x_3311_, v___y_3309_, v___y_3310_);
if (lean_obj_tag(v___x_3312_) == 0)
{
lean_dec_ref_known(v___x_3312_, 1);
v_a_3300_ = v___x_3306_;
goto v___jp_3299_;
}
else
{
return v___x_3312_;
}
}
}
v___jp_3299_:
{
size_t v___x_3301_; size_t v___x_3302_; 
v___x_3301_ = ((size_t)1ULL);
v___x_3302_ = lean_usize_add(v_i_3294_, v___x_3301_);
v_i_3294_ = v___x_3302_;
v_b_3295_ = v_a_3300_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10___boxed(lean_object* v_val_3317_, lean_object* v___x_3318_, lean_object* v___x_3319_, lean_object* v___x_3320_, lean_object* v_as_3321_, lean_object* v_sz_3322_, lean_object* v_i_3323_, lean_object* v_b_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_){
_start:
{
uint8_t v_val_8904__boxed_3328_; uint8_t v___x_8906__boxed_3329_; size_t v_sz_boxed_3330_; size_t v_i_boxed_3331_; lean_object* v_res_3332_; 
v_val_8904__boxed_3328_ = lean_unbox(v_val_3317_);
v___x_8906__boxed_3329_ = lean_unbox(v___x_3319_);
v_sz_boxed_3330_ = lean_unbox_usize(v_sz_3322_);
lean_dec(v_sz_3322_);
v_i_boxed_3331_ = lean_unbox_usize(v_i_3323_);
lean_dec(v_i_3323_);
v_res_3332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10(v_val_8904__boxed_3328_, v___x_3318_, v___x_8906__boxed_3329_, v___x_3320_, v_as_3321_, v_sz_boxed_3330_, v_i_boxed_3331_, v_b_3324_, v___y_3325_, v___y_3326_);
lean_dec(v___y_3326_);
lean_dec_ref(v___y_3325_);
lean_dec_ref(v_as_3321_);
lean_dec_ref(v___x_3320_);
lean_dec(v___x_3318_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5(lean_object* v___x_3333_, uint8_t v___x_3334_, lean_object* v___x_3335_, uint8_t v_val_3336_, lean_object* v_as_3337_, size_t v_sz_3338_, size_t v_i_3339_, lean_object* v_b_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_){
_start:
{
lean_object* v_a_3345_; uint8_t v___x_3349_; 
v___x_3349_ = lean_usize_dec_lt(v_i_3339_, v_sz_3338_);
if (v___x_3349_ == 0)
{
lean_object* v___x_3350_; 
v___x_3350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3350_, 0, v_b_3340_);
return v___x_3350_;
}
else
{
lean_object* v___x_3351_; lean_object* v_a_3352_; lean_object* v___y_3354_; lean_object* v___y_3355_; lean_object* v___x_3358_; 
v___x_3351_ = lean_box(0);
v_a_3352_ = lean_array_uget_borrowed(v_as_3337_, v_i_3339_);
v___x_3358_ = l_Lean_Syntax_getRange_x3f(v_a_3352_, v___x_3334_);
if (lean_obj_tag(v___x_3358_) == 1)
{
lean_object* v_val_3359_; lean_object* v_start_3360_; uint8_t v___x_3361_; 
v_val_3359_ = lean_ctor_get(v___x_3358_, 0);
lean_inc(v_val_3359_);
lean_dec_ref_known(v___x_3358_, 1);
v_start_3360_ = lean_ctor_get(v_val_3359_, 0);
lean_inc(v_start_3360_);
lean_dec(v_val_3359_);
v___x_3361_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg(v___x_3335_, v_start_3360_);
lean_dec(v_start_3360_);
if (v___x_3361_ == 0)
{
v___y_3354_ = v___y_3341_;
v___y_3355_ = v___y_3342_;
goto v___jp_3353_;
}
else
{
v_a_3345_ = v___x_3351_;
goto v___jp_3344_;
}
}
else
{
lean_dec(v___x_3358_);
v___y_3354_ = v___y_3341_;
v___y_3355_ = v___y_3342_;
goto v___jp_3353_;
}
v___jp_3353_:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3356_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10___closed__0));
lean_inc(v_a_3352_);
v___x_3357_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(v_val_3336_, v___x_3333_, v_a_3352_, v___x_3356_, v___y_3354_, v___y_3355_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_dec_ref_known(v___x_3357_, 1);
v_a_3345_ = v___x_3351_;
goto v___jp_3344_;
}
else
{
return v___x_3357_;
}
}
}
v___jp_3344_:
{
size_t v___x_3346_; size_t v___x_3347_; lean_object* v___x_3348_; 
v___x_3346_ = ((size_t)1ULL);
v___x_3347_ = lean_usize_add(v_i_3339_, v___x_3346_);
v___x_3348_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10(v_val_3336_, v___x_3333_, v___x_3334_, v___x_3335_, v_as_3337_, v_sz_3338_, v___x_3347_, v_a_3345_, v___y_3341_, v___y_3342_);
return v___x_3348_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5___boxed(lean_object* v___x_3362_, lean_object* v___x_3363_, lean_object* v___x_3364_, lean_object* v_val_3365_, lean_object* v_as_3366_, lean_object* v_sz_3367_, lean_object* v_i_3368_, lean_object* v_b_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_){
_start:
{
uint8_t v___x_8962__boxed_3373_; uint8_t v_val_8964__boxed_3374_; size_t v_sz_boxed_3375_; size_t v_i_boxed_3376_; lean_object* v_res_3377_; 
v___x_8962__boxed_3373_ = lean_unbox(v___x_3363_);
v_val_8964__boxed_3374_ = lean_unbox(v_val_3365_);
v_sz_boxed_3375_ = lean_unbox_usize(v_sz_3367_);
lean_dec(v_sz_3367_);
v_i_boxed_3376_ = lean_unbox_usize(v_i_3368_);
lean_dec(v_i_3368_);
v_res_3377_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5(v___x_3362_, v___x_8962__boxed_3373_, v___x_3364_, v_val_8964__boxed_3374_, v_as_3366_, v_sz_boxed_3375_, v_i_boxed_3376_, v_b_3369_, v___y_3370_, v___y_3371_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
lean_dec_ref(v_as_3366_);
lean_dec_ref(v___x_3364_);
lean_dec(v___x_3362_);
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12(lean_object* v___x_3384_, uint8_t v___x_3385_, lean_object* v___x_3386_, lean_object* v_as_3387_, size_t v_sz_3388_, size_t v_i_3389_, lean_object* v_b_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_){
_start:
{
lean_object* v_a_3395_; uint8_t v___x_3399_; 
v___x_3399_ = lean_usize_dec_lt(v_i_3389_, v_sz_3388_);
if (v___x_3399_ == 0)
{
lean_object* v___x_3400_; 
v___x_3400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3400_, 0, v_b_3390_);
return v___x_3400_;
}
else
{
lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v_a_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3401_ = lean_unsigned_to_nat(0u);
v___x_3402_ = lean_unsigned_to_nat(2u);
v___x_3403_ = lean_box(0);
v___x_3404_ = lean_unsigned_to_nat(1u);
v_a_3405_ = lean_array_uget_borrowed(v_as_3387_, v_i_3389_);
v___x_3406_ = l_Lean_Syntax_getArg(v_a_3405_, v___x_3401_);
v___x_3407_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v___x_3406_, v___y_3391_, v___y_3392_);
lean_dec(v___x_3406_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_a_3408_; 
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_a_3408_);
lean_dec_ref_known(v___x_3407_, 1);
if (lean_obj_tag(v_a_3408_) == 1)
{
lean_object* v_val_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; uint8_t v___x_3412_; 
v_val_3409_ = lean_ctor_get(v_a_3408_, 0);
lean_inc(v_val_3409_);
lean_dec_ref_known(v_a_3408_, 1);
lean_inc(v_a_3405_);
v___x_3410_ = l_Lean_Syntax_getKind(v_a_3405_);
v___x_3411_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12___closed__1));
v___x_3412_ = lean_name_eq(v___x_3410_, v___x_3411_);
lean_dec(v___x_3410_);
if (v___x_3412_ == 0)
{
lean_object* v___x_3413_; lean_object* v___x_3414_; size_t v_sz_3415_; size_t v___x_3416_; uint8_t v___x_3417_; lean_object* v___x_3418_; 
v___x_3413_ = l_Lean_Syntax_getArg(v_a_3405_, v___x_3402_);
v___x_3414_ = l_Lean_Syntax_getArgs(v___x_3413_);
lean_dec(v___x_3413_);
v_sz_3415_ = lean_array_size(v___x_3414_);
v___x_3416_ = ((size_t)0ULL);
v___x_3417_ = lean_unbox(v_val_3409_);
lean_dec(v_val_3409_);
v___x_3418_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5(v___x_3384_, v___x_3385_, v___x_3386_, v___x_3417_, v___x_3414_, v_sz_3415_, v___x_3416_, v___x_3403_, v___y_3391_, v___y_3392_);
lean_dec_ref(v___x_3414_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_dec_ref_known(v___x_3418_, 1);
v_a_3395_ = v___x_3403_;
goto v___jp_3394_;
}
else
{
return v___x_3418_;
}
}
else
{
lean_object* v___x_3419_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___x_3426_; 
v___x_3419_ = l_Lean_Syntax_getArg(v_a_3405_, v___x_3404_);
v___x_3426_ = l_Lean_Syntax_getRange_x3f(v___x_3419_, v___x_3385_);
if (lean_obj_tag(v___x_3426_) == 1)
{
lean_object* v_val_3427_; lean_object* v_start_3428_; uint8_t v___x_3429_; 
v_val_3427_ = lean_ctor_get(v___x_3426_, 0);
lean_inc(v_val_3427_);
lean_dec_ref_known(v___x_3426_, 1);
v_start_3428_ = lean_ctor_get(v_val_3427_, 0);
lean_inc(v_start_3428_);
lean_dec(v_val_3427_);
v___x_3429_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg(v___x_3386_, v_start_3428_);
lean_dec(v_start_3428_);
if (v___x_3429_ == 0)
{
v___y_3421_ = v___y_3391_;
v___y_3422_ = v___y_3392_;
goto v___jp_3420_;
}
else
{
lean_dec(v___x_3419_);
lean_dec(v_val_3409_);
v_a_3395_ = v___x_3403_;
goto v___jp_3394_;
}
}
else
{
lean_dec(v___x_3426_);
v___y_3421_ = v___y_3391_;
v___y_3422_ = v___y_3392_;
goto v___jp_3420_;
}
v___jp_3420_:
{
lean_object* v___x_3423_; uint8_t v___x_3424_; lean_object* v___x_3425_; 
v___x_3423_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10___closed__0));
v___x_3424_ = lean_unbox(v_val_3409_);
lean_dec(v_val_3409_);
v___x_3425_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(v___x_3424_, v___x_3384_, v___x_3419_, v___x_3423_, v___y_3421_, v___y_3422_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_dec_ref_known(v___x_3425_, 1);
v_a_3395_ = v___x_3403_;
goto v___jp_3394_;
}
else
{
return v___x_3425_;
}
}
}
}
else
{
lean_dec(v_a_3408_);
v_a_3395_ = v___x_3403_;
goto v___jp_3394_;
}
}
else
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3437_; 
v_a_3430_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3432_ = v___x_3407_;
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3407_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3435_; 
if (v_isShared_3433_ == 0)
{
v___x_3435_ = v___x_3432_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_a_3430_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
}
v___jp_3394_:
{
size_t v___x_3396_; size_t v___x_3397_; 
v___x_3396_ = ((size_t)1ULL);
v___x_3397_ = lean_usize_add(v_i_3389_, v___x_3396_);
v_i_3389_ = v___x_3397_;
v_b_3390_ = v_a_3395_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12___boxed(lean_object* v___x_3438_, lean_object* v___x_3439_, lean_object* v___x_3440_, lean_object* v_as_3441_, lean_object* v_sz_3442_, lean_object* v_i_3443_, lean_object* v_b_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_){
_start:
{
uint8_t v___x_9033__boxed_3448_; size_t v_sz_boxed_3449_; size_t v_i_boxed_3450_; lean_object* v_res_3451_; 
v___x_9033__boxed_3448_ = lean_unbox(v___x_3439_);
v_sz_boxed_3449_ = lean_unbox_usize(v_sz_3442_);
lean_dec(v_sz_3442_);
v_i_boxed_3450_ = lean_unbox_usize(v_i_3443_);
lean_dec(v_i_3443_);
v_res_3451_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12(v___x_3438_, v___x_9033__boxed_3448_, v___x_3440_, v_as_3441_, v_sz_boxed_3449_, v_i_boxed_3450_, v_b_3444_, v___y_3445_, v___y_3446_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
lean_dec_ref(v_as_3441_);
lean_dec_ref(v___x_3440_);
lean_dec(v___x_3438_);
return v_res_3451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6(lean_object* v___x_3452_, uint8_t v___x_3453_, lean_object* v___x_3454_, lean_object* v_as_3455_, size_t v_sz_3456_, size_t v_i_3457_, lean_object* v_b_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
lean_object* v_a_3463_; uint8_t v___x_3467_; 
v___x_3467_ = lean_usize_dec_lt(v_i_3457_, v_sz_3456_);
if (v___x_3467_ == 0)
{
lean_object* v___x_3468_; 
v___x_3468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3468_, 0, v_b_3458_);
return v___x_3468_;
}
else
{
lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v_a_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3469_ = lean_unsigned_to_nat(0u);
v___x_3470_ = lean_box(0);
v___x_3471_ = lean_unsigned_to_nat(2u);
v___x_3472_ = lean_unsigned_to_nat(1u);
v_a_3473_ = lean_array_uget_borrowed(v_as_3455_, v_i_3457_);
v___x_3474_ = l_Lean_Syntax_getArg(v_a_3473_, v___x_3469_);
v___x_3475_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v___x_3474_, v___y_3459_, v___y_3460_);
lean_dec(v___x_3474_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_object* v_a_3476_; 
v_a_3476_ = lean_ctor_get(v___x_3475_, 0);
lean_inc(v_a_3476_);
lean_dec_ref_known(v___x_3475_, 1);
if (lean_obj_tag(v_a_3476_) == 1)
{
lean_object* v_val_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; uint8_t v___x_3480_; 
v_val_3477_ = lean_ctor_get(v_a_3476_, 0);
lean_inc(v_val_3477_);
lean_dec_ref_known(v_a_3476_, 1);
lean_inc(v_a_3473_);
v___x_3478_ = l_Lean_Syntax_getKind(v_a_3473_);
v___x_3479_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12___closed__1));
v___x_3480_ = lean_name_eq(v___x_3478_, v___x_3479_);
lean_dec(v___x_3478_);
if (v___x_3480_ == 0)
{
lean_object* v___x_3481_; lean_object* v___x_3482_; size_t v_sz_3483_; size_t v___x_3484_; uint8_t v___x_3485_; lean_object* v___x_3486_; 
v___x_3481_ = l_Lean_Syntax_getArg(v_a_3473_, v___x_3471_);
v___x_3482_ = l_Lean_Syntax_getArgs(v___x_3481_);
lean_dec(v___x_3481_);
v_sz_3483_ = lean_array_size(v___x_3482_);
v___x_3484_ = ((size_t)0ULL);
v___x_3485_ = lean_unbox(v_val_3477_);
lean_dec(v_val_3477_);
v___x_3486_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5(v___x_3452_, v___x_3453_, v___x_3454_, v___x_3485_, v___x_3482_, v_sz_3483_, v___x_3484_, v___x_3470_, v___y_3459_, v___y_3460_);
lean_dec_ref(v___x_3482_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_dec_ref_known(v___x_3486_, 1);
v_a_3463_ = v___x_3470_;
goto v___jp_3462_;
}
else
{
return v___x_3486_;
}
}
else
{
lean_object* v___x_3487_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___x_3494_; 
v___x_3487_ = l_Lean_Syntax_getArg(v_a_3473_, v___x_3472_);
v___x_3494_ = l_Lean_Syntax_getRange_x3f(v___x_3487_, v___x_3453_);
if (lean_obj_tag(v___x_3494_) == 1)
{
lean_object* v_val_3495_; lean_object* v_start_3496_; uint8_t v___x_3497_; 
v_val_3495_ = lean_ctor_get(v___x_3494_, 0);
lean_inc(v_val_3495_);
lean_dec_ref_known(v___x_3494_, 1);
v_start_3496_ = lean_ctor_get(v_val_3495_, 0);
lean_inc(v_start_3496_);
lean_dec(v_val_3495_);
v___x_3497_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg(v___x_3454_, v_start_3496_);
lean_dec(v_start_3496_);
if (v___x_3497_ == 0)
{
v___y_3489_ = v___y_3459_;
v___y_3490_ = v___y_3460_;
goto v___jp_3488_;
}
else
{
lean_dec(v___x_3487_);
lean_dec(v_val_3477_);
v_a_3463_ = v___x_3470_;
goto v___jp_3462_;
}
}
else
{
lean_dec(v___x_3494_);
v___y_3489_ = v___y_3459_;
v___y_3490_ = v___y_3460_;
goto v___jp_3488_;
}
v___jp_3488_:
{
lean_object* v___x_3491_; uint8_t v___x_3492_; lean_object* v___x_3493_; 
v___x_3491_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__5_spec__10___closed__0));
v___x_3492_ = lean_unbox(v_val_3477_);
lean_dec(v_val_3477_);
v___x_3493_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusField(v___x_3492_, v___x_3452_, v___x_3487_, v___x_3491_, v___y_3489_, v___y_3490_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_dec_ref_known(v___x_3493_, 1);
v_a_3463_ = v___x_3470_;
goto v___jp_3462_;
}
else
{
return v___x_3493_;
}
}
}
}
else
{
lean_dec(v_a_3476_);
v_a_3463_ = v___x_3470_;
goto v___jp_3462_;
}
}
else
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3505_; 
v_a_3498_ = lean_ctor_get(v___x_3475_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3500_ = v___x_3475_;
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3475_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3503_; 
if (v_isShared_3501_ == 0)
{
v___x_3503_ = v___x_3500_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_a_3498_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
}
v___jp_3462_:
{
size_t v___x_3464_; size_t v___x_3465_; lean_object* v___x_3466_; 
v___x_3464_ = ((size_t)1ULL);
v___x_3465_ = lean_usize_add(v_i_3457_, v___x_3464_);
v___x_3466_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6_spec__12(v___x_3452_, v___x_3453_, v___x_3454_, v_as_3455_, v_sz_3456_, v___x_3465_, v_a_3463_, v___y_3459_, v___y_3460_);
return v___x_3466_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6___boxed(lean_object* v___x_3506_, lean_object* v___x_3507_, lean_object* v___x_3508_, lean_object* v_as_3509_, lean_object* v_sz_3510_, lean_object* v_i_3511_, lean_object* v_b_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_){
_start:
{
uint8_t v___x_9153__boxed_3516_; size_t v_sz_boxed_3517_; size_t v_i_boxed_3518_; lean_object* v_res_3519_; 
v___x_9153__boxed_3516_ = lean_unbox(v___x_3507_);
v_sz_boxed_3517_ = lean_unbox_usize(v_sz_3510_);
lean_dec(v_sz_3510_);
v_i_boxed_3518_ = lean_unbox_usize(v_i_3511_);
lean_dec(v_i_3511_);
v_res_3519_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6(v___x_3506_, v___x_9153__boxed_3516_, v___x_3508_, v_as_3509_, v_sz_boxed_3517_, v_i_boxed_3518_, v_b_3512_, v___y_3513_, v___y_3514_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec_ref(v_as_3509_);
lean_dec_ref(v___x_3508_);
lean_dec(v___x_3506_);
return v_res_3519_;
}
}
static lean_object* _init_l_Lean_Linter_MissingDocs_checkDecl___closed__0(void){
_start:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3520_ = lean_box(0);
v___x_3521_ = lean_unsigned_to_nat(16u);
v___x_3522_ = lean_mk_array(v___x_3521_, v___x_3520_);
return v___x_3522_;
}
}
static lean_object* _init_l_Lean_Linter_MissingDocs_checkDecl___closed__1(void){
_start:
{
lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3523_ = lean_obj_once(&l_Lean_Linter_MissingDocs_checkDecl___closed__0, &l_Lean_Linter_MissingDocs_checkDecl___closed__0_once, _init_l_Lean_Linter_MissingDocs_checkDecl___closed__0);
v___x_3524_ = lean_unsigned_to_nat(0u);
v___x_3525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3524_);
lean_ctor_set(v___x_3525_, 1, v___x_3523_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkDecl(lean_object* v_stx_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_){
_start:
{
lean_object* v___x_3530_; lean_object* v_head_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; uint8_t v___x_3537_; 
v___x_3530_ = lean_unsigned_to_nat(0u);
v_head_3531_ = l_Lean_Syntax_getArg(v_stx_3526_, v___x_3530_);
v___x_3532_ = lean_unsigned_to_nat(2u);
v___x_3533_ = l_Lean_Syntax_getArg(v_head_3531_, v___x_3532_);
v___x_3534_ = l_Lean_Syntax_getArg(v___x_3533_, v___x_3530_);
lean_dec(v___x_3533_);
v___x_3535_ = l_Lean_Syntax_getKind(v___x_3534_);
v___x_3536_ = ((lean_object*)(l_Lean_Linter_MissingDocs_declModifiersDocStatus___closed__0));
v___x_3537_ = lean_name_eq(v___x_3535_, v___x_3536_);
lean_dec(v___x_3535_);
if (v___x_3537_ == 0)
{
lean_object* v___x_3538_; lean_object* v_rest_3539_; lean_object* v___y_3541_; lean_object* v___y_3542_; uint8_t v___y_3543_; uint8_t v___x_3575_; lean_object* v_k_3576_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___x_3615_; 
v___x_3538_ = lean_unsigned_to_nat(1u);
v_rest_3539_ = l_Lean_Syntax_getArg(v_stx_3526_, v___x_3538_);
v___x_3575_ = 1;
lean_inc(v_rest_3539_);
v_k_3576_ = l_Lean_Syntax_getKind(v_rest_3539_);
v___x_3615_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v_head_3531_, v_a_3527_, v_a_3528_);
lean_dec(v_head_3531_);
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v_a_3616_; 
v_a_3616_ = lean_ctor_get(v___x_3615_, 0);
lean_inc(v_a_3616_);
lean_dec_ref_known(v___x_3615_, 1);
if (lean_obj_tag(v_a_3616_) == 1)
{
lean_object* v_val_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; uint8_t v___x_3620_; lean_object* v___x_3621_; 
v_val_3617_ = lean_ctor_get(v_a_3616_, 0);
lean_inc(v_val_3617_);
lean_dec_ref_known(v_a_3616_, 1);
v___x_3618_ = l_Lean_Syntax_getArg(v_rest_3539_, v___x_3538_);
v___x_3619_ = l_Lean_Syntax_getArg(v___x_3618_, v___x_3530_);
lean_dec(v___x_3618_);
v___x_3620_ = lean_unbox(v_val_3617_);
lean_dec(v_val_3617_);
v___x_3621_ = l_Lean_Linter_MissingDocs_lintDeclHead(v_k_3576_, v___x_3619_, v___x_3620_, v_a_3527_, v_a_3528_);
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_dec_ref_known(v___x_3621_, 1);
v___y_3578_ = v_a_3527_;
v___y_3579_ = v_a_3528_;
goto v___jp_3577_;
}
else
{
lean_dec(v_k_3576_);
lean_dec(v_rest_3539_);
return v___x_3621_;
}
}
else
{
lean_dec(v_a_3616_);
v___y_3578_ = v_a_3527_;
v___y_3579_ = v_a_3528_;
goto v___jp_3577_;
}
}
else
{
lean_object* v_a_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3629_; 
lean_dec(v_k_3576_);
lean_dec(v_rest_3539_);
v_a_3622_ = lean_ctor_get(v___x_3615_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3624_ = v___x_3615_;
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_a_3622_);
lean_dec(v___x_3615_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3627_; 
if (v_isShared_3625_ == 0)
{
v___x_3627_ = v___x_3624_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_a_3622_);
v___x_3627_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
return v___x_3627_;
}
}
}
v___jp_3540_:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; size_t v_sz_3548_; size_t v___x_3549_; lean_object* v___x_3550_; 
v___x_3544_ = lean_unsigned_to_nat(4u);
v___x_3545_ = l_Lean_Syntax_getArg(v_rest_3539_, v___x_3544_);
v___x_3546_ = l_Lean_Syntax_getArgs(v___x_3545_);
lean_dec(v___x_3545_);
v___x_3547_ = lean_box(0);
v_sz_3548_ = lean_array_size(v___x_3546_);
v___x_3549_ = ((size_t)0ULL);
v___x_3550_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__0(v_rest_3539_, v___x_3537_, v___y_3543_, v___x_3546_, v_sz_3548_, v___x_3549_, v___x_3547_, v___y_3541_, v___y_3542_);
lean_dec_ref(v___x_3546_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3573_; 
v_isSharedCheck_3573_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3573_ == 0)
{
lean_object* v_unused_3574_; 
v_unused_3574_ = lean_ctor_get(v___x_3550_, 0);
lean_dec(v_unused_3574_);
v___x_3552_ = v___x_3550_;
v_isShared_3553_ = v_isSharedCheck_3573_;
goto v_resetjp_3551_;
}
else
{
lean_dec(v___x_3550_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3573_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; uint8_t v___x_3556_; 
v___x_3554_ = lean_unsigned_to_nat(5u);
v___x_3555_ = l_Lean_Syntax_getArg(v_rest_3539_, v___x_3554_);
v___x_3556_ = l_Lean_Syntax_isNone(v___x_3555_);
if (v___x_3556_ == 0)
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; size_t v_sz_3560_; lean_object* v___x_3561_; 
lean_del_object(v___x_3552_);
v___x_3557_ = l_Lean_Syntax_getArg(v___x_3555_, v___x_3530_);
lean_dec(v___x_3555_);
v___x_3558_ = l_Lean_Syntax_getArg(v___x_3557_, v___x_3538_);
lean_dec(v___x_3557_);
v___x_3559_ = l_Lean_Syntax_getArgs(v___x_3558_);
lean_dec(v___x_3558_);
v_sz_3560_ = lean_array_size(v___x_3559_);
v___x_3561_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__1(v_rest_3539_, v___x_3559_, v_sz_3560_, v___x_3549_, v___x_3547_, v___y_3541_, v___y_3542_);
lean_dec_ref(v___x_3559_);
lean_dec(v_rest_3539_);
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3568_; 
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3568_ == 0)
{
lean_object* v_unused_3569_; 
v_unused_3569_ = lean_ctor_get(v___x_3561_, 0);
lean_dec(v_unused_3569_);
v___x_3563_ = v___x_3561_;
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
else
{
lean_dec(v___x_3561_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3566_; 
if (v_isShared_3564_ == 0)
{
lean_ctor_set(v___x_3563_, 0, v___x_3547_);
v___x_3566_ = v___x_3563_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v___x_3547_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
else
{
return v___x_3561_;
}
}
else
{
lean_object* v___x_3571_; 
lean_dec(v___x_3555_);
lean_dec(v_rest_3539_);
if (v_isShared_3553_ == 0)
{
lean_ctor_set(v___x_3552_, 0, v___x_3547_);
v___x_3571_ = v___x_3552_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v___x_3547_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
return v___x_3571_;
}
}
}
}
else
{
lean_dec(v_rest_3539_);
return v___x_3550_;
}
}
v___jp_3577_:
{
lean_object* v___x_3580_; uint8_t v___x_3581_; 
v___x_3580_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__9));
v___x_3581_ = lean_name_eq(v_k_3576_, v___x_3580_);
if (v___x_3581_ == 0)
{
lean_object* v___x_3582_; uint8_t v___x_3583_; 
v___x_3582_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__11));
v___x_3583_ = lean_name_eq(v_k_3576_, v___x_3582_);
if (v___x_3583_ == 0)
{
lean_object* v___x_3584_; uint8_t v___x_3585_; 
v___x_3584_ = ((lean_object*)(l_Lean_Linter_MissingDocs_lintDeclHead___closed__13));
v___x_3585_ = lean_name_eq(v_k_3576_, v___x_3584_);
lean_dec(v_k_3576_);
if (v___x_3585_ == 0)
{
lean_object* v___x_3586_; lean_object* v___x_3587_; 
lean_dec(v_rest_3539_);
v___x_3586_ = lean_box(0);
v___x_3587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3586_);
return v___x_3587_;
}
else
{
lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; uint8_t v___x_3591_; 
v___x_3588_ = lean_unsigned_to_nat(4u);
v___x_3589_ = l_Lean_Syntax_getArg(v_rest_3539_, v___x_3588_);
v___x_3590_ = l_Lean_Syntax_getArg(v___x_3589_, v___x_3532_);
lean_dec(v___x_3589_);
v___x_3591_ = l_Lean_Syntax_isNone(v___x_3590_);
if (v___x_3591_ == 0)
{
lean_object* v___x_3592_; lean_object* v_infoState_3593_; lean_object* v_trees_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; size_t v_sz_3602_; size_t v___x_3603_; lean_object* v___x_3604_; 
v___x_3592_ = lean_st_ref_get(v___y_3579_);
v_infoState_3593_ = lean_ctor_get(v___x_3592_, 8);
lean_inc_ref(v_infoState_3593_);
lean_dec(v___x_3592_);
v_trees_3594_ = lean_ctor_get(v_infoState_3593_, 2);
lean_inc_ref(v_trees_3594_);
lean_dec_ref(v_infoState_3593_);
v___x_3595_ = lean_obj_once(&l_Lean_Linter_MissingDocs_checkDecl___closed__1, &l_Lean_Linter_MissingDocs_checkDecl___closed__1_once, _init_l_Lean_Linter_MissingDocs_checkDecl___closed__1);
v___x_3596_ = l_Lean_PersistentArray_foldlM___at___00Lean_Linter_MissingDocs_checkDecl_spec__3(v___x_3591_, v_trees_3594_, v___x_3595_, v___x_3530_);
lean_dec_ref(v_trees_3594_);
v___x_3597_ = l_Lean_Syntax_getArg(v_rest_3539_, v___x_3538_);
lean_dec(v_rest_3539_);
v___x_3598_ = l_Lean_Syntax_getArg(v___x_3597_, v___x_3530_);
lean_dec(v___x_3597_);
v___x_3599_ = l_Lean_Syntax_getArg(v___x_3590_, v___x_3530_);
lean_dec(v___x_3590_);
v___x_3600_ = l_Lean_Syntax_getArgs(v___x_3599_);
lean_dec(v___x_3599_);
v___x_3601_ = lean_box(0);
v_sz_3602_ = lean_array_size(v___x_3600_);
v___x_3603_ = ((size_t)0ULL);
v___x_3604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_MissingDocs_checkDecl_spec__6(v___x_3598_, v___x_3591_, v___x_3596_, v___x_3600_, v_sz_3602_, v___x_3603_, v___x_3601_, v___y_3578_, v___y_3579_);
lean_dec_ref(v___x_3600_);
lean_dec_ref(v___x_3596_);
lean_dec(v___x_3598_);
if (lean_obj_tag(v___x_3604_) == 0)
{
lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3611_; 
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3611_ == 0)
{
lean_object* v_unused_3612_; 
v_unused_3612_ = lean_ctor_get(v___x_3604_, 0);
lean_dec(v_unused_3612_);
v___x_3606_ = v___x_3604_;
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
else
{
lean_dec(v___x_3604_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3609_; 
if (v_isShared_3607_ == 0)
{
lean_ctor_set(v___x_3606_, 0, v___x_3601_);
v___x_3609_ = v___x_3606_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3601_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
else
{
return v___x_3604_;
}
}
else
{
lean_object* v___x_3613_; lean_object* v___x_3614_; 
lean_dec(v___x_3590_);
lean_dec(v_rest_3539_);
v___x_3613_ = lean_box(0);
v___x_3614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3613_);
return v___x_3614_;
}
}
}
else
{
lean_dec(v_k_3576_);
v___y_3541_ = v___y_3578_;
v___y_3542_ = v___y_3579_;
v___y_3543_ = v___x_3583_;
goto v___jp_3540_;
}
}
else
{
lean_dec(v_k_3576_);
v___y_3541_ = v___y_3578_;
v___y_3542_ = v___y_3579_;
v___y_3543_ = v___x_3575_;
goto v___jp_3540_;
}
}
}
else
{
lean_object* v___x_3630_; lean_object* v___x_3631_; 
lean_dec(v_head_3531_);
v___x_3630_ = lean_box(0);
v___x_3631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3631_, 0, v___x_3630_);
return v___x_3631_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkDecl___boxed(lean_object* v_stx_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_){
_start:
{
lean_object* v_res_3636_; 
v_res_3636_ = l_Lean_Linter_MissingDocs_checkDecl(v_stx_3632_, v_a_3633_, v_a_3634_);
lean_dec(v_a_3634_);
lean_dec_ref(v_a_3633_);
lean_dec(v_stx_3632_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2(lean_object* v_00_u03b2_3637_, lean_object* v_m_3638_, lean_object* v_a_3639_, lean_object* v_b_3640_){
_start:
{
lean_object* v___x_3641_; 
v___x_3641_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2___redArg(v_m_3638_, v_a_3639_, v_b_3640_);
return v___x_3641_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4(lean_object* v_00_u03b2_3642_, lean_object* v_m_3643_, lean_object* v_a_3644_){
_start:
{
uint8_t v___x_3645_; 
v___x_3645_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___redArg(v_m_3643_, v_a_3644_);
return v___x_3645_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4___boxed(lean_object* v_00_u03b2_3646_, lean_object* v_m_3647_, lean_object* v_a_3648_){
_start:
{
uint8_t v_res_3649_; lean_object* v_r_3650_; 
v_res_3649_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_MissingDocs_checkDecl_spec__4(v_00_u03b2_3646_, v_m_3647_, v_a_3648_);
lean_dec(v_a_3648_);
lean_dec_ref(v_m_3647_);
v_r_3650_ = lean_box(v_res_3649_);
return v_r_3650_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2(lean_object* v_00_u03b2_3651_, lean_object* v_a_3652_, lean_object* v_x_3653_){
_start:
{
uint8_t v___x_3654_; 
v___x_3654_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2___redArg(v_a_3652_, v_x_3653_);
return v___x_3654_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2___boxed(lean_object* v_00_u03b2_3655_, lean_object* v_a_3656_, lean_object* v_x_3657_){
_start:
{
uint8_t v_res_3658_; lean_object* v_r_3659_; 
v_res_3658_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__2(v_00_u03b2_3655_, v_a_3656_, v_x_3657_);
lean_dec(v_x_3657_);
lean_dec(v_a_3656_);
v_r_3659_ = lean_box(v_res_3658_);
return v_r_3659_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3(lean_object* v_00_u03b2_3660_, lean_object* v_data_3661_){
_start:
{
lean_object* v___x_3662_; 
v___x_3662_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3___redArg(v_data_3661_);
return v___x_3662_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_3663_, lean_object* v_i_3664_, lean_object* v_source_3665_, lean_object* v_target_3666_){
_start:
{
lean_object* v___x_3667_; 
v___x_3667_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4___redArg(v_i_3664_, v_source_3665_, v_target_3666_);
return v___x_3667_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_3668_, lean_object* v_x_3669_, lean_object* v_x_3670_){
_start:
{
lean_object* v___x_3671_; 
v___x_3671_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_MissingDocs_checkDecl_spec__2_spec__3_spec__4_spec__9___redArg(v_x_3669_, v_x_3670_);
return v___x_3671_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__2(void){
_start:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3678_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkDecl___boxed), 4, 0);
v___x_3679_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_3679_, 0, v___x_3678_);
return v___x_3679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1(){
_start:
{
lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; 
v___x_3681_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__1));
v___x_3682_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__2, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__2_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___closed__2);
v___x_3683_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_3681_, v___x_3682_);
return v___x_3683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1___boxed(lean_object* v_a_3684_){
_start:
{
lean_object* v_res_3685_; 
v_res_3685_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkDecl___regBuiltin_Lean_Linter_MissingDocs_checkDecl__1();
return v_res_3685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkInit(lean_object* v_stx_3687_, lean_object* v_a_3688_, lean_object* v_a_3689_){
_start:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; uint8_t v___x_3693_; 
v___x_3691_ = lean_unsigned_to_nat(2u);
v___x_3692_ = l_Lean_Syntax_getArg(v_stx_3687_, v___x_3691_);
v___x_3693_ = l_Lean_Syntax_isNone(v___x_3692_);
if (v___x_3693_ == 0)
{
lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
v___x_3694_ = lean_unsigned_to_nat(0u);
v___x_3695_ = l_Lean_Syntax_getArg(v_stx_3687_, v___x_3694_);
v___x_3696_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v___x_3695_, v_a_3688_, v_a_3689_);
lean_dec(v___x_3695_);
if (lean_obj_tag(v___x_3696_) == 0)
{
lean_object* v_a_3697_; lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3710_; 
v_a_3697_ = lean_ctor_get(v___x_3696_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3696_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3699_ = v___x_3696_;
v_isShared_3700_ = v_isSharedCheck_3710_;
goto v_resetjp_3698_;
}
else
{
lean_inc(v_a_3697_);
lean_dec(v___x_3696_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3710_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
if (lean_obj_tag(v_a_3697_) == 1)
{
lean_object* v_val_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; uint8_t v___x_3704_; lean_object* v___x_3705_; 
lean_del_object(v___x_3699_);
v_val_3701_ = lean_ctor_get(v_a_3697_, 0);
lean_inc(v_val_3701_);
lean_dec_ref_known(v_a_3697_, 1);
v___x_3702_ = l_Lean_Syntax_getArg(v___x_3692_, v___x_3694_);
lean_dec(v___x_3692_);
v___x_3703_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkInit___closed__0));
v___x_3704_ = lean_unbox(v_val_3701_);
lean_dec(v_val_3701_);
v___x_3705_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v___x_3704_, v___x_3702_, v___x_3703_, v_a_3688_, v_a_3689_);
return v___x_3705_;
}
else
{
lean_object* v___x_3706_; lean_object* v___x_3708_; 
lean_dec(v_a_3697_);
lean_dec(v___x_3692_);
v___x_3706_ = lean_box(0);
if (v_isShared_3700_ == 0)
{
lean_ctor_set(v___x_3699_, 0, v___x_3706_);
v___x_3708_ = v___x_3699_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3706_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
}
}
else
{
lean_object* v_a_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3718_; 
lean_dec(v___x_3692_);
v_a_3711_ = lean_ctor_get(v___x_3696_, 0);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3696_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3713_ = v___x_3696_;
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_a_3711_);
lean_dec(v___x_3696_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3716_; 
if (v_isShared_3714_ == 0)
{
v___x_3716_ = v___x_3713_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_a_3711_);
v___x_3716_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
return v___x_3716_;
}
}
}
}
else
{
lean_object* v___x_3719_; lean_object* v___x_3720_; 
lean_dec(v___x_3692_);
v___x_3719_ = lean_box(0);
v___x_3720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3719_);
return v___x_3720_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkInit___boxed(lean_object* v_stx_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_){
_start:
{
lean_object* v_res_3725_; 
v_res_3725_ = l_Lean_Linter_MissingDocs_checkInit(v_stx_3721_, v_a_3722_, v_a_3723_);
lean_dec(v_a_3723_);
lean_dec_ref(v_a_3722_);
lean_dec(v_stx_3721_);
return v_res_3725_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__2(void){
_start:
{
lean_object* v___x_3732_; lean_object* v___x_3733_; 
v___x_3732_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkInit___boxed), 4, 0);
v___x_3733_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_3733_, 0, v___x_3732_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1(){
_start:
{
lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3735_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__1));
v___x_3736_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__2, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__2_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___closed__2);
v___x_3737_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_3735_, v___x_3736_);
return v___x_3737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1___boxed(lean_object* v_a_3738_){
_start:
{
lean_object* v_res_3739_; 
v_res_3739_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkInit___regBuiltin_Lean_Linter_MissingDocs_checkInit__1();
return v_res_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkNotation(lean_object* v_stx_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_){
_start:
{
lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; uint8_t v___x_3758_; 
v___x_3751_ = lean_unsigned_to_nat(2u);
v___x_3752_ = l_Lean_Syntax_getArg(v_stx_3747_, v___x_3751_);
v___x_3753_ = lean_unsigned_to_nat(0u);
v___x_3754_ = l_Lean_Syntax_getArg(v___x_3752_, v___x_3753_);
lean_dec(v___x_3752_);
v___x_3755_ = l_Lean_Syntax_getArg(v___x_3754_, v___x_3753_);
lean_dec(v___x_3754_);
v___x_3756_ = l_Lean_Syntax_getKind(v___x_3755_);
v___x_3757_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkNotation___closed__1));
v___x_3758_ = lean_name_eq(v___x_3756_, v___x_3757_);
lean_dec(v___x_3756_);
if (v___x_3758_ == 0)
{
lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; 
v___x_3759_ = l_Lean_Syntax_getArg(v_stx_3747_, v___x_3753_);
v___x_3760_ = lean_unsigned_to_nat(1u);
v___x_3761_ = l_Lean_Syntax_getArg(v_stx_3747_, v___x_3760_);
v___x_3762_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus(v___x_3759_, v___x_3761_, v___x_3758_, v_a_3748_, v_a_3749_);
lean_dec(v___x_3761_);
lean_dec(v___x_3759_);
if (lean_obj_tag(v___x_3762_) == 0)
{
lean_object* v_a_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3786_; 
v_a_3763_ = lean_ctor_get(v___x_3762_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___x_3762_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3765_ = v___x_3762_;
v_isShared_3766_ = v_isSharedCheck_3786_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_a_3763_);
lean_dec(v___x_3762_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3786_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
if (lean_obj_tag(v_a_3763_) == 1)
{
lean_object* v_val_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; uint8_t v___x_3770_; 
lean_del_object(v___x_3765_);
v_val_3767_ = lean_ctor_get(v_a_3763_, 0);
lean_inc(v_val_3767_);
lean_dec_ref_known(v_a_3763_, 1);
v___x_3768_ = lean_unsigned_to_nat(5u);
v___x_3769_ = l_Lean_Syntax_getArg(v_stx_3747_, v___x_3768_);
v___x_3770_ = l_Lean_Syntax_isNone(v___x_3769_);
if (v___x_3770_ == 0)
{
lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; uint8_t v___x_3775_; lean_object* v___x_3776_; 
v___x_3771_ = l_Lean_Syntax_getArg(v___x_3769_, v___x_3753_);
lean_dec(v___x_3769_);
v___x_3772_ = lean_unsigned_to_nat(3u);
v___x_3773_ = l_Lean_Syntax_getArg(v___x_3771_, v___x_3772_);
lean_dec(v___x_3771_);
v___x_3774_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkNotation___closed__2));
v___x_3775_ = lean_unbox(v_val_3767_);
lean_dec(v_val_3767_);
v___x_3776_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v___x_3775_, v___x_3773_, v___x_3774_, v_a_3748_, v_a_3749_);
return v___x_3776_;
}
else
{
lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; uint8_t v___x_3780_; lean_object* v___x_3781_; 
lean_dec(v___x_3769_);
v___x_3777_ = lean_unsigned_to_nat(3u);
v___x_3778_ = l_Lean_Syntax_getArg(v_stx_3747_, v___x_3777_);
v___x_3779_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkNotation___closed__2));
v___x_3780_ = lean_unbox(v_val_3767_);
lean_dec(v_val_3767_);
v___x_3781_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus(v___x_3780_, v___x_3778_, v___x_3779_, v_a_3748_, v_a_3749_);
return v___x_3781_;
}
}
else
{
lean_object* v___x_3782_; lean_object* v___x_3784_; 
lean_dec(v_a_3763_);
v___x_3782_ = lean_box(0);
if (v_isShared_3766_ == 0)
{
lean_ctor_set(v___x_3765_, 0, v___x_3782_);
v___x_3784_ = v___x_3765_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v___x_3782_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
}
else
{
lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3794_; 
v_a_3787_ = lean_ctor_get(v___x_3762_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3762_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3789_ = v___x_3762_;
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_dec(v___x_3762_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v___x_3792_; 
if (v_isShared_3790_ == 0)
{
v___x_3792_ = v___x_3789_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_a_3787_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
}
else
{
lean_object* v___x_3795_; lean_object* v___x_3796_; 
v___x_3795_ = lean_box(0);
v___x_3796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3796_, 0, v___x_3795_);
return v___x_3796_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkNotation___boxed(lean_object* v_stx_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_){
_start:
{
lean_object* v_res_3801_; 
v_res_3801_ = l_Lean_Linter_MissingDocs_checkNotation(v_stx_3797_, v_a_3798_, v_a_3799_);
lean_dec(v_a_3799_);
lean_dec_ref(v_a_3798_);
lean_dec(v_stx_3797_);
return v_res_3801_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___closed__1(void){
_start:
{
lean_object* v___x_3807_; lean_object* v___x_3808_; 
v___x_3807_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkNotation___boxed), 4, 0);
v___x_3808_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_3808_, 0, v___x_3807_);
return v___x_3808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1(){
_start:
{
lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; 
v___x_3810_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___closed__0));
v___x_3811_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___closed__1, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___closed__1_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___closed__1);
v___x_3812_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_3810_, v___x_3811_);
return v___x_3812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1___boxed(lean_object* v_a_3813_){
_start:
{
lean_object* v_res_3814_; 
v_res_3814_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkNotation___regBuiltin_Lean_Linter_MissingDocs_checkNotation__1();
return v_res_3814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkMixfix(lean_object* v_stx_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_){
_start:
{
lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; uint8_t v___x_3826_; 
v___x_3819_ = lean_unsigned_to_nat(2u);
v___x_3820_ = l_Lean_Syntax_getArg(v_stx_3815_, v___x_3819_);
v___x_3821_ = lean_unsigned_to_nat(0u);
v___x_3822_ = l_Lean_Syntax_getArg(v___x_3820_, v___x_3821_);
lean_dec(v___x_3820_);
v___x_3823_ = l_Lean_Syntax_getArg(v___x_3822_, v___x_3821_);
lean_dec(v___x_3822_);
v___x_3824_ = l_Lean_Syntax_getKind(v___x_3823_);
v___x_3825_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkNotation___closed__1));
v___x_3826_ = lean_name_eq(v___x_3824_, v___x_3825_);
lean_dec(v___x_3824_);
if (v___x_3826_ == 0)
{
lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; 
v___x_3827_ = l_Lean_Syntax_getArg(v_stx_3815_, v___x_3821_);
v___x_3828_ = lean_unsigned_to_nat(1u);
v___x_3829_ = l_Lean_Syntax_getArg(v_stx_3815_, v___x_3828_);
v___x_3830_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus(v___x_3827_, v___x_3829_, v___x_3826_, v_a_3816_, v_a_3817_);
lean_dec(v___x_3829_);
lean_dec(v___x_3827_);
if (lean_obj_tag(v___x_3830_) == 0)
{
lean_object* v_a_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3857_; 
v_a_3831_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3857_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3833_ = v___x_3830_;
v_isShared_3834_ = v_isSharedCheck_3857_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_a_3831_);
lean_dec(v___x_3830_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3857_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
if (lean_obj_tag(v_a_3831_) == 1)
{
lean_object* v_val_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; uint8_t v___x_3838_; 
lean_del_object(v___x_3833_);
v_val_3835_ = lean_ctor_get(v_a_3831_, 0);
lean_inc(v_val_3835_);
lean_dec_ref_known(v_a_3831_, 1);
v___x_3836_ = lean_unsigned_to_nat(5u);
v___x_3837_ = l_Lean_Syntax_getArg(v_stx_3815_, v___x_3836_);
v___x_3838_ = l_Lean_Syntax_isNone(v___x_3837_);
if (v___x_3838_ == 0)
{
lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; uint8_t v___x_3845_; lean_object* v___x_3846_; 
v___x_3839_ = l_Lean_Syntax_getArg(v___x_3837_, v___x_3821_);
lean_dec(v___x_3837_);
v___x_3840_ = lean_unsigned_to_nat(3u);
v___x_3841_ = l_Lean_Syntax_getArg(v___x_3839_, v___x_3840_);
lean_dec(v___x_3839_);
v___x_3842_ = l_Lean_Syntax_getArg(v_stx_3815_, v___x_3840_);
v___x_3843_ = l_Lean_Syntax_getArg(v___x_3842_, v___x_3821_);
lean_dec(v___x_3842_);
v___x_3844_ = l_Lean_Syntax_getAtomVal(v___x_3843_);
lean_dec(v___x_3843_);
v___x_3845_ = lean_unbox(v_val_3835_);
lean_dec(v_val_3835_);
v___x_3846_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v___x_3845_, v___x_3841_, v___x_3844_, v_a_3816_, v_a_3817_);
return v___x_3846_;
}
else
{
lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; uint8_t v___x_3851_; lean_object* v___x_3852_; 
lean_dec(v___x_3837_);
v___x_3847_ = lean_unsigned_to_nat(3u);
v___x_3848_ = l_Lean_Syntax_getArg(v_stx_3815_, v___x_3847_);
v___x_3849_ = l_Lean_Syntax_getArg(v___x_3848_, v___x_3821_);
v___x_3850_ = l_Lean_Syntax_getAtomVal(v___x_3849_);
lean_dec(v___x_3849_);
v___x_3851_ = lean_unbox(v_val_3835_);
lean_dec(v_val_3835_);
v___x_3852_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus(v___x_3851_, v___x_3848_, v___x_3850_, v_a_3816_, v_a_3817_);
return v___x_3852_;
}
}
else
{
lean_object* v___x_3853_; lean_object* v___x_3855_; 
lean_dec(v_a_3831_);
v___x_3853_ = lean_box(0);
if (v_isShared_3834_ == 0)
{
lean_ctor_set(v___x_3833_, 0, v___x_3853_);
v___x_3855_ = v___x_3833_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v___x_3853_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
}
else
{
lean_object* v_a_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3865_; 
v_a_3858_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3860_ = v___x_3830_;
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_a_3858_);
lean_dec(v___x_3830_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
lean_object* v___x_3863_; 
if (v_isShared_3861_ == 0)
{
v___x_3863_ = v___x_3860_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v_a_3858_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
return v___x_3863_;
}
}
}
}
else
{
lean_object* v___x_3866_; lean_object* v___x_3867_; 
v___x_3866_ = lean_box(0);
v___x_3867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3867_, 0, v___x_3866_);
return v___x_3867_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkMixfix___boxed(lean_object* v_stx_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_){
_start:
{
lean_object* v_res_3872_; 
v_res_3872_ = l_Lean_Linter_MissingDocs_checkMixfix(v_stx_3868_, v_a_3869_, v_a_3870_);
lean_dec(v_a_3870_);
lean_dec_ref(v_a_3869_);
lean_dec(v_stx_3868_);
return v_res_3872_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__2(void){
_start:
{
lean_object* v___x_3879_; lean_object* v___x_3880_; 
v___x_3879_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkMixfix___boxed), 4, 0);
v___x_3880_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_3880_, 0, v___x_3879_);
return v___x_3880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1(){
_start:
{
lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v___x_3882_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__1));
v___x_3883_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__2, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__2_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___closed__2);
v___x_3884_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_3882_, v___x_3883_);
return v___x_3884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1___boxed(lean_object* v_a_3885_){
_start:
{
lean_object* v_res_3886_; 
v_res_3886_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMixfix___regBuiltin_Lean_Linter_MissingDocs_checkMixfix__1();
return v_res_3886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntax(lean_object* v_stx_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_){
_start:
{
lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; uint8_t v___x_3899_; 
v___x_3892_ = lean_unsigned_to_nat(2u);
v___x_3893_ = l_Lean_Syntax_getArg(v_stx_3888_, v___x_3892_);
v___x_3894_ = lean_unsigned_to_nat(0u);
v___x_3895_ = l_Lean_Syntax_getArg(v___x_3893_, v___x_3894_);
lean_dec(v___x_3893_);
v___x_3896_ = l_Lean_Syntax_getArg(v___x_3895_, v___x_3894_);
lean_dec(v___x_3895_);
v___x_3897_ = l_Lean_Syntax_getKind(v___x_3896_);
v___x_3898_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkNotation___closed__1));
v___x_3899_ = lean_name_eq(v___x_3897_, v___x_3898_);
lean_dec(v___x_3897_);
if (v___x_3899_ == 0)
{
uint8_t v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; 
v___x_3900_ = 1;
v___x_3901_ = l_Lean_Syntax_getArg(v_stx_3888_, v___x_3894_);
v___x_3902_ = lean_unsigned_to_nat(1u);
v___x_3903_ = l_Lean_Syntax_getArg(v_stx_3888_, v___x_3902_);
v___x_3904_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus(v___x_3901_, v___x_3903_, v___x_3900_, v_a_3889_, v_a_3890_);
lean_dec(v___x_3903_);
lean_dec(v___x_3901_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v_a_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3928_; 
v_a_3905_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3907_ = v___x_3904_;
v_isShared_3908_ = v_isSharedCheck_3928_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_a_3905_);
lean_dec(v___x_3904_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3928_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
if (lean_obj_tag(v_a_3905_) == 1)
{
lean_object* v_val_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; uint8_t v___x_3912_; 
lean_del_object(v___x_3907_);
v_val_3909_ = lean_ctor_get(v_a_3905_, 0);
lean_inc(v_val_3909_);
lean_dec_ref_known(v_a_3905_, 1);
v___x_3910_ = lean_unsigned_to_nat(5u);
v___x_3911_ = l_Lean_Syntax_getArg(v_stx_3888_, v___x_3910_);
v___x_3912_ = l_Lean_Syntax_isNone(v___x_3911_);
if (v___x_3912_ == 0)
{
lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; uint8_t v___x_3917_; lean_object* v___x_3918_; 
v___x_3913_ = l_Lean_Syntax_getArg(v___x_3911_, v___x_3894_);
lean_dec(v___x_3911_);
v___x_3914_ = lean_unsigned_to_nat(3u);
v___x_3915_ = l_Lean_Syntax_getArg(v___x_3913_, v___x_3914_);
lean_dec(v___x_3913_);
v___x_3916_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkSyntax___closed__0));
v___x_3917_ = lean_unbox(v_val_3909_);
lean_dec(v_val_3909_);
v___x_3918_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v___x_3917_, v___x_3915_, v___x_3916_, v_a_3889_, v_a_3890_);
return v___x_3918_;
}
else
{
lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; uint8_t v___x_3922_; lean_object* v___x_3923_; 
lean_dec(v___x_3911_);
v___x_3919_ = lean_unsigned_to_nat(3u);
v___x_3920_ = l_Lean_Syntax_getArg(v_stx_3888_, v___x_3919_);
v___x_3921_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkSyntax___closed__0));
v___x_3922_ = lean_unbox(v_val_3909_);
lean_dec(v_val_3909_);
v___x_3923_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus(v___x_3922_, v___x_3920_, v___x_3921_, v_a_3889_, v_a_3890_);
return v___x_3923_;
}
}
else
{
lean_object* v___x_3924_; lean_object* v___x_3926_; 
lean_dec(v_a_3905_);
v___x_3924_ = lean_box(0);
if (v_isShared_3908_ == 0)
{
lean_ctor_set(v___x_3907_, 0, v___x_3924_);
v___x_3926_ = v___x_3907_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v___x_3924_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
return v___x_3926_;
}
}
}
}
else
{
lean_object* v_a_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3936_; 
v_a_3929_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3931_ = v___x_3904_;
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_a_3929_);
lean_dec(v___x_3904_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v___x_3934_; 
if (v_isShared_3932_ == 0)
{
v___x_3934_ = v___x_3931_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_a_3929_);
v___x_3934_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
return v___x_3934_;
}
}
}
}
else
{
lean_object* v___x_3937_; lean_object* v___x_3938_; 
v___x_3937_ = lean_box(0);
v___x_3938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3938_, 0, v___x_3937_);
return v___x_3938_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntax___boxed(lean_object* v_stx_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_){
_start:
{
lean_object* v_res_3943_; 
v_res_3943_ = l_Lean_Linter_MissingDocs_checkSyntax(v_stx_3939_, v_a_3940_, v_a_3941_);
lean_dec(v_a_3941_);
lean_dec_ref(v_a_3940_);
lean_dec(v_stx_3939_);
return v_res_3943_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___closed__1(void){
_start:
{
lean_object* v___x_3949_; lean_object* v___x_3950_; 
v___x_3949_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkSyntax___boxed), 4, 0);
v___x_3950_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_3950_, 0, v___x_3949_);
return v___x_3950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1(){
_start:
{
lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___x_3952_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___closed__0));
v___x_3953_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___closed__1, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___closed__1_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___closed__1);
v___x_3954_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_3952_, v___x_3953_);
return v___x_3954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1___boxed(lean_object* v_a_3955_){
_start:
{
lean_object* v_res_3956_; 
v_res_3956_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntax___regBuiltin_Lean_Linter_MissingDocs_checkSyntax__1();
return v_res_3956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_mkSimpleHandler(lean_object* v_name_3957_, lean_object* v_declNameStxIdx_3958_, lean_object* v_stx_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_){
_start:
{
lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3963_ = lean_unsigned_to_nat(0u);
v___x_3964_ = l_Lean_Syntax_getArg(v_stx_3959_, v___x_3963_);
v___x_3965_ = l_Lean_Linter_MissingDocs_isMissingDoc(v___x_3964_, v_a_3960_, v_a_3961_);
if (lean_obj_tag(v___x_3965_) == 0)
{
lean_object* v_a_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3990_; 
v_a_3966_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_3990_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_3990_ == 0)
{
v___x_3968_ = v___x_3965_;
v_isShared_3969_ = v_isSharedCheck_3990_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_a_3966_);
lean_dec(v___x_3965_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_3990_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
uint8_t v___x_3970_; 
v___x_3970_ = lean_unbox(v_a_3966_);
lean_dec(v_a_3966_);
if (v___x_3970_ == 0)
{
lean_object* v___x_3971_; lean_object* v___x_3973_; 
lean_dec(v___x_3964_);
lean_dec_ref(v_name_3957_);
v___x_3971_ = lean_box(0);
if (v_isShared_3969_ == 0)
{
lean_ctor_set(v___x_3968_, 0, v___x_3971_);
v___x_3973_ = v___x_3968_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v___x_3971_);
v___x_3973_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
return v___x_3973_;
}
}
else
{
lean_object* v___x_3975_; 
lean_del_object(v___x_3968_);
v___x_3975_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString(v___x_3964_, v_a_3960_, v_a_3961_);
lean_dec(v___x_3964_);
if (lean_obj_tag(v___x_3975_) == 0)
{
lean_object* v_a_3976_; uint8_t v___x_3977_; 
v_a_3976_ = lean_ctor_get(v___x_3975_, 0);
lean_inc(v_a_3976_);
lean_dec_ref_known(v___x_3975_, 1);
v___x_3977_ = lean_unbox(v_a_3976_);
lean_dec(v_a_3976_);
if (v___x_3977_ == 0)
{
lean_object* v___x_3978_; lean_object* v___x_3979_; 
v___x_3978_ = l_Lean_Syntax_getArg(v_stx_3959_, v_declNameStxIdx_3958_);
v___x_3979_ = l_Lean_Linter_MissingDocs_lintNamed(v___x_3978_, v_name_3957_, v_a_3960_, v_a_3961_);
return v___x_3979_;
}
else
{
lean_object* v___x_3980_; lean_object* v___x_3981_; 
v___x_3980_ = l_Lean_Syntax_getArg(v_stx_3959_, v_declNameStxIdx_3958_);
v___x_3981_ = l_Lean_Linter_MissingDocs_lintEmptyNamed(v___x_3980_, v_name_3957_, v_a_3960_, v_a_3961_);
return v___x_3981_;
}
}
else
{
lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3989_; 
lean_dec_ref(v_name_3957_);
v_a_3982_ = lean_ctor_get(v___x_3975_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3975_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3984_ = v___x_3975_;
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v___x_3975_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3987_; 
if (v_isShared_3985_ == 0)
{
v___x_3987_ = v___x_3984_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_a_3982_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
return v___x_3987_;
}
}
}
}
}
}
else
{
lean_object* v_a_3991_; lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_3998_; 
lean_dec(v___x_3964_);
lean_dec_ref(v_name_3957_);
v_a_3991_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_3998_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_3998_ == 0)
{
v___x_3993_ = v___x_3965_;
v_isShared_3994_ = v_isSharedCheck_3998_;
goto v_resetjp_3992_;
}
else
{
lean_inc(v_a_3991_);
lean_dec(v___x_3965_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_3998_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v___x_3996_; 
if (v_isShared_3994_ == 0)
{
v___x_3996_ = v___x_3993_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v_a_3991_);
v___x_3996_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
return v___x_3996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_mkSimpleHandler___boxed(lean_object* v_name_3999_, lean_object* v_declNameStxIdx_4000_, lean_object* v_stx_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_){
_start:
{
lean_object* v_res_4005_; 
v_res_4005_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v_name_3999_, v_declNameStxIdx_4000_, v_stx_4001_, v_a_4002_, v_a_4003_);
lean_dec(v_a_4003_);
lean_dec_ref(v_a_4002_);
lean_dec(v_stx_4001_);
lean_dec(v_declNameStxIdx_4000_);
return v_res_4005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntaxAbbrev(lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_){
_start:
{
lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; 
v___x_4010_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkSyntax___closed__0));
v___x_4011_ = lean_unsigned_to_nat(2u);
v___x_4012_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_4010_, v___x_4011_, v_a_4006_, v_a_4007_, v_a_4008_);
return v___x_4012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntaxAbbrev___boxed(lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_){
_start:
{
lean_object* v_res_4017_; 
v_res_4017_ = l_Lean_Linter_MissingDocs_checkSyntaxAbbrev(v_a_4013_, v_a_4014_, v_a_4015_);
lean_dec(v_a_4015_);
lean_dec_ref(v_a_4014_);
lean_dec(v_a_4013_);
return v_res_4017_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__2(void){
_start:
{
lean_object* v___x_4024_; lean_object* v___x_4025_; 
v___x_4024_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkSyntaxAbbrev___boxed), 4, 0);
v___x_4025_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4025_, 0, v___x_4024_);
return v___x_4025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1(){
_start:
{
lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; 
v___x_4027_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__1));
v___x_4028_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__2, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__2_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___closed__2);
v___x_4029_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4027_, v___x_4028_);
return v___x_4029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1___boxed(lean_object* v_a_4030_){
_start:
{
lean_object* v_res_4031_; 
v_res_4031_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxAbbrev__1();
return v_res_4031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntaxCat(lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_){
_start:
{
lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; 
v___x_4037_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkSyntaxCat___closed__0));
v___x_4038_ = lean_unsigned_to_nat(2u);
v___x_4039_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_4037_, v___x_4038_, v_a_4033_, v_a_4034_, v_a_4035_);
return v___x_4039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSyntaxCat___boxed(lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_){
_start:
{
lean_object* v_res_4044_; 
v_res_4044_ = l_Lean_Linter_MissingDocs_checkSyntaxCat(v_a_4040_, v_a_4041_, v_a_4042_);
lean_dec(v_a_4042_);
lean_dec_ref(v_a_4041_);
lean_dec(v_a_4040_);
return v_res_4044_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__2(void){
_start:
{
lean_object* v___x_4051_; lean_object* v___x_4052_; 
v___x_4051_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkSyntaxCat___boxed), 4, 0);
v___x_4052_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4052_, 0, v___x_4051_);
return v___x_4052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1(){
_start:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; 
v___x_4054_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__1));
v___x_4055_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__2, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__2_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___closed__2);
v___x_4056_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4054_, v___x_4055_);
return v___x_4056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1___boxed(lean_object* v_a_4057_){
_start:
{
lean_object* v_res_4058_; 
v_res_4058_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSyntaxCat___regBuiltin_Lean_Linter_MissingDocs_checkSyntaxCat__1();
return v_res_4058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkMacro(lean_object* v_stx_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_){
_start:
{
lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; uint8_t v___x_4071_; 
v___x_4064_ = lean_unsigned_to_nat(2u);
v___x_4065_ = l_Lean_Syntax_getArg(v_stx_4060_, v___x_4064_);
v___x_4066_ = lean_unsigned_to_nat(0u);
v___x_4067_ = l_Lean_Syntax_getArg(v___x_4065_, v___x_4066_);
lean_dec(v___x_4065_);
v___x_4068_ = l_Lean_Syntax_getArg(v___x_4067_, v___x_4066_);
lean_dec(v___x_4067_);
v___x_4069_ = l_Lean_Syntax_getKind(v___x_4068_);
v___x_4070_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkNotation___closed__1));
v___x_4071_ = lean_name_eq(v___x_4069_, v___x_4070_);
lean_dec(v___x_4069_);
if (v___x_4071_ == 0)
{
uint8_t v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
v___x_4072_ = 1;
v___x_4073_ = l_Lean_Syntax_getArg(v_stx_4060_, v___x_4066_);
v___x_4074_ = lean_unsigned_to_nat(1u);
v___x_4075_ = l_Lean_Syntax_getArg(v_stx_4060_, v___x_4074_);
v___x_4076_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus(v___x_4073_, v___x_4075_, v___x_4072_, v_a_4061_, v_a_4062_);
lean_dec(v___x_4075_);
lean_dec(v___x_4073_);
if (lean_obj_tag(v___x_4076_) == 0)
{
lean_object* v_a_4077_; lean_object* v___x_4079_; uint8_t v_isShared_4080_; uint8_t v_isSharedCheck_4100_; 
v_a_4077_ = lean_ctor_get(v___x_4076_, 0);
v_isSharedCheck_4100_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4100_ == 0)
{
v___x_4079_ = v___x_4076_;
v_isShared_4080_ = v_isSharedCheck_4100_;
goto v_resetjp_4078_;
}
else
{
lean_inc(v_a_4077_);
lean_dec(v___x_4076_);
v___x_4079_ = lean_box(0);
v_isShared_4080_ = v_isSharedCheck_4100_;
goto v_resetjp_4078_;
}
v_resetjp_4078_:
{
if (lean_obj_tag(v_a_4077_) == 1)
{
lean_object* v_val_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; uint8_t v___x_4084_; 
lean_del_object(v___x_4079_);
v_val_4081_ = lean_ctor_get(v_a_4077_, 0);
lean_inc(v_val_4081_);
lean_dec_ref_known(v_a_4077_, 1);
v___x_4082_ = lean_unsigned_to_nat(5u);
v___x_4083_ = l_Lean_Syntax_getArg(v_stx_4060_, v___x_4082_);
v___x_4084_ = l_Lean_Syntax_isNone(v___x_4083_);
if (v___x_4084_ == 0)
{
lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; uint8_t v___x_4089_; lean_object* v___x_4090_; 
v___x_4085_ = l_Lean_Syntax_getArg(v___x_4083_, v___x_4066_);
lean_dec(v___x_4083_);
v___x_4086_ = lean_unsigned_to_nat(3u);
v___x_4087_ = l_Lean_Syntax_getArg(v___x_4085_, v___x_4086_);
lean_dec(v___x_4085_);
v___x_4088_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkMacro___closed__0));
v___x_4089_ = lean_unbox(v_val_4081_);
lean_dec(v_val_4081_);
v___x_4090_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v___x_4089_, v___x_4087_, v___x_4088_, v_a_4061_, v_a_4062_);
return v___x_4090_;
}
else
{
lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; uint8_t v___x_4094_; lean_object* v___x_4095_; 
lean_dec(v___x_4083_);
v___x_4091_ = lean_unsigned_to_nat(3u);
v___x_4092_ = l_Lean_Syntax_getArg(v_stx_4060_, v___x_4091_);
v___x_4093_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkMacro___closed__0));
v___x_4094_ = lean_unbox(v_val_4081_);
lean_dec(v_val_4081_);
v___x_4095_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus(v___x_4094_, v___x_4092_, v___x_4093_, v_a_4061_, v_a_4062_);
return v___x_4095_;
}
}
else
{
lean_object* v___x_4096_; lean_object* v___x_4098_; 
lean_dec(v_a_4077_);
v___x_4096_ = lean_box(0);
if (v_isShared_4080_ == 0)
{
lean_ctor_set(v___x_4079_, 0, v___x_4096_);
v___x_4098_ = v___x_4079_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v___x_4096_);
v___x_4098_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
return v___x_4098_;
}
}
}
}
else
{
lean_object* v_a_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4108_; 
v_a_4101_ = lean_ctor_get(v___x_4076_, 0);
v_isSharedCheck_4108_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4108_ == 0)
{
v___x_4103_ = v___x_4076_;
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_a_4101_);
lean_dec(v___x_4076_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v___x_4106_; 
if (v_isShared_4104_ == 0)
{
v___x_4106_ = v___x_4103_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v_a_4101_);
v___x_4106_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
return v___x_4106_;
}
}
}
}
else
{
lean_object* v___x_4109_; lean_object* v___x_4110_; 
v___x_4109_ = lean_box(0);
v___x_4110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4109_);
return v___x_4110_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkMacro___boxed(lean_object* v_stx_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_){
_start:
{
lean_object* v_res_4115_; 
v_res_4115_ = l_Lean_Linter_MissingDocs_checkMacro(v_stx_4111_, v_a_4112_, v_a_4113_);
lean_dec(v_a_4113_);
lean_dec_ref(v_a_4112_);
lean_dec(v_stx_4111_);
return v_res_4115_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___closed__1(void){
_start:
{
lean_object* v___x_4121_; lean_object* v___x_4122_; 
v___x_4121_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkMacro___boxed), 4, 0);
v___x_4122_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4122_, 0, v___x_4121_);
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1(){
_start:
{
lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; 
v___x_4124_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___closed__0));
v___x_4125_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___closed__1, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___closed__1_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___closed__1);
v___x_4126_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4124_, v___x_4125_);
return v___x_4126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1___boxed(lean_object* v_a_4127_){
_start:
{
lean_object* v_res_4128_; 
v_res_4128_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkMacro___regBuiltin_Lean_Linter_MissingDocs_checkMacro__1();
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkElab(lean_object* v_stx_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_){
_start:
{
lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; uint8_t v___x_4141_; 
v___x_4134_ = lean_unsigned_to_nat(2u);
v___x_4135_ = l_Lean_Syntax_getArg(v_stx_4130_, v___x_4134_);
v___x_4136_ = lean_unsigned_to_nat(0u);
v___x_4137_ = l_Lean_Syntax_getArg(v___x_4135_, v___x_4136_);
lean_dec(v___x_4135_);
v___x_4138_ = l_Lean_Syntax_getArg(v___x_4137_, v___x_4136_);
lean_dec(v___x_4137_);
v___x_4139_ = l_Lean_Syntax_getKind(v___x_4138_);
v___x_4140_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkNotation___closed__1));
v___x_4141_ = lean_name_eq(v___x_4139_, v___x_4140_);
lean_dec(v___x_4139_);
if (v___x_4141_ == 0)
{
uint8_t v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; 
v___x_4142_ = 1;
v___x_4143_ = l_Lean_Syntax_getArg(v_stx_4130_, v___x_4136_);
v___x_4144_ = lean_unsigned_to_nat(1u);
v___x_4145_ = l_Lean_Syntax_getArg(v_stx_4130_, v___x_4144_);
v___x_4146_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_docOptStatus(v___x_4143_, v___x_4145_, v___x_4142_, v_a_4131_, v_a_4132_);
lean_dec(v___x_4145_);
lean_dec(v___x_4143_);
if (lean_obj_tag(v___x_4146_) == 0)
{
lean_object* v_a_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4170_; 
v_a_4147_ = lean_ctor_get(v___x_4146_, 0);
v_isSharedCheck_4170_ = !lean_is_exclusive(v___x_4146_);
if (v_isSharedCheck_4170_ == 0)
{
v___x_4149_ = v___x_4146_;
v_isShared_4150_ = v_isSharedCheck_4170_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_a_4147_);
lean_dec(v___x_4146_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4170_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
if (lean_obj_tag(v_a_4147_) == 1)
{
lean_object* v_val_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; uint8_t v___x_4154_; 
lean_del_object(v___x_4149_);
v_val_4151_ = lean_ctor_get(v_a_4147_, 0);
lean_inc(v_val_4151_);
lean_dec_ref_known(v_a_4147_, 1);
v___x_4152_ = lean_unsigned_to_nat(5u);
v___x_4153_ = l_Lean_Syntax_getArg(v_stx_4130_, v___x_4152_);
v___x_4154_ = l_Lean_Syntax_isNone(v___x_4153_);
if (v___x_4154_ == 0)
{
lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; uint8_t v___x_4159_; lean_object* v___x_4160_; 
v___x_4155_ = l_Lean_Syntax_getArg(v___x_4153_, v___x_4136_);
lean_dec(v___x_4153_);
v___x_4156_ = lean_unsigned_to_nat(3u);
v___x_4157_ = l_Lean_Syntax_getArg(v___x_4155_, v___x_4156_);
lean_dec(v___x_4155_);
v___x_4158_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkElab___closed__0));
v___x_4159_ = lean_unbox(v_val_4151_);
lean_dec(v_val_4151_);
v___x_4160_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v___x_4159_, v___x_4157_, v___x_4158_, v_a_4131_, v_a_4132_);
return v___x_4160_;
}
else
{
lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; uint8_t v___x_4164_; lean_object* v___x_4165_; 
lean_dec(v___x_4153_);
v___x_4161_ = lean_unsigned_to_nat(3u);
v___x_4162_ = l_Lean_Syntax_getArg(v_stx_4130_, v___x_4161_);
v___x_4163_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkElab___closed__0));
v___x_4164_ = lean_unbox(v_val_4151_);
lean_dec(v_val_4151_);
v___x_4165_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatus(v___x_4164_, v___x_4162_, v___x_4163_, v_a_4131_, v_a_4132_);
return v___x_4165_;
}
}
else
{
lean_object* v___x_4166_; lean_object* v___x_4168_; 
lean_dec(v_a_4147_);
v___x_4166_ = lean_box(0);
if (v_isShared_4150_ == 0)
{
lean_ctor_set(v___x_4149_, 0, v___x_4166_);
v___x_4168_ = v___x_4149_;
goto v_reusejp_4167_;
}
else
{
lean_object* v_reuseFailAlloc_4169_; 
v_reuseFailAlloc_4169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4169_, 0, v___x_4166_);
v___x_4168_ = v_reuseFailAlloc_4169_;
goto v_reusejp_4167_;
}
v_reusejp_4167_:
{
return v___x_4168_;
}
}
}
}
else
{
lean_object* v_a_4171_; lean_object* v___x_4173_; uint8_t v_isShared_4174_; uint8_t v_isSharedCheck_4178_; 
v_a_4171_ = lean_ctor_get(v___x_4146_, 0);
v_isSharedCheck_4178_ = !lean_is_exclusive(v___x_4146_);
if (v_isSharedCheck_4178_ == 0)
{
v___x_4173_ = v___x_4146_;
v_isShared_4174_ = v_isSharedCheck_4178_;
goto v_resetjp_4172_;
}
else
{
lean_inc(v_a_4171_);
lean_dec(v___x_4146_);
v___x_4173_ = lean_box(0);
v_isShared_4174_ = v_isSharedCheck_4178_;
goto v_resetjp_4172_;
}
v_resetjp_4172_:
{
lean_object* v___x_4176_; 
if (v_isShared_4174_ == 0)
{
v___x_4176_ = v___x_4173_;
goto v_reusejp_4175_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4177_, 0, v_a_4171_);
v___x_4176_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4175_;
}
v_reusejp_4175_:
{
return v___x_4176_;
}
}
}
}
else
{
lean_object* v___x_4179_; lean_object* v___x_4180_; 
v___x_4179_ = lean_box(0);
v___x_4180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4180_, 0, v___x_4179_);
return v___x_4180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkElab___boxed(lean_object* v_stx_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_){
_start:
{
lean_object* v_res_4185_; 
v_res_4185_ = l_Lean_Linter_MissingDocs_checkElab(v_stx_4181_, v_a_4182_, v_a_4183_);
lean_dec(v_a_4183_);
lean_dec_ref(v_a_4182_);
lean_dec(v_stx_4181_);
return v_res_4185_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___closed__1(void){
_start:
{
lean_object* v___x_4191_; lean_object* v___x_4192_; 
v___x_4191_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkElab___boxed), 4, 0);
v___x_4192_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4192_, 0, v___x_4191_);
return v___x_4192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1(){
_start:
{
lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; 
v___x_4194_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___closed__0));
v___x_4195_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___closed__1, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___closed__1_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___closed__1);
v___x_4196_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4194_, v___x_4195_);
return v___x_4196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1___boxed(lean_object* v_a_4197_){
_start:
{
lean_object* v_res_4198_; 
v_res_4198_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkElab___regBuiltin_Lean_Linter_MissingDocs_checkElab__1();
return v_res_4198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkClassAbbrev(lean_object* v_stx_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_){
_start:
{
lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; 
v___x_4204_ = lean_unsigned_to_nat(0u);
v___x_4205_ = l_Lean_Syntax_getArg(v_stx_4200_, v___x_4204_);
v___x_4206_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v___x_4205_, v_a_4201_, v_a_4202_);
lean_dec(v___x_4205_);
if (lean_obj_tag(v___x_4206_) == 0)
{
lean_object* v_a_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4221_; 
v_a_4207_ = lean_ctor_get(v___x_4206_, 0);
v_isSharedCheck_4221_ = !lean_is_exclusive(v___x_4206_);
if (v_isSharedCheck_4221_ == 0)
{
v___x_4209_ = v___x_4206_;
v_isShared_4210_ = v_isSharedCheck_4221_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_a_4207_);
lean_dec(v___x_4206_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4221_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
if (lean_obj_tag(v_a_4207_) == 1)
{
lean_object* v_val_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; uint8_t v___x_4215_; lean_object* v___x_4216_; 
lean_del_object(v___x_4209_);
v_val_4211_ = lean_ctor_get(v_a_4207_, 0);
lean_inc(v_val_4211_);
lean_dec_ref_known(v_a_4207_, 1);
v___x_4212_ = lean_unsigned_to_nat(3u);
v___x_4213_ = l_Lean_Syntax_getArg(v_stx_4200_, v___x_4212_);
v___x_4214_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkClassAbbrev___closed__0));
v___x_4215_ = lean_unbox(v_val_4211_);
lean_dec(v_val_4211_);
v___x_4216_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v___x_4215_, v___x_4213_, v___x_4214_, v_a_4201_, v_a_4202_);
return v___x_4216_;
}
else
{
lean_object* v___x_4217_; lean_object* v___x_4219_; 
lean_dec(v_a_4207_);
v___x_4217_ = lean_box(0);
if (v_isShared_4210_ == 0)
{
lean_ctor_set(v___x_4209_, 0, v___x_4217_);
v___x_4219_ = v___x_4209_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v___x_4217_);
v___x_4219_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
return v___x_4219_;
}
}
}
}
else
{
lean_object* v_a_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4229_; 
v_a_4222_ = lean_ctor_get(v___x_4206_, 0);
v_isSharedCheck_4229_ = !lean_is_exclusive(v___x_4206_);
if (v_isSharedCheck_4229_ == 0)
{
v___x_4224_ = v___x_4206_;
v_isShared_4225_ = v_isSharedCheck_4229_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_a_4222_);
lean_dec(v___x_4206_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4229_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v___x_4227_; 
if (v_isShared_4225_ == 0)
{
v___x_4227_ = v___x_4224_;
goto v_reusejp_4226_;
}
else
{
lean_object* v_reuseFailAlloc_4228_; 
v_reuseFailAlloc_4228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4228_, 0, v_a_4222_);
v___x_4227_ = v_reuseFailAlloc_4228_;
goto v_reusejp_4226_;
}
v_reusejp_4226_:
{
return v___x_4227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkClassAbbrev___boxed(lean_object* v_stx_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_){
_start:
{
lean_object* v_res_4234_; 
v_res_4234_ = l_Lean_Linter_MissingDocs_checkClassAbbrev(v_stx_4230_, v_a_4231_, v_a_4232_);
lean_dec(v_a_4232_);
lean_dec_ref(v_a_4231_);
lean_dec(v_stx_4230_);
return v_res_4234_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__2(void){
_start:
{
lean_object* v___x_4241_; lean_object* v___x_4242_; 
v___x_4241_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkClassAbbrev___boxed), 4, 0);
v___x_4242_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4242_, 0, v___x_4241_);
return v___x_4242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1(){
_start:
{
lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; 
v___x_4244_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__1));
v___x_4245_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__2, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__2_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___closed__2);
v___x_4246_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4244_, v___x_4245_);
return v___x_4246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1___boxed(lean_object* v_a_4247_){
_start:
{
lean_object* v_res_4248_; 
v_res_4248_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkClassAbbrev___regBuiltin_Lean_Linter_MissingDocs_checkClassAbbrev__1();
return v_res_4248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSimpLike(lean_object* v_a_4250_, lean_object* v_a_4251_, lean_object* v_a_4252_){
_start:
{
lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; 
v___x_4254_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkSimpLike___closed__0));
v___x_4255_ = lean_unsigned_to_nat(2u);
v___x_4256_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_4254_, v___x_4255_, v_a_4250_, v_a_4251_, v_a_4252_);
return v___x_4256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkSimpLike___boxed(lean_object* v_a_4257_, lean_object* v_a_4258_, lean_object* v_a_4259_, lean_object* v_a_4260_){
_start:
{
lean_object* v_res_4261_; 
v_res_4261_ = l_Lean_Linter_MissingDocs_checkSimpLike(v_a_4257_, v_a_4258_, v_a_4259_);
lean_dec(v_a_4259_);
lean_dec_ref(v_a_4258_);
lean_dec(v_a_4257_);
return v_res_4261_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__3(void){
_start:
{
lean_object* v___x_4269_; lean_object* v___x_4270_; 
v___x_4269_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkSimpLike___boxed), 4, 0);
v___x_4270_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4270_, 0, v___x_4269_);
return v___x_4270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1(){
_start:
{
lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; 
v___x_4272_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__2));
v___x_4273_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__3, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__3_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___closed__3);
v___x_4274_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4272_, v___x_4273_);
return v___x_4274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1___boxed(lean_object* v_a_4275_){
_start:
{
lean_object* v_res_4276_; 
v_res_4276_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkSimpLike___regBuiltin_Lean_Linter_MissingDocs_checkSimpLike__1();
return v_res_4276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption(lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_){
_start:
{
lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; 
v___x_4282_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption___closed__0));
v___x_4283_ = lean_unsigned_to_nat(3u);
v___x_4284_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_4282_, v___x_4283_, v_a_4278_, v_a_4279_, v_a_4280_);
return v___x_4284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption___boxed(lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_){
_start:
{
lean_object* v_res_4289_; 
v_res_4289_ = l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption(v_a_4285_, v_a_4286_, v_a_4287_);
lean_dec(v_a_4287_);
lean_dec_ref(v_a_4286_);
lean_dec(v_a_4285_);
return v_res_4289_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__3(void){
_start:
{
lean_object* v___x_4296_; lean_object* v___x_4297_; 
v___x_4296_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption___boxed), 4, 0);
v___x_4297_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4297_, 0, v___x_4296_);
return v___x_4297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1(){
_start:
{
lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; 
v___x_4299_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__2));
v___x_4300_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__3, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__3_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___closed__3);
v___x_4301_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4299_, v___x_4300_);
return v___x_4301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1___boxed(lean_object* v_a_4302_){
_start:
{
lean_object* v_res_4303_; 
v_res_4303_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterBuiltinOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterBuiltinOption__1();
return v_res_4303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterOption(lean_object* v_stx_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_){
_start:
{
lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; 
v___x_4308_ = lean_unsigned_to_nat(0u);
v___x_4309_ = l_Lean_Syntax_getArg(v_stx_4304_, v___x_4308_);
v___x_4310_ = l_Lean_Linter_MissingDocs_declModifiersDocStatus(v___x_4309_, v_a_4305_, v_a_4306_);
lean_dec(v___x_4309_);
if (lean_obj_tag(v___x_4310_) == 0)
{
lean_object* v_a_4311_; lean_object* v___x_4313_; uint8_t v_isShared_4314_; uint8_t v_isSharedCheck_4325_; 
v_a_4311_ = lean_ctor_get(v___x_4310_, 0);
v_isSharedCheck_4325_ = !lean_is_exclusive(v___x_4310_);
if (v_isSharedCheck_4325_ == 0)
{
v___x_4313_ = v___x_4310_;
v_isShared_4314_ = v_isSharedCheck_4325_;
goto v_resetjp_4312_;
}
else
{
lean_inc(v_a_4311_);
lean_dec(v___x_4310_);
v___x_4313_ = lean_box(0);
v_isShared_4314_ = v_isSharedCheck_4325_;
goto v_resetjp_4312_;
}
v_resetjp_4312_:
{
if (lean_obj_tag(v_a_4311_) == 1)
{
lean_object* v_val_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; uint8_t v___x_4319_; lean_object* v___x_4320_; 
lean_del_object(v___x_4313_);
v_val_4315_ = lean_ctor_get(v_a_4311_, 0);
lean_inc(v_val_4315_);
lean_dec_ref_known(v_a_4311_, 1);
v___x_4316_ = lean_unsigned_to_nat(2u);
v___x_4317_ = l_Lean_Syntax_getArg(v_stx_4304_, v___x_4316_);
v___x_4318_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkRegisterBuiltinOption___closed__0));
v___x_4319_ = lean_unbox(v_val_4315_);
lean_dec(v_val_4315_);
v___x_4320_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_lintDocStatusNamed(v___x_4319_, v___x_4317_, v___x_4318_, v_a_4305_, v_a_4306_);
return v___x_4320_;
}
else
{
lean_object* v___x_4321_; lean_object* v___x_4323_; 
lean_dec(v_a_4311_);
v___x_4321_ = lean_box(0);
if (v_isShared_4314_ == 0)
{
lean_ctor_set(v___x_4313_, 0, v___x_4321_);
v___x_4323_ = v___x_4313_;
goto v_reusejp_4322_;
}
else
{
lean_object* v_reuseFailAlloc_4324_; 
v_reuseFailAlloc_4324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4324_, 0, v___x_4321_);
v___x_4323_ = v_reuseFailAlloc_4324_;
goto v_reusejp_4322_;
}
v_reusejp_4322_:
{
return v___x_4323_;
}
}
}
}
else
{
lean_object* v_a_4326_; lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4333_; 
v_a_4326_ = lean_ctor_get(v___x_4310_, 0);
v_isSharedCheck_4333_ = !lean_is_exclusive(v___x_4310_);
if (v_isSharedCheck_4333_ == 0)
{
v___x_4328_ = v___x_4310_;
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
else
{
lean_inc(v_a_4326_);
lean_dec(v___x_4310_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v___x_4331_; 
if (v_isShared_4329_ == 0)
{
v___x_4331_ = v___x_4328_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v_a_4326_);
v___x_4331_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
return v___x_4331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterOption___boxed(lean_object* v_stx_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_, lean_object* v_a_4337_){
_start:
{
lean_object* v_res_4338_; 
v_res_4338_ = l_Lean_Linter_MissingDocs_checkRegisterOption(v_stx_4334_, v_a_4335_, v_a_4336_);
lean_dec(v_a_4336_);
lean_dec_ref(v_a_4335_);
lean_dec(v_stx_4334_);
return v_res_4338_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__2(void){
_start:
{
lean_object* v___x_4344_; lean_object* v___x_4345_; 
v___x_4344_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkRegisterOption___boxed), 4, 0);
v___x_4345_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4345_, 0, v___x_4344_);
return v___x_4345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1(){
_start:
{
lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; 
v___x_4347_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__1));
v___x_4348_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__2, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__2_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___closed__2);
v___x_4349_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4347_, v___x_4348_);
return v___x_4349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1___boxed(lean_object* v_a_4350_){
_start:
{
lean_object* v_res_4351_; 
v_res_4351_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterOption___regBuiltin_Lean_Linter_MissingDocs_checkRegisterOption__1();
return v_res_4351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterSimpAttr(lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_){
_start:
{
lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; 
v___x_4357_ = ((lean_object*)(l_Lean_Linter_MissingDocs_checkRegisterSimpAttr___closed__0));
v___x_4358_ = lean_unsigned_to_nat(2u);
v___x_4359_ = l_Lean_Linter_MissingDocs_mkSimpleHandler(v___x_4357_, v___x_4358_, v_a_4353_, v_a_4354_, v_a_4355_);
return v___x_4359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_checkRegisterSimpAttr___boxed(lean_object* v_a_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_){
_start:
{
lean_object* v_res_4364_; 
v_res_4364_ = l_Lean_Linter_MissingDocs_checkRegisterSimpAttr(v_a_4360_, v_a_4361_, v_a_4362_);
lean_dec(v_a_4362_);
lean_dec_ref(v_a_4361_);
lean_dec(v_a_4360_);
return v_res_4364_;
}
}
static lean_object* _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__2(void){
_start:
{
lean_object* v___x_4371_; lean_object* v___x_4372_; 
v___x_4371_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_checkRegisterSimpAttr___boxed), 4, 0);
v___x_4372_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_SimpleHandler_toHandler___boxed), 6, 1);
lean_closure_set(v___x_4372_, 0, v___x_4371_);
return v___x_4372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1(){
_start:
{
lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; 
v___x_4374_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__1));
v___x_4375_ = lean_obj_once(&l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__2, &l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__2_once, _init_l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___closed__2);
v___x_4376_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_4374_, v___x_4375_);
return v___x_4376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1___boxed(lean_object* v_a_4377_){
_start:
{
lean_object* v_res_4378_; 
v_res_4378_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_checkRegisterSimpAttr___regBuiltin_Lean_Linter_MissingDocs_checkRegisterSimpAttr__1();
return v_res_4378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2___redArg(lean_object* v_t_4379_, lean_object* v___y_4380_){
_start:
{
lean_object* v___x_4382_; lean_object* v_infoState_4383_; uint8_t v_enabled_4384_; 
v___x_4382_ = lean_st_ref_get(v___y_4380_);
v_infoState_4383_ = lean_ctor_get(v___x_4382_, 8);
lean_inc_ref(v_infoState_4383_);
lean_dec(v___x_4382_);
v_enabled_4384_ = lean_ctor_get_uint8(v_infoState_4383_, sizeof(void*)*3);
lean_dec_ref(v_infoState_4383_);
if (v_enabled_4384_ == 0)
{
lean_object* v___x_4385_; lean_object* v___x_4386_; 
lean_dec_ref(v_t_4379_);
v___x_4385_ = lean_box(0);
v___x_4386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4386_, 0, v___x_4385_);
return v___x_4386_;
}
else
{
lean_object* v___x_4387_; lean_object* v_infoState_4388_; lean_object* v_env_4389_; lean_object* v_messages_4390_; lean_object* v_scopes_4391_; lean_object* v_usedQuotCtxts_4392_; lean_object* v_nextMacroScope_4393_; lean_object* v_maxRecDepth_4394_; lean_object* v_ngen_4395_; lean_object* v_auxDeclNGen_4396_; lean_object* v_traceState_4397_; lean_object* v_snapshotTasks_4398_; lean_object* v_prevLinterStates_4399_; lean_object* v_codeQualityEntryTasks_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4422_; 
v___x_4387_ = lean_st_ref_take(v___y_4380_);
v_infoState_4388_ = lean_ctor_get(v___x_4387_, 8);
v_env_4389_ = lean_ctor_get(v___x_4387_, 0);
v_messages_4390_ = lean_ctor_get(v___x_4387_, 1);
v_scopes_4391_ = lean_ctor_get(v___x_4387_, 2);
v_usedQuotCtxts_4392_ = lean_ctor_get(v___x_4387_, 3);
v_nextMacroScope_4393_ = lean_ctor_get(v___x_4387_, 4);
v_maxRecDepth_4394_ = lean_ctor_get(v___x_4387_, 5);
v_ngen_4395_ = lean_ctor_get(v___x_4387_, 6);
v_auxDeclNGen_4396_ = lean_ctor_get(v___x_4387_, 7);
v_traceState_4397_ = lean_ctor_get(v___x_4387_, 9);
v_snapshotTasks_4398_ = lean_ctor_get(v___x_4387_, 10);
v_prevLinterStates_4399_ = lean_ctor_get(v___x_4387_, 11);
v_codeQualityEntryTasks_4400_ = lean_ctor_get(v___x_4387_, 12);
v_isSharedCheck_4422_ = !lean_is_exclusive(v___x_4387_);
if (v_isSharedCheck_4422_ == 0)
{
v___x_4402_ = v___x_4387_;
v_isShared_4403_ = v_isSharedCheck_4422_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_codeQualityEntryTasks_4400_);
lean_inc(v_prevLinterStates_4399_);
lean_inc(v_snapshotTasks_4398_);
lean_inc(v_traceState_4397_);
lean_inc(v_infoState_4388_);
lean_inc(v_auxDeclNGen_4396_);
lean_inc(v_ngen_4395_);
lean_inc(v_maxRecDepth_4394_);
lean_inc(v_nextMacroScope_4393_);
lean_inc(v_usedQuotCtxts_4392_);
lean_inc(v_scopes_4391_);
lean_inc(v_messages_4390_);
lean_inc(v_env_4389_);
lean_dec(v___x_4387_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4422_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
uint8_t v_enabled_4404_; lean_object* v_assignment_4405_; lean_object* v_lazyAssignment_4406_; lean_object* v_trees_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4421_; 
v_enabled_4404_ = lean_ctor_get_uint8(v_infoState_4388_, sizeof(void*)*3);
v_assignment_4405_ = lean_ctor_get(v_infoState_4388_, 0);
v_lazyAssignment_4406_ = lean_ctor_get(v_infoState_4388_, 1);
v_trees_4407_ = lean_ctor_get(v_infoState_4388_, 2);
v_isSharedCheck_4421_ = !lean_is_exclusive(v_infoState_4388_);
if (v_isSharedCheck_4421_ == 0)
{
v___x_4409_ = v_infoState_4388_;
v_isShared_4410_ = v_isSharedCheck_4421_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_trees_4407_);
lean_inc(v_lazyAssignment_4406_);
lean_inc(v_assignment_4405_);
lean_dec(v_infoState_4388_);
v___x_4409_ = lean_box(0);
v_isShared_4410_ = v_isSharedCheck_4421_;
goto v_resetjp_4408_;
}
v_resetjp_4408_:
{
lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4414_; 
v___x_4411_ = lean_box(0);
v___x_4412_ = l_Lean_PersistentArray_push___redArg(v_trees_4407_, v_t_4379_);
if (v_isShared_4410_ == 0)
{
lean_ctor_set(v___x_4409_, 2, v___x_4412_);
v___x_4414_ = v___x_4409_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v_assignment_4405_);
lean_ctor_set(v_reuseFailAlloc_4420_, 1, v_lazyAssignment_4406_);
lean_ctor_set(v_reuseFailAlloc_4420_, 2, v___x_4412_);
lean_ctor_set_uint8(v_reuseFailAlloc_4420_, sizeof(void*)*3, v_enabled_4404_);
v___x_4414_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
lean_object* v___x_4416_; 
if (v_isShared_4403_ == 0)
{
lean_ctor_set(v___x_4402_, 8, v___x_4414_);
v___x_4416_ = v___x_4402_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_env_4389_);
lean_ctor_set(v_reuseFailAlloc_4419_, 1, v_messages_4390_);
lean_ctor_set(v_reuseFailAlloc_4419_, 2, v_scopes_4391_);
lean_ctor_set(v_reuseFailAlloc_4419_, 3, v_usedQuotCtxts_4392_);
lean_ctor_set(v_reuseFailAlloc_4419_, 4, v_nextMacroScope_4393_);
lean_ctor_set(v_reuseFailAlloc_4419_, 5, v_maxRecDepth_4394_);
lean_ctor_set(v_reuseFailAlloc_4419_, 6, v_ngen_4395_);
lean_ctor_set(v_reuseFailAlloc_4419_, 7, v_auxDeclNGen_4396_);
lean_ctor_set(v_reuseFailAlloc_4419_, 8, v___x_4414_);
lean_ctor_set(v_reuseFailAlloc_4419_, 9, v_traceState_4397_);
lean_ctor_set(v_reuseFailAlloc_4419_, 10, v_snapshotTasks_4398_);
lean_ctor_set(v_reuseFailAlloc_4419_, 11, v_prevLinterStates_4399_);
lean_ctor_set(v_reuseFailAlloc_4419_, 12, v_codeQualityEntryTasks_4400_);
v___x_4416_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
lean_object* v___x_4417_; lean_object* v___x_4418_; 
v___x_4417_ = lean_st_ref_put(v___y_4380_, v___x_4416_);
v___x_4418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4418_, 0, v___x_4411_);
return v___x_4418_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_t_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_){
_start:
{
lean_object* v_res_4426_; 
v_res_4426_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2___redArg(v_t_4423_, v___y_4424_);
lean_dec(v___y_4424_);
return v_res_4426_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; 
v___x_4427_ = lean_unsigned_to_nat(32u);
v___x_4428_ = lean_mk_empty_array_with_capacity(v___x_4427_);
v___x_4429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4429_, 0, v___x_4428_);
return v___x_4429_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__1(void){
_start:
{
size_t v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; 
v___x_4430_ = ((size_t)5ULL);
v___x_4431_ = lean_unsigned_to_nat(0u);
v___x_4432_ = lean_unsigned_to_nat(32u);
v___x_4433_ = lean_mk_empty_array_with_capacity(v___x_4432_);
v___x_4434_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__0);
v___x_4435_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4435_, 0, v___x_4434_);
lean_ctor_set(v___x_4435_, 1, v___x_4433_);
lean_ctor_set(v___x_4435_, 2, v___x_4431_);
lean_ctor_set(v___x_4435_, 3, v___x_4431_);
lean_ctor_set_usize(v___x_4435_, 4, v___x_4430_);
return v___x_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1(lean_object* v_t_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_){
_start:
{
lean_object* v___x_4440_; lean_object* v_infoState_4441_; uint8_t v_enabled_4442_; 
v___x_4440_ = lean_st_ref_get(v___y_4438_);
v_infoState_4441_ = lean_ctor_get(v___x_4440_, 8);
lean_inc_ref(v_infoState_4441_);
lean_dec(v___x_4440_);
v_enabled_4442_ = lean_ctor_get_uint8(v_infoState_4441_, sizeof(void*)*3);
lean_dec_ref(v_infoState_4441_);
if (v_enabled_4442_ == 0)
{
lean_object* v___x_4443_; lean_object* v___x_4444_; 
lean_dec_ref(v_t_4436_);
v___x_4443_ = lean_box(0);
v___x_4444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4444_, 0, v___x_4443_);
return v___x_4444_;
}
else
{
lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; 
v___x_4445_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___closed__1);
v___x_4446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4446_, 0, v_t_4436_);
lean_ctor_set(v___x_4446_, 1, v___x_4445_);
v___x_4447_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2___redArg(v___x_4446_, v___y_4438_);
return v___x_4447_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1___boxed(lean_object* v_t_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_){
_start:
{
lean_object* v_res_4452_; 
v_res_4452_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1(v_t_4448_, v___y_4449_, v___y_4450_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
return v_res_4452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__0(lean_object* v_info_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_){
_start:
{
lean_object* v___x_4457_; lean_object* v___x_4458_; 
v___x_4457_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_4457_, 0, v_info_4453_);
v___x_4458_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1(v___x_4457_, v___y_4454_, v___y_4455_);
return v___x_4458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__0___boxed(lean_object* v_info_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_){
_start:
{
lean_object* v_res_4463_; 
v_res_4463_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__0(v_info_4459_, v___y_4460_, v___y_4461_);
lean_dec(v___y_4461_);
lean_dec_ref(v___y_4460_);
return v_res_4463_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4465_; lean_object* v___x_4466_; 
v___x_4465_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__0));
v___x_4466_ = l_Lean_stringToMessageData(v___x_4465_);
return v___x_4466_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4468_; lean_object* v___x_4469_; 
v___x_4468_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__2));
v___x_4469_ = l_Lean_stringToMessageData(v___x_4468_);
return v___x_4469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg(lean_object* v_optionName_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_){
_start:
{
lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; 
v___x_4474_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__1, &l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__1_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__1);
v___x_4475_ = l_Lean_MessageData_ofName(v_optionName_4470_);
v___x_4476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4476_, 0, v___x_4474_);
lean_ctor_set(v___x_4476_, 1, v___x_4475_);
v___x_4477_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__3, &l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__3_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___closed__3);
v___x_4478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4478_, 0, v___x_4476_);
lean_ctor_set(v___x_4478_, 1, v___x_4477_);
v___x_4479_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg(v___x_4478_, v___y_4471_, v___y_4472_);
return v___x_4479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg___boxed(lean_object* v_optionName_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_){
_start:
{
lean_object* v_res_4484_; 
v_res_4484_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg(v_optionName_4480_, v___y_4481_, v___y_4482_);
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
return v_res_4484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__6(lean_object* v_o_4485_, lean_object* v_k_4486_, lean_object* v_v_4487_){
_start:
{
lean_object* v_map_4488_; uint8_t v_hasTrace_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4502_; 
v_map_4488_ = lean_ctor_get(v_o_4485_, 0);
v_hasTrace_4489_ = lean_ctor_get_uint8(v_o_4485_, sizeof(void*)*1);
v_isSharedCheck_4502_ = !lean_is_exclusive(v_o_4485_);
if (v_isSharedCheck_4502_ == 0)
{
v___x_4491_ = v_o_4485_;
v_isShared_4492_ = v_isSharedCheck_4502_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_map_4488_);
lean_dec(v_o_4485_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4502_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
lean_object* v___x_4493_; 
lean_inc(v_k_4486_);
v___x_4493_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4486_, v_v_4487_, v_map_4488_);
if (v_hasTrace_4489_ == 0)
{
lean_object* v___x_4494_; uint8_t v___x_4495_; lean_object* v___x_4497_; 
v___x_4494_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__3_spec__5___closed__9));
v___x_4495_ = l_Lean_Name_isPrefixOf(v___x_4494_, v_k_4486_);
lean_dec(v_k_4486_);
if (v_isShared_4492_ == 0)
{
lean_ctor_set(v___x_4491_, 0, v___x_4493_);
v___x_4497_ = v___x_4491_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v___x_4493_);
v___x_4497_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
lean_ctor_set_uint8(v___x_4497_, sizeof(void*)*1, v___x_4495_);
return v___x_4497_;
}
}
else
{
lean_object* v___x_4500_; 
lean_dec(v_k_4486_);
if (v_isShared_4492_ == 0)
{
lean_ctor_set(v___x_4491_, 0, v___x_4493_);
v___x_4500_ = v___x_4491_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v___x_4493_);
lean_ctor_set_uint8(v_reuseFailAlloc_4501_, sizeof(void*)*1, v_hasTrace_4489_);
v___x_4500_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
return v___x_4500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8_spec__10(lean_object* v_msg_4503_){
_start:
{
lean_object* v___x_4504_; lean_object* v___x_4505_; 
v___x_4504_ = l_Lean_instInhabitedExpr;
v___x_4505_ = lean_panic_fn_borrowed(v___x_4504_, v_msg_4503_);
return v___x_4505_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__1(void){
_start:
{
lean_object* v___x_4507_; lean_object* v___x_4508_; 
v___x_4507_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__0));
v___x_4508_ = l_Lean_stringToMessageData(v___x_4507_);
return v___x_4508_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__3(void){
_start:
{
lean_object* v___x_4510_; lean_object* v___x_4511_; 
v___x_4510_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__2));
v___x_4511_ = l_Lean_stringToMessageData(v___x_4510_);
return v___x_4511_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__5(void){
_start:
{
lean_object* v___x_4513_; lean_object* v___x_4514_; 
v___x_4513_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__4));
v___x_4514_ = l_Lean_stringToMessageData(v___x_4513_);
return v___x_4514_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__7(void){
_start:
{
lean_object* v___x_4516_; lean_object* v___x_4517_; 
v___x_4516_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__6));
v___x_4517_ = l_Lean_stringToMessageData(v___x_4516_);
return v___x_4517_;
}
}
static lean_object* _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__16(void){
_start:
{
lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; 
v___x_4529_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__15));
v___x_4530_ = lean_unsigned_to_nat(14u);
v___x_4531_ = lean_unsigned_to_nat(22u);
v___x_4532_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__14));
v___x_4533_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__13));
v___x_4534_ = l_mkPanicMessageWithDecl(v___x_4533_, v___x_4532_, v___x_4531_, v___x_4530_, v___x_4529_);
return v___x_4534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8(lean_object* v_optionName_4535_, lean_object* v_found_4536_, lean_object* v_defVal_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_){
_start:
{
lean_object* v___x_4541_; 
v___x_4541_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_defVal_4537_);
if (lean_obj_tag(v___x_4541_) == 1)
{
lean_object* v_val_4542_; lean_object* v___y_4544_; lean_object* v___y_4545_; lean_object* v___y_4546_; lean_object* v___y_4565_; lean_object* v___x_4613_; 
v_val_4542_ = lean_ctor_get(v___x_4541_, 0);
lean_inc(v_val_4542_);
lean_dec_ref_known(v___x_4541_, 1);
v___x_4613_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_found_4536_);
if (lean_obj_tag(v___x_4613_) == 0)
{
lean_object* v___x_4614_; lean_object* v___x_4615_; 
v___x_4614_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__16, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__16_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__16);
v___x_4615_ = l_panic___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8_spec__10(v___x_4614_);
v___y_4565_ = v___x_4615_;
goto v___jp_4564_;
}
else
{
lean_object* v_val_4616_; 
v_val_4616_ = lean_ctor_get(v___x_4613_, 0);
lean_inc(v_val_4616_);
lean_dec_ref_known(v___x_4613_, 1);
v___y_4565_ = v_val_4616_;
goto v___jp_4564_;
}
v___jp_4543_:
{
lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; 
v___x_4547_ = l_Lean_MessageData_ofFormat(v___y_4546_);
v___x_4548_ = l_Lean_indentD(v___x_4547_);
lean_inc_ref(v___y_4545_);
v___x_4549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4549_, 0, v___y_4545_);
lean_ctor_set(v___x_4549_, 1, v___x_4548_);
v___x_4550_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__1, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__1_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__1);
v___x_4551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4551_, 0, v___x_4549_);
lean_ctor_set(v___x_4551_, 1, v___x_4550_);
v___x_4552_ = l_Lean_MessageData_ofExpr(v___y_4544_);
v___x_4553_ = l_Lean_indentD(v___x_4552_);
v___x_4554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4554_, 0, v___x_4551_);
lean_ctor_set(v___x_4554_, 1, v___x_4553_);
v___x_4555_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__3, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__3_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__3);
v___x_4556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4556_, 0, v___x_4554_);
lean_ctor_set(v___x_4556_, 1, v___x_4555_);
v___x_4557_ = l_Lean_MessageData_ofName(v_optionName_4535_);
v___x_4558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4558_, 0, v___x_4556_);
lean_ctor_set(v___x_4558_, 1, v___x_4557_);
v___x_4559_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__5, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__5_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__5);
v___x_4560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4560_, 0, v___x_4558_);
lean_ctor_set(v___x_4560_, 1, v___x_4559_);
v___x_4561_ = l_Lean_indentExpr(v_val_4542_);
v___x_4562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4562_, 0, v___x_4560_);
lean_ctor_set(v___x_4562_, 1, v___x_4561_);
v___x_4563_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg(v___x_4562_, v___y_4538_, v___y_4539_);
return v___x_4563_;
}
v___jp_4564_:
{
lean_object* v___x_4566_; 
v___x_4566_ = lean_obj_once(&l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__7, &l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__7_once, _init_l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__7);
switch(lean_obj_tag(v_found_4536_))
{
case 0:
{
lean_object* v_v_4567_; lean_object* v___x_4569_; uint8_t v_isShared_4570_; uint8_t v_isSharedCheck_4575_; 
v_v_4567_ = lean_ctor_get(v_found_4536_, 0);
v_isSharedCheck_4575_ = !lean_is_exclusive(v_found_4536_);
if (v_isSharedCheck_4575_ == 0)
{
v___x_4569_ = v_found_4536_;
v_isShared_4570_ = v_isSharedCheck_4575_;
goto v_resetjp_4568_;
}
else
{
lean_inc(v_v_4567_);
lean_dec(v_found_4536_);
v___x_4569_ = lean_box(0);
v_isShared_4570_ = v_isSharedCheck_4575_;
goto v_resetjp_4568_;
}
v_resetjp_4568_:
{
lean_object* v___x_4571_; lean_object* v___x_4573_; 
v___x_4571_ = l_String_quote(v_v_4567_);
if (v_isShared_4570_ == 0)
{
lean_ctor_set_tag(v___x_4569_, 3);
lean_ctor_set(v___x_4569_, 0, v___x_4571_);
v___x_4573_ = v___x_4569_;
goto v_reusejp_4572_;
}
else
{
lean_object* v_reuseFailAlloc_4574_; 
v_reuseFailAlloc_4574_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4574_, 0, v___x_4571_);
v___x_4573_ = v_reuseFailAlloc_4574_;
goto v_reusejp_4572_;
}
v_reusejp_4572_:
{
v___y_4544_ = v___y_4565_;
v___y_4545_ = v___x_4566_;
v___y_4546_ = v___x_4573_;
goto v___jp_4543_;
}
}
}
case 1:
{
uint8_t v_v_4576_; 
v_v_4576_ = lean_ctor_get_uint8(v_found_4536_, 0);
lean_dec_ref_known(v_found_4536_, 0);
if (v_v_4576_ == 0)
{
lean_object* v___x_4577_; 
v___x_4577_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__9));
v___y_4544_ = v___y_4565_;
v___y_4545_ = v___x_4566_;
v___y_4546_ = v___x_4577_;
goto v___jp_4543_;
}
else
{
lean_object* v___x_4578_; 
v___x_4578_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__11));
v___y_4544_ = v___y_4565_;
v___y_4545_ = v___x_4566_;
v___y_4546_ = v___x_4578_;
goto v___jp_4543_;
}
}
case 2:
{
lean_object* v_v_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4590_; 
v_v_4579_ = lean_ctor_get(v_found_4536_, 0);
v_isSharedCheck_4590_ = !lean_is_exclusive(v_found_4536_);
if (v_isSharedCheck_4590_ == 0)
{
v___x_4581_ = v_found_4536_;
v_isShared_4582_ = v_isSharedCheck_4590_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_v_4579_);
lean_dec(v_found_4536_);
v___x_4581_ = lean_box(0);
v_isShared_4582_ = v_isSharedCheck_4590_;
goto v_resetjp_4580_;
}
v_resetjp_4580_:
{
lean_object* v___x_4583_; uint8_t v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4587_; 
v___x_4583_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__12));
v___x_4584_ = 1;
v___x_4585_ = l_Lean_Name_toString(v_v_4579_, v___x_4584_);
if (v_isShared_4582_ == 0)
{
lean_ctor_set_tag(v___x_4581_, 3);
lean_ctor_set(v___x_4581_, 0, v___x_4585_);
v___x_4587_ = v___x_4581_;
goto v_reusejp_4586_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v___x_4585_);
v___x_4587_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4586_;
}
v_reusejp_4586_:
{
lean_object* v___x_4588_; 
v___x_4588_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_4588_, 0, v___x_4583_);
lean_ctor_set(v___x_4588_, 1, v___x_4587_);
v___y_4544_ = v___y_4565_;
v___y_4545_ = v___x_4566_;
v___y_4546_ = v___x_4588_;
goto v___jp_4543_;
}
}
}
case 3:
{
lean_object* v_v_4591_; lean_object* v___x_4593_; uint8_t v_isShared_4594_; uint8_t v_isSharedCheck_4599_; 
v_v_4591_ = lean_ctor_get(v_found_4536_, 0);
v_isSharedCheck_4599_ = !lean_is_exclusive(v_found_4536_);
if (v_isSharedCheck_4599_ == 0)
{
v___x_4593_ = v_found_4536_;
v_isShared_4594_ = v_isSharedCheck_4599_;
goto v_resetjp_4592_;
}
else
{
lean_inc(v_v_4591_);
lean_dec(v_found_4536_);
v___x_4593_ = lean_box(0);
v_isShared_4594_ = v_isSharedCheck_4599_;
goto v_resetjp_4592_;
}
v_resetjp_4592_:
{
lean_object* v___x_4595_; lean_object* v___x_4597_; 
v___x_4595_ = l_Nat_reprFast(v_v_4591_);
if (v_isShared_4594_ == 0)
{
lean_ctor_set(v___x_4593_, 0, v___x_4595_);
v___x_4597_ = v___x_4593_;
goto v_reusejp_4596_;
}
else
{
lean_object* v_reuseFailAlloc_4598_; 
v_reuseFailAlloc_4598_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4598_, 0, v___x_4595_);
v___x_4597_ = v_reuseFailAlloc_4598_;
goto v_reusejp_4596_;
}
v_reusejp_4596_:
{
v___y_4544_ = v___y_4565_;
v___y_4545_ = v___x_4566_;
v___y_4546_ = v___x_4597_;
goto v___jp_4543_;
}
}
}
case 4:
{
lean_object* v_v_4600_; lean_object* v___x_4602_; uint8_t v_isShared_4603_; uint8_t v_isSharedCheck_4608_; 
v_v_4600_ = lean_ctor_get(v_found_4536_, 0);
v_isSharedCheck_4608_ = !lean_is_exclusive(v_found_4536_);
if (v_isSharedCheck_4608_ == 0)
{
v___x_4602_ = v_found_4536_;
v_isShared_4603_ = v_isSharedCheck_4608_;
goto v_resetjp_4601_;
}
else
{
lean_inc(v_v_4600_);
lean_dec(v_found_4536_);
v___x_4602_ = lean_box(0);
v_isShared_4603_ = v_isSharedCheck_4608_;
goto v_resetjp_4601_;
}
v_resetjp_4601_:
{
lean_object* v___x_4604_; lean_object* v___x_4606_; 
v___x_4604_ = l_Int_repr(v_v_4600_);
lean_dec(v_v_4600_);
if (v_isShared_4603_ == 0)
{
lean_ctor_set_tag(v___x_4602_, 3);
lean_ctor_set(v___x_4602_, 0, v___x_4604_);
v___x_4606_ = v___x_4602_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v___x_4604_);
v___x_4606_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
v___y_4544_ = v___y_4565_;
v___y_4545_ = v___x_4566_;
v___y_4546_ = v___x_4606_;
goto v___jp_4543_;
}
}
}
default: 
{
lean_object* v_v_4609_; lean_object* v___x_4610_; uint8_t v___x_4611_; lean_object* v___x_4612_; 
v_v_4609_ = lean_ctor_get(v_found_4536_, 0);
lean_inc(v_v_4609_);
lean_dec_ref_known(v_found_4536_, 1);
v___x_4610_ = lean_box(0);
v___x_4611_ = 0;
v___x_4612_ = l_Lean_Syntax_formatStx(v_v_4609_, v___x_4610_, v___x_4611_);
v___y_4544_ = v___y_4565_;
v___y_4545_ = v___x_4566_;
v___y_4546_ = v___x_4612_;
goto v___jp_4543_;
}
}
}
}
else
{
lean_object* v___x_4617_; 
lean_dec(v___x_4541_);
lean_dec_ref(v_found_4536_);
v___x_4617_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg(v_optionName_4535_, v___y_4538_, v___y_4539_);
return v___x_4617_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___boxed(lean_object* v_optionName_4618_, lean_object* v_found_4619_, lean_object* v_defVal_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_){
_start:
{
lean_object* v_res_4624_; 
v_res_4624_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8(v_optionName_4618_, v_found_4619_, v_defVal_4620_, v___y_4621_, v___y_4622_);
lean_dec(v___y_4622_);
lean_dec_ref(v___y_4621_);
lean_dec_ref(v_defVal_4620_);
return v_res_4624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5(lean_object* v_optionName_4625_, lean_object* v_decl_4626_, lean_object* v_val_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_){
_start:
{
lean_object* v_defValue_4631_; uint8_t v___x_4632_; 
v_defValue_4631_ = lean_ctor_get(v_decl_4626_, 2);
v___x_4632_ = l_Lean_DataValue_sameCtor(v_defValue_4631_, v_val_4627_);
if (v___x_4632_ == 0)
{
lean_object* v___x_4633_; 
v___x_4633_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8(v_optionName_4625_, v_val_4627_, v_defValue_4631_, v___y_4628_, v___y_4629_);
return v___x_4633_;
}
else
{
lean_object* v___x_4634_; lean_object* v___x_4635_; 
lean_dec_ref(v_val_4627_);
lean_dec(v_optionName_4625_);
v___x_4634_ = lean_box(0);
v___x_4635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4635_, 0, v___x_4634_);
return v___x_4635_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5___boxed(lean_object* v_optionName_4636_, lean_object* v_decl_4637_, lean_object* v_val_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_){
_start:
{
lean_object* v_res_4642_; 
v_res_4642_ = l_Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5(v_optionName_4636_, v_decl_4637_, v_val_4638_, v___y_4639_, v___y_4640_);
lean_dec(v___y_4640_);
lean_dec_ref(v___y_4639_);
lean_dec_ref(v_decl_4637_);
return v_res_4642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3(lean_object* v_optionName_4643_, lean_object* v_decl_4644_, lean_object* v_val_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_){
_start:
{
lean_object* v___x_4649_; 
lean_inc_ref(v_val_4645_);
lean_inc(v_optionName_4643_);
v___x_4649_ = l_Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5(v_optionName_4643_, v_decl_4644_, v_val_4645_, v___y_4646_, v___y_4647_);
if (lean_obj_tag(v___x_4649_) == 0)
{
lean_object* v___x_4651_; uint8_t v_isShared_4652_; uint8_t v_isSharedCheck_4663_; 
v_isSharedCheck_4663_ = !lean_is_exclusive(v___x_4649_);
if (v_isSharedCheck_4663_ == 0)
{
lean_object* v_unused_4664_; 
v_unused_4664_ = lean_ctor_get(v___x_4649_, 0);
lean_dec(v_unused_4664_);
v___x_4651_ = v___x_4649_;
v_isShared_4652_ = v_isSharedCheck_4663_;
goto v_resetjp_4650_;
}
else
{
lean_dec(v___x_4649_);
v___x_4651_ = lean_box(0);
v_isShared_4652_ = v_isSharedCheck_4663_;
goto v_resetjp_4650_;
}
v_resetjp_4650_:
{
lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v_scopes_4655_; lean_object* v___x_4656_; lean_object* v_opts_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4661_; 
v___x_4653_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4654_ = lean_st_ref_get(v___y_4647_);
v_scopes_4655_ = lean_ctor_get(v___x_4654_, 2);
lean_inc(v_scopes_4655_);
lean_dec(v___x_4654_);
v___x_4656_ = l_List_head_x21___redArg(v___x_4653_, v_scopes_4655_);
lean_dec(v_scopes_4655_);
v_opts_4657_ = lean_ctor_get(v___x_4656_, 1);
lean_inc_ref(v_opts_4657_);
lean_dec(v___x_4656_);
v___x_4658_ = l_Lean_Options_set___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__6(v_opts_4657_, v_optionName_4643_, v_val_4645_);
v___x_4659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4659_, 0, v___x_4658_);
lean_ctor_set(v___x_4659_, 1, v_decl_4644_);
if (v_isShared_4652_ == 0)
{
lean_ctor_set(v___x_4651_, 0, v___x_4659_);
v___x_4661_ = v___x_4651_;
goto v_reusejp_4660_;
}
else
{
lean_object* v_reuseFailAlloc_4662_; 
v_reuseFailAlloc_4662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4662_, 0, v___x_4659_);
v___x_4661_ = v_reuseFailAlloc_4662_;
goto v_reusejp_4660_;
}
v_reusejp_4660_:
{
return v___x_4661_;
}
}
}
else
{
lean_object* v_a_4665_; lean_object* v___x_4667_; uint8_t v_isShared_4668_; uint8_t v_isSharedCheck_4672_; 
lean_dec_ref(v_val_4645_);
lean_dec_ref(v_decl_4644_);
lean_dec(v_optionName_4643_);
v_a_4665_ = lean_ctor_get(v___x_4649_, 0);
v_isSharedCheck_4672_ = !lean_is_exclusive(v___x_4649_);
if (v_isSharedCheck_4672_ == 0)
{
v___x_4667_ = v___x_4649_;
v_isShared_4668_ = v_isSharedCheck_4672_;
goto v_resetjp_4666_;
}
else
{
lean_inc(v_a_4665_);
lean_dec(v___x_4649_);
v___x_4667_ = lean_box(0);
v_isShared_4668_ = v_isSharedCheck_4672_;
goto v_resetjp_4666_;
}
v_resetjp_4666_:
{
lean_object* v___x_4670_; 
if (v_isShared_4668_ == 0)
{
v___x_4670_ = v___x_4667_;
goto v_reusejp_4669_;
}
else
{
lean_object* v_reuseFailAlloc_4671_; 
v_reuseFailAlloc_4671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4671_, 0, v_a_4665_);
v___x_4670_ = v_reuseFailAlloc_4671_;
goto v_reusejp_4669_;
}
v_reusejp_4669_:
{
return v___x_4670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3___boxed(lean_object* v_optionName_4673_, lean_object* v_decl_4674_, lean_object* v_val_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_){
_start:
{
lean_object* v_res_4679_; 
v_res_4679_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3(v_optionName_4673_, v_decl_4674_, v_val_4675_, v___y_4676_, v___y_4677_);
lean_dec(v___y_4677_);
lean_dec_ref(v___y_4676_);
return v_res_4679_;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4681_; lean_object* v___x_4682_; 
v___x_4681_ = ((lean_object*)(l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__0));
v___x_4682_ = l_Lean_stringToMessageData(v___x_4681_);
return v___x_4682_;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__3(void){
_start:
{
lean_object* v___x_4684_; lean_object* v___x_4685_; 
v___x_4684_ = ((lean_object*)(l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__2));
v___x_4685_ = l_Lean_stringToMessageData(v___x_4684_);
return v___x_4685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0(lean_object* v_id_4686_, lean_object* v_val_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_){
_start:
{
lean_object* v___x_4691_; 
v___x_4691_ = l_Lean_Elab_Command_getRef___redArg(v___y_4688_);
if (lean_obj_tag(v___x_4691_) == 0)
{
lean_object* v_a_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4702_; uint8_t v_isShared_4703_; uint8_t v_isSharedCheck_4772_; 
v_a_4692_ = lean_ctor_get(v___x_4691_, 0);
lean_inc_n(v_a_4692_, 2);
lean_dec_ref_known(v___x_4691_, 1);
v___x_4693_ = l_Lean_Syntax_getArgs(v_a_4692_);
v___x_4694_ = lean_unsigned_to_nat(3u);
v___x_4695_ = lean_unsigned_to_nat(0u);
v___x_4696_ = l_Array_toSubarray___redArg(v___x_4693_, v___x_4695_, v___x_4694_);
v___x_4697_ = l_Subarray_copy___redArg(v___x_4696_);
v___x_4698_ = l_Lean_Syntax_setArgs(v_a_4692_, v___x_4697_);
v___x_4699_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_4699_, 0, v___x_4698_);
v___x_4700_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__0(v___x_4699_, v___y_4688_, v___y_4689_);
v_isSharedCheck_4772_ = !lean_is_exclusive(v___x_4700_);
if (v_isSharedCheck_4772_ == 0)
{
lean_object* v_unused_4773_; 
v_unused_4773_ = lean_ctor_get(v___x_4700_, 0);
lean_dec(v_unused_4773_);
v___x_4702_ = v___x_4700_;
v_isShared_4703_ = v_isSharedCheck_4772_;
goto v_resetjp_4701_;
}
else
{
lean_dec(v___x_4700_);
v___x_4702_ = lean_box(0);
v_isShared_4703_ = v_isSharedCheck_4772_;
goto v_resetjp_4701_;
}
v_resetjp_4701_:
{
lean_object* v___x_4704_; lean_object* v_optionName_4705_; lean_object* v___x_4706_; 
v___x_4704_ = l_Lean_Syntax_getId(v_id_4686_);
v_optionName_4705_ = l_Lean_Name_eraseMacroScopes(v___x_4704_);
lean_dec(v___x_4704_);
lean_inc(v_optionName_4705_);
v___x_4706_ = l_Lean_getOptionDecl(v_optionName_4705_);
if (lean_obj_tag(v___x_4706_) == 0)
{
lean_object* v_a_4707_; lean_object* v_declName_4708_; lean_object* v_defValue_4709_; lean_object* v___x_4710_; lean_object* v___x_4712_; 
lean_dec(v_a_4692_);
v_a_4707_ = lean_ctor_get(v___x_4706_, 0);
lean_inc(v_a_4707_);
lean_dec_ref_known(v___x_4706_, 1);
v_declName_4708_ = lean_ctor_get(v_a_4707_, 1);
v_defValue_4709_ = lean_ctor_get(v_a_4707_, 2);
lean_inc(v_declName_4708_);
lean_inc(v_optionName_4705_);
v___x_4710_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4710_, 0, v_id_4686_);
lean_ctor_set(v___x_4710_, 1, v_optionName_4705_);
lean_ctor_set(v___x_4710_, 2, v_declName_4708_);
if (v_isShared_4703_ == 0)
{
lean_ctor_set_tag(v___x_4702_, 5);
lean_ctor_set(v___x_4702_, 0, v___x_4710_);
v___x_4712_ = v___x_4702_;
goto v_reusejp_4711_;
}
else
{
lean_object* v_reuseFailAlloc_4757_; 
v_reuseFailAlloc_4757_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4757_, 0, v___x_4710_);
v___x_4712_ = v_reuseFailAlloc_4757_;
goto v_reusejp_4711_;
}
v_reusejp_4711_:
{
lean_object* v___x_4713_; lean_object* v___x_4728_; 
v___x_4713_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1(v___x_4712_, v___y_4688_, v___y_4689_);
lean_dec_ref(v___x_4713_);
v___x_4728_ = l_Lean_Syntax_isStrLit_x3f(v_val_4687_);
if (lean_obj_tag(v___x_4728_) == 0)
{
lean_object* v___x_4729_; 
v___x_4729_ = l_Lean_Syntax_isNatLit_x3f(v_val_4687_);
if (lean_obj_tag(v___x_4729_) == 0)
{
if (lean_obj_tag(v_val_4687_) == 2)
{
lean_object* v_val_4730_; lean_object* v___x_4731_; uint8_t v___x_4732_; 
v_val_4730_ = lean_ctor_get(v_val_4687_, 1);
v___x_4731_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__10));
v___x_4732_ = lean_string_dec_eq(v_val_4730_, v___x_4731_);
if (v___x_4732_ == 0)
{
lean_object* v___x_4733_; uint8_t v___x_4734_; 
v___x_4733_ = ((lean_object*)(l___private_Lean_Elab_SetOption_0__Lean_Elab_validateOptionValue_throwMistypedOptionValue___at___00Lean_Elab_validateOptionValue___at___00__private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3_spec__5_spec__8___closed__8));
v___x_4734_ = lean_string_dec_eq(v_val_4730_, v___x_4733_);
if (v___x_4734_ == 0)
{
lean_inc_ref(v_defValue_4709_);
lean_dec(v_a_4707_);
goto v___jp_4714_;
}
else
{
lean_object* v___x_4735_; lean_object* v___x_4736_; 
lean_dec_ref_known(v_val_4687_, 2);
v___x_4735_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4735_, 0, v___x_4732_);
v___x_4736_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3(v_optionName_4705_, v_a_4707_, v___x_4735_, v___y_4688_, v___y_4689_);
return v___x_4736_;
}
}
else
{
lean_object* v___x_4737_; lean_object* v___x_4738_; 
lean_dec_ref_known(v_val_4687_, 2);
v___x_4737_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_4737_, 0, v___x_4732_);
v___x_4738_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3(v_optionName_4705_, v_a_4707_, v___x_4737_, v___y_4688_, v___y_4689_);
return v___x_4738_;
}
}
else
{
lean_inc_ref(v_defValue_4709_);
lean_dec(v_a_4707_);
goto v___jp_4714_;
}
}
else
{
lean_object* v_val_4739_; lean_object* v___x_4741_; uint8_t v_isShared_4742_; uint8_t v_isSharedCheck_4747_; 
lean_dec(v_val_4687_);
v_val_4739_ = lean_ctor_get(v___x_4729_, 0);
v_isSharedCheck_4747_ = !lean_is_exclusive(v___x_4729_);
if (v_isSharedCheck_4747_ == 0)
{
v___x_4741_ = v___x_4729_;
v_isShared_4742_ = v_isSharedCheck_4747_;
goto v_resetjp_4740_;
}
else
{
lean_inc(v_val_4739_);
lean_dec(v___x_4729_);
v___x_4741_ = lean_box(0);
v_isShared_4742_ = v_isSharedCheck_4747_;
goto v_resetjp_4740_;
}
v_resetjp_4740_:
{
lean_object* v___x_4744_; 
if (v_isShared_4742_ == 0)
{
lean_ctor_set_tag(v___x_4741_, 3);
v___x_4744_ = v___x_4741_;
goto v_reusejp_4743_;
}
else
{
lean_object* v_reuseFailAlloc_4746_; 
v_reuseFailAlloc_4746_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4746_, 0, v_val_4739_);
v___x_4744_ = v_reuseFailAlloc_4746_;
goto v_reusejp_4743_;
}
v_reusejp_4743_:
{
lean_object* v___x_4745_; 
v___x_4745_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3(v_optionName_4705_, v_a_4707_, v___x_4744_, v___y_4688_, v___y_4689_);
return v___x_4745_;
}
}
}
}
else
{
lean_object* v_val_4748_; lean_object* v___x_4750_; uint8_t v_isShared_4751_; uint8_t v_isSharedCheck_4756_; 
lean_dec(v_val_4687_);
v_val_4748_ = lean_ctor_get(v___x_4728_, 0);
v_isSharedCheck_4756_ = !lean_is_exclusive(v___x_4728_);
if (v_isSharedCheck_4756_ == 0)
{
v___x_4750_ = v___x_4728_;
v_isShared_4751_ = v_isSharedCheck_4756_;
goto v_resetjp_4749_;
}
else
{
lean_inc(v_val_4748_);
lean_dec(v___x_4728_);
v___x_4750_ = lean_box(0);
v_isShared_4751_ = v_isSharedCheck_4756_;
goto v_resetjp_4749_;
}
v_resetjp_4749_:
{
lean_object* v___x_4753_; 
if (v_isShared_4751_ == 0)
{
lean_ctor_set_tag(v___x_4750_, 0);
v___x_4753_ = v___x_4750_;
goto v_reusejp_4752_;
}
else
{
lean_object* v_reuseFailAlloc_4755_; 
v_reuseFailAlloc_4755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4755_, 0, v_val_4748_);
v___x_4753_ = v_reuseFailAlloc_4755_;
goto v_reusejp_4752_;
}
v_reusejp_4752_:
{
lean_object* v___x_4754_; 
v___x_4754_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_elabSetOption_setOption___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__3(v_optionName_4705_, v_a_4707_, v___x_4753_, v___y_4688_, v___y_4689_);
return v___x_4754_;
}
}
}
v___jp_4714_:
{
lean_object* v___x_4715_; 
v___x_4715_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_ctorType_x3f(v_defValue_4709_);
lean_dec_ref(v_defValue_4709_);
if (lean_obj_tag(v___x_4715_) == 1)
{
lean_object* v_val_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; 
lean_dec(v_optionName_4705_);
v_val_4716_ = lean_ctor_get(v___x_4715_, 0);
lean_inc(v_val_4716_);
lean_dec_ref_known(v___x_4715_, 1);
v___x_4717_ = lean_obj_once(&l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__1, &l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__1_once, _init_l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__1);
v___x_4718_ = l_Lean_MessageData_ofSyntax(v_val_4687_);
v___x_4719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4719_, 0, v___x_4717_);
lean_ctor_set(v___x_4719_, 1, v___x_4718_);
v___x_4720_ = lean_obj_once(&l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__3, &l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__3_once, _init_l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___closed__3);
v___x_4721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4721_, 0, v___x_4719_);
lean_ctor_set(v___x_4721_, 1, v___x_4720_);
v___x_4722_ = l_Lean_MessageData_ofExpr(v_val_4716_);
v___x_4723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4723_, 0, v___x_4721_);
lean_ctor_set(v___x_4723_, 1, v___x_4722_);
v___x_4724_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_initFn_00___x40_Lean_Linter_MissingDocs_573930092____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___closed__1);
v___x_4725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4725_, 0, v___x_4723_);
lean_ctor_set(v___x_4725_, 1, v___x_4724_);
v___x_4726_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_getDocStringText___at___00__private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_isEmptyDocString_spec__0_spec__0_spec__1___redArg(v___x_4725_, v___y_4688_, v___y_4689_);
return v___x_4726_;
}
else
{
lean_object* v___x_4727_; 
lean_dec(v___x_4715_);
lean_dec(v_val_4687_);
v___x_4727_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg(v_optionName_4705_, v___y_4688_, v___y_4689_);
return v___x_4727_;
}
}
}
}
else
{
lean_object* v_a_4758_; lean_object* v___x_4760_; uint8_t v_isShared_4761_; uint8_t v_isSharedCheck_4771_; 
lean_dec(v_optionName_4705_);
lean_dec(v_val_4687_);
lean_dec(v_id_4686_);
v_a_4758_ = lean_ctor_get(v___x_4706_, 0);
v_isSharedCheck_4771_ = !lean_is_exclusive(v___x_4706_);
if (v_isSharedCheck_4771_ == 0)
{
v___x_4760_ = v___x_4706_;
v_isShared_4761_ = v_isSharedCheck_4771_;
goto v_resetjp_4759_;
}
else
{
lean_inc(v_a_4758_);
lean_dec(v___x_4706_);
v___x_4760_ = lean_box(0);
v_isShared_4761_ = v_isSharedCheck_4771_;
goto v_resetjp_4759_;
}
v_resetjp_4759_:
{
lean_object* v___x_4762_; lean_object* v___x_4764_; 
v___x_4762_ = lean_io_error_to_string(v_a_4758_);
if (v_isShared_4703_ == 0)
{
lean_ctor_set_tag(v___x_4702_, 3);
lean_ctor_set(v___x_4702_, 0, v___x_4762_);
v___x_4764_ = v___x_4702_;
goto v_reusejp_4763_;
}
else
{
lean_object* v_reuseFailAlloc_4770_; 
v_reuseFailAlloc_4770_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4770_, 0, v___x_4762_);
v___x_4764_ = v_reuseFailAlloc_4770_;
goto v_reusejp_4763_;
}
v_reusejp_4763_:
{
lean_object* v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4768_; 
v___x_4765_ = l_Lean_MessageData_ofFormat(v___x_4764_);
v___x_4766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4766_, 0, v_a_4692_);
lean_ctor_set(v___x_4766_, 1, v___x_4765_);
if (v_isShared_4761_ == 0)
{
lean_ctor_set(v___x_4760_, 0, v___x_4766_);
v___x_4768_ = v___x_4760_;
goto v_reusejp_4767_;
}
else
{
lean_object* v_reuseFailAlloc_4769_; 
v_reuseFailAlloc_4769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4769_, 0, v___x_4766_);
v___x_4768_ = v_reuseFailAlloc_4769_;
goto v_reusejp_4767_;
}
v_reusejp_4767_:
{
return v___x_4768_;
}
}
}
}
}
}
else
{
lean_object* v_a_4774_; lean_object* v___x_4776_; uint8_t v_isShared_4777_; uint8_t v_isSharedCheck_4781_; 
lean_dec(v_val_4687_);
lean_dec(v_id_4686_);
v_a_4774_ = lean_ctor_get(v___x_4691_, 0);
v_isSharedCheck_4781_ = !lean_is_exclusive(v___x_4691_);
if (v_isSharedCheck_4781_ == 0)
{
v___x_4776_ = v___x_4691_;
v_isShared_4777_ = v_isSharedCheck_4781_;
goto v_resetjp_4775_;
}
else
{
lean_inc(v_a_4774_);
lean_dec(v___x_4691_);
v___x_4776_ = lean_box(0);
v_isShared_4777_ = v_isSharedCheck_4781_;
goto v_resetjp_4775_;
}
v_resetjp_4775_:
{
lean_object* v___x_4779_; 
if (v_isShared_4777_ == 0)
{
v___x_4779_ = v___x_4776_;
goto v_reusejp_4778_;
}
else
{
lean_object* v_reuseFailAlloc_4780_; 
v_reuseFailAlloc_4780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4780_, 0, v_a_4774_);
v___x_4779_ = v_reuseFailAlloc_4780_;
goto v_reusejp_4778_;
}
v_reusejp_4778_:
{
return v___x_4779_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0___boxed(lean_object* v_id_4782_, lean_object* v_val_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_){
_start:
{
lean_object* v_res_4787_; 
v_res_4787_ = l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0(v_id_4782_, v_val_4783_, v___y_4784_, v___y_4785_);
lean_dec(v___y_4785_);
lean_dec_ref(v___y_4784_);
return v_res_4787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg___lam__0(lean_object* v___x_4788_, lean_object* v___x_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_){
_start:
{
lean_object* v___x_4793_; 
v___x_4793_ = l_Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0(v___x_4788_, v___x_4789_, v___y_4790_, v___y_4791_);
if (lean_obj_tag(v___x_4793_) == 0)
{
lean_object* v_a_4794_; lean_object* v___x_4796_; uint8_t v_isShared_4797_; uint8_t v_isSharedCheck_4802_; 
v_a_4794_ = lean_ctor_get(v___x_4793_, 0);
v_isSharedCheck_4802_ = !lean_is_exclusive(v___x_4793_);
if (v_isSharedCheck_4802_ == 0)
{
v___x_4796_ = v___x_4793_;
v_isShared_4797_ = v_isSharedCheck_4802_;
goto v_resetjp_4795_;
}
else
{
lean_inc(v_a_4794_);
lean_dec(v___x_4793_);
v___x_4796_ = lean_box(0);
v_isShared_4797_ = v_isSharedCheck_4802_;
goto v_resetjp_4795_;
}
v_resetjp_4795_:
{
lean_object* v_fst_4798_; lean_object* v___x_4800_; 
v_fst_4798_ = lean_ctor_get(v_a_4794_, 0);
lean_inc(v_fst_4798_);
lean_dec(v_a_4794_);
if (v_isShared_4797_ == 0)
{
lean_ctor_set(v___x_4796_, 0, v_fst_4798_);
v___x_4800_ = v___x_4796_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v_fst_4798_);
v___x_4800_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
return v___x_4800_;
}
}
}
else
{
lean_object* v_a_4803_; lean_object* v___x_4805_; uint8_t v_isShared_4806_; uint8_t v_isSharedCheck_4819_; 
v_a_4803_ = lean_ctor_get(v___x_4793_, 0);
v_isSharedCheck_4819_ = !lean_is_exclusive(v___x_4793_);
if (v_isSharedCheck_4819_ == 0)
{
v___x_4805_ = v___x_4793_;
v_isShared_4806_ = v_isSharedCheck_4819_;
goto v_resetjp_4804_;
}
else
{
lean_inc(v_a_4803_);
lean_dec(v___x_4793_);
v___x_4805_ = lean_box(0);
v_isShared_4806_ = v_isSharedCheck_4819_;
goto v_resetjp_4804_;
}
v_resetjp_4804_:
{
uint8_t v___x_4807_; 
v___x_4807_ = l_Lean_Exception_isInterrupt(v_a_4803_);
if (v___x_4807_ == 0)
{
lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v_scopes_4810_; lean_object* v___x_4811_; lean_object* v_opts_4812_; lean_object* v___x_4814_; 
lean_dec(v_a_4803_);
v___x_4808_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_4809_ = lean_st_ref_get(v___y_4791_);
v_scopes_4810_ = lean_ctor_get(v___x_4809_, 2);
lean_inc(v_scopes_4810_);
lean_dec(v___x_4809_);
v___x_4811_ = l_List_head_x21___redArg(v___x_4808_, v_scopes_4810_);
lean_dec(v_scopes_4810_);
v_opts_4812_ = lean_ctor_get(v___x_4811_, 1);
lean_inc_ref(v_opts_4812_);
lean_dec(v___x_4811_);
if (v_isShared_4806_ == 0)
{
lean_ctor_set_tag(v___x_4805_, 0);
lean_ctor_set(v___x_4805_, 0, v_opts_4812_);
v___x_4814_ = v___x_4805_;
goto v_reusejp_4813_;
}
else
{
lean_object* v_reuseFailAlloc_4815_; 
v_reuseFailAlloc_4815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4815_, 0, v_opts_4812_);
v___x_4814_ = v_reuseFailAlloc_4815_;
goto v_reusejp_4813_;
}
v_reusejp_4813_:
{
return v___x_4814_;
}
}
else
{
lean_object* v___x_4817_; 
if (v_isShared_4806_ == 0)
{
v___x_4817_ = v___x_4805_;
goto v_reusejp_4816_;
}
else
{
lean_object* v_reuseFailAlloc_4818_; 
v_reuseFailAlloc_4818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4818_, 0, v_a_4803_);
v___x_4817_ = v_reuseFailAlloc_4818_;
goto v_reusejp_4816_;
}
v_reusejp_4816_:
{
return v___x_4817_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg___lam__0___boxed(lean_object* v___x_4820_, lean_object* v___x_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_){
_start:
{
lean_object* v_res_4825_; 
v_res_4825_ = l_Lean_Linter_MissingDocs_handleIn___redArg___lam__0(v___x_4820_, v___x_4821_, v___y_4822_, v___y_4823_);
lean_dec(v___y_4823_);
lean_dec_ref(v___y_4822_);
return v_res_4825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg___lam__1(lean_object* v_a_4826_, lean_object* v_x_4827_){
_start:
{
lean_object* v_header_4828_; lean_object* v_currNamespace_4829_; lean_object* v_openDecls_4830_; lean_object* v_levelNames_4831_; lean_object* v_varDecls_4832_; lean_object* v_varUIds_4833_; lean_object* v_includedVars_4834_; lean_object* v_omittedVars_4835_; uint8_t v_isNoncomputable_4836_; uint8_t v_isPublic_4837_; uint8_t v_isMeta_4838_; lean_object* v_attrs_4839_; lean_object* v___x_4841_; uint8_t v_isShared_4842_; uint8_t v_isSharedCheck_4846_; 
v_header_4828_ = lean_ctor_get(v_x_4827_, 0);
v_currNamespace_4829_ = lean_ctor_get(v_x_4827_, 2);
v_openDecls_4830_ = lean_ctor_get(v_x_4827_, 3);
v_levelNames_4831_ = lean_ctor_get(v_x_4827_, 4);
v_varDecls_4832_ = lean_ctor_get(v_x_4827_, 5);
v_varUIds_4833_ = lean_ctor_get(v_x_4827_, 6);
v_includedVars_4834_ = lean_ctor_get(v_x_4827_, 7);
v_omittedVars_4835_ = lean_ctor_get(v_x_4827_, 8);
v_isNoncomputable_4836_ = lean_ctor_get_uint8(v_x_4827_, sizeof(void*)*10);
v_isPublic_4837_ = lean_ctor_get_uint8(v_x_4827_, sizeof(void*)*10 + 1);
v_isMeta_4838_ = lean_ctor_get_uint8(v_x_4827_, sizeof(void*)*10 + 2);
v_attrs_4839_ = lean_ctor_get(v_x_4827_, 9);
v_isSharedCheck_4846_ = !lean_is_exclusive(v_x_4827_);
if (v_isSharedCheck_4846_ == 0)
{
lean_object* v_unused_4847_; 
v_unused_4847_ = lean_ctor_get(v_x_4827_, 1);
lean_dec(v_unused_4847_);
v___x_4841_ = v_x_4827_;
v_isShared_4842_ = v_isSharedCheck_4846_;
goto v_resetjp_4840_;
}
else
{
lean_inc(v_attrs_4839_);
lean_inc(v_omittedVars_4835_);
lean_inc(v_includedVars_4834_);
lean_inc(v_varUIds_4833_);
lean_inc(v_varDecls_4832_);
lean_inc(v_levelNames_4831_);
lean_inc(v_openDecls_4830_);
lean_inc(v_currNamespace_4829_);
lean_inc(v_header_4828_);
lean_dec(v_x_4827_);
v___x_4841_ = lean_box(0);
v_isShared_4842_ = v_isSharedCheck_4846_;
goto v_resetjp_4840_;
}
v_resetjp_4840_:
{
lean_object* v___x_4844_; 
if (v_isShared_4842_ == 0)
{
lean_ctor_set(v___x_4841_, 1, v_a_4826_);
v___x_4844_ = v___x_4841_;
goto v_reusejp_4843_;
}
else
{
lean_object* v_reuseFailAlloc_4845_; 
v_reuseFailAlloc_4845_ = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(v_reuseFailAlloc_4845_, 0, v_header_4828_);
lean_ctor_set(v_reuseFailAlloc_4845_, 1, v_a_4826_);
lean_ctor_set(v_reuseFailAlloc_4845_, 2, v_currNamespace_4829_);
lean_ctor_set(v_reuseFailAlloc_4845_, 3, v_openDecls_4830_);
lean_ctor_set(v_reuseFailAlloc_4845_, 4, v_levelNames_4831_);
lean_ctor_set(v_reuseFailAlloc_4845_, 5, v_varDecls_4832_);
lean_ctor_set(v_reuseFailAlloc_4845_, 6, v_varUIds_4833_);
lean_ctor_set(v_reuseFailAlloc_4845_, 7, v_includedVars_4834_);
lean_ctor_set(v_reuseFailAlloc_4845_, 8, v_omittedVars_4835_);
lean_ctor_set(v_reuseFailAlloc_4845_, 9, v_attrs_4839_);
lean_ctor_set_uint8(v_reuseFailAlloc_4845_, sizeof(void*)*10, v_isNoncomputable_4836_);
lean_ctor_set_uint8(v_reuseFailAlloc_4845_, sizeof(void*)*10 + 1, v_isPublic_4837_);
lean_ctor_set_uint8(v_reuseFailAlloc_4845_, sizeof(void*)*10 + 2, v_isMeta_4838_);
v___x_4844_ = v_reuseFailAlloc_4845_;
goto v_reusejp_4843_;
}
v_reusejp_4843_:
{
return v___x_4844_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___redArg(uint8_t v_flag_4848_, lean_object* v___y_4849_){
_start:
{
lean_object* v___x_4851_; lean_object* v_infoState_4852_; lean_object* v_env_4853_; lean_object* v_messages_4854_; lean_object* v_scopes_4855_; lean_object* v_usedQuotCtxts_4856_; lean_object* v_nextMacroScope_4857_; lean_object* v_maxRecDepth_4858_; lean_object* v_ngen_4859_; lean_object* v_auxDeclNGen_4860_; lean_object* v_traceState_4861_; lean_object* v_snapshotTasks_4862_; lean_object* v_prevLinterStates_4863_; lean_object* v_codeQualityEntryTasks_4864_; lean_object* v___x_4866_; uint8_t v_isShared_4867_; uint8_t v_isSharedCheck_4884_; 
v___x_4851_ = lean_st_ref_take(v___y_4849_);
v_infoState_4852_ = lean_ctor_get(v___x_4851_, 8);
v_env_4853_ = lean_ctor_get(v___x_4851_, 0);
v_messages_4854_ = lean_ctor_get(v___x_4851_, 1);
v_scopes_4855_ = lean_ctor_get(v___x_4851_, 2);
v_usedQuotCtxts_4856_ = lean_ctor_get(v___x_4851_, 3);
v_nextMacroScope_4857_ = lean_ctor_get(v___x_4851_, 4);
v_maxRecDepth_4858_ = lean_ctor_get(v___x_4851_, 5);
v_ngen_4859_ = lean_ctor_get(v___x_4851_, 6);
v_auxDeclNGen_4860_ = lean_ctor_get(v___x_4851_, 7);
v_traceState_4861_ = lean_ctor_get(v___x_4851_, 9);
v_snapshotTasks_4862_ = lean_ctor_get(v___x_4851_, 10);
v_prevLinterStates_4863_ = lean_ctor_get(v___x_4851_, 11);
v_codeQualityEntryTasks_4864_ = lean_ctor_get(v___x_4851_, 12);
v_isSharedCheck_4884_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_4884_ == 0)
{
v___x_4866_ = v___x_4851_;
v_isShared_4867_ = v_isSharedCheck_4884_;
goto v_resetjp_4865_;
}
else
{
lean_inc(v_codeQualityEntryTasks_4864_);
lean_inc(v_prevLinterStates_4863_);
lean_inc(v_snapshotTasks_4862_);
lean_inc(v_traceState_4861_);
lean_inc(v_infoState_4852_);
lean_inc(v_auxDeclNGen_4860_);
lean_inc(v_ngen_4859_);
lean_inc(v_maxRecDepth_4858_);
lean_inc(v_nextMacroScope_4857_);
lean_inc(v_usedQuotCtxts_4856_);
lean_inc(v_scopes_4855_);
lean_inc(v_messages_4854_);
lean_inc(v_env_4853_);
lean_dec(v___x_4851_);
v___x_4866_ = lean_box(0);
v_isShared_4867_ = v_isSharedCheck_4884_;
goto v_resetjp_4865_;
}
v_resetjp_4865_:
{
lean_object* v_assignment_4868_; lean_object* v_lazyAssignment_4869_; lean_object* v_trees_4870_; lean_object* v___x_4872_; uint8_t v_isShared_4873_; uint8_t v_isSharedCheck_4883_; 
v_assignment_4868_ = lean_ctor_get(v_infoState_4852_, 0);
v_lazyAssignment_4869_ = lean_ctor_get(v_infoState_4852_, 1);
v_trees_4870_ = lean_ctor_get(v_infoState_4852_, 2);
v_isSharedCheck_4883_ = !lean_is_exclusive(v_infoState_4852_);
if (v_isSharedCheck_4883_ == 0)
{
v___x_4872_ = v_infoState_4852_;
v_isShared_4873_ = v_isSharedCheck_4883_;
goto v_resetjp_4871_;
}
else
{
lean_inc(v_trees_4870_);
lean_inc(v_lazyAssignment_4869_);
lean_inc(v_assignment_4868_);
lean_dec(v_infoState_4852_);
v___x_4872_ = lean_box(0);
v_isShared_4873_ = v_isSharedCheck_4883_;
goto v_resetjp_4871_;
}
v_resetjp_4871_:
{
lean_object* v___x_4874_; lean_object* v___x_4876_; 
v___x_4874_ = lean_box(0);
if (v_isShared_4873_ == 0)
{
v___x_4876_ = v___x_4872_;
goto v_reusejp_4875_;
}
else
{
lean_object* v_reuseFailAlloc_4882_; 
v_reuseFailAlloc_4882_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_4882_, 0, v_assignment_4868_);
lean_ctor_set(v_reuseFailAlloc_4882_, 1, v_lazyAssignment_4869_);
lean_ctor_set(v_reuseFailAlloc_4882_, 2, v_trees_4870_);
v___x_4876_ = v_reuseFailAlloc_4882_;
goto v_reusejp_4875_;
}
v_reusejp_4875_:
{
lean_object* v___x_4878_; 
lean_ctor_set_uint8(v___x_4876_, sizeof(void*)*3, v_flag_4848_);
if (v_isShared_4867_ == 0)
{
lean_ctor_set(v___x_4866_, 8, v___x_4876_);
v___x_4878_ = v___x_4866_;
goto v_reusejp_4877_;
}
else
{
lean_object* v_reuseFailAlloc_4881_; 
v_reuseFailAlloc_4881_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_4881_, 0, v_env_4853_);
lean_ctor_set(v_reuseFailAlloc_4881_, 1, v_messages_4854_);
lean_ctor_set(v_reuseFailAlloc_4881_, 2, v_scopes_4855_);
lean_ctor_set(v_reuseFailAlloc_4881_, 3, v_usedQuotCtxts_4856_);
lean_ctor_set(v_reuseFailAlloc_4881_, 4, v_nextMacroScope_4857_);
lean_ctor_set(v_reuseFailAlloc_4881_, 5, v_maxRecDepth_4858_);
lean_ctor_set(v_reuseFailAlloc_4881_, 6, v_ngen_4859_);
lean_ctor_set(v_reuseFailAlloc_4881_, 7, v_auxDeclNGen_4860_);
lean_ctor_set(v_reuseFailAlloc_4881_, 8, v___x_4876_);
lean_ctor_set(v_reuseFailAlloc_4881_, 9, v_traceState_4861_);
lean_ctor_set(v_reuseFailAlloc_4881_, 10, v_snapshotTasks_4862_);
lean_ctor_set(v_reuseFailAlloc_4881_, 11, v_prevLinterStates_4863_);
lean_ctor_set(v_reuseFailAlloc_4881_, 12, v_codeQualityEntryTasks_4864_);
v___x_4878_ = v_reuseFailAlloc_4881_;
goto v_reusejp_4877_;
}
v_reusejp_4877_:
{
lean_object* v___x_4879_; lean_object* v___x_4880_; 
v___x_4879_ = lean_st_ref_put(v___y_4849_, v___x_4878_);
v___x_4880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4880_, 0, v___x_4874_);
return v___x_4880_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___redArg___boxed(lean_object* v_flag_4885_, lean_object* v___y_4886_, lean_object* v___y_4887_){
_start:
{
uint8_t v_flag_boxed_4888_; lean_object* v_res_4889_; 
v_flag_boxed_4888_ = lean_unbox(v_flag_4885_);
v_res_4889_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___redArg(v_flag_boxed_4888_, v___y_4886_);
lean_dec(v___y_4886_);
return v_res_4889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1___redArg(uint8_t v_flag_4890_, lean_object* v_x_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_){
_start:
{
lean_object* v___x_4895_; lean_object* v_infoState_4896_; uint8_t v_enabled_4897_; lean_object* v_a_4899_; lean_object* v___x_4909_; lean_object* v___x_4910_; 
v___x_4895_ = lean_st_ref_get(v___y_4893_);
v_infoState_4896_ = lean_ctor_get(v___x_4895_, 8);
lean_inc_ref(v_infoState_4896_);
lean_dec(v___x_4895_);
v_enabled_4897_ = lean_ctor_get_uint8(v_infoState_4896_, sizeof(void*)*3);
lean_dec_ref(v_infoState_4896_);
v___x_4909_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___redArg(v_flag_4890_, v___y_4893_);
lean_dec_ref(v___x_4909_);
lean_inc(v___y_4893_);
lean_inc_ref(v___y_4892_);
v___x_4910_ = lean_apply_3(v_x_4891_, v___y_4892_, v___y_4893_, lean_box(0));
if (lean_obj_tag(v___x_4910_) == 0)
{
lean_object* v_a_4911_; lean_object* v___x_4912_; lean_object* v___x_4914_; uint8_t v_isShared_4915_; uint8_t v_isSharedCheck_4919_; 
v_a_4911_ = lean_ctor_get(v___x_4910_, 0);
lean_inc(v_a_4911_);
lean_dec_ref_known(v___x_4910_, 1);
v___x_4912_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___redArg(v_enabled_4897_, v___y_4893_);
v_isSharedCheck_4919_ = !lean_is_exclusive(v___x_4912_);
if (v_isSharedCheck_4919_ == 0)
{
lean_object* v_unused_4920_; 
v_unused_4920_ = lean_ctor_get(v___x_4912_, 0);
lean_dec(v_unused_4920_);
v___x_4914_ = v___x_4912_;
v_isShared_4915_ = v_isSharedCheck_4919_;
goto v_resetjp_4913_;
}
else
{
lean_dec(v___x_4912_);
v___x_4914_ = lean_box(0);
v_isShared_4915_ = v_isSharedCheck_4919_;
goto v_resetjp_4913_;
}
v_resetjp_4913_:
{
lean_object* v___x_4917_; 
if (v_isShared_4915_ == 0)
{
lean_ctor_set(v___x_4914_, 0, v_a_4911_);
v___x_4917_ = v___x_4914_;
goto v_reusejp_4916_;
}
else
{
lean_object* v_reuseFailAlloc_4918_; 
v_reuseFailAlloc_4918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4918_, 0, v_a_4911_);
v___x_4917_ = v_reuseFailAlloc_4918_;
goto v_reusejp_4916_;
}
v_reusejp_4916_:
{
return v___x_4917_;
}
}
}
else
{
lean_object* v_a_4921_; 
v_a_4921_ = lean_ctor_get(v___x_4910_, 0);
lean_inc(v_a_4921_);
lean_dec_ref_known(v___x_4910_, 1);
v_a_4899_ = v_a_4921_;
goto v___jp_4898_;
}
v___jp_4898_:
{
lean_object* v___x_4900_; lean_object* v___x_4902_; uint8_t v_isShared_4903_; uint8_t v_isSharedCheck_4907_; 
v___x_4900_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___redArg(v_enabled_4897_, v___y_4893_);
v_isSharedCheck_4907_ = !lean_is_exclusive(v___x_4900_);
if (v_isSharedCheck_4907_ == 0)
{
lean_object* v_unused_4908_; 
v_unused_4908_ = lean_ctor_get(v___x_4900_, 0);
lean_dec(v_unused_4908_);
v___x_4902_ = v___x_4900_;
v_isShared_4903_ = v_isSharedCheck_4907_;
goto v_resetjp_4901_;
}
else
{
lean_dec(v___x_4900_);
v___x_4902_ = lean_box(0);
v_isShared_4903_ = v_isSharedCheck_4907_;
goto v_resetjp_4901_;
}
v_resetjp_4901_:
{
lean_object* v___x_4905_; 
if (v_isShared_4903_ == 0)
{
lean_ctor_set_tag(v___x_4902_, 1);
lean_ctor_set(v___x_4902_, 0, v_a_4899_);
v___x_4905_ = v___x_4902_;
goto v_reusejp_4904_;
}
else
{
lean_object* v_reuseFailAlloc_4906_; 
v_reuseFailAlloc_4906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4906_, 0, v_a_4899_);
v___x_4905_ = v_reuseFailAlloc_4906_;
goto v_reusejp_4904_;
}
v_reusejp_4904_:
{
return v___x_4905_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1___redArg___boxed(lean_object* v_flag_4922_, lean_object* v_x_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_, lean_object* v___y_4926_){
_start:
{
uint8_t v_flag_boxed_4927_; lean_object* v_res_4928_; 
v_flag_boxed_4927_ = lean_unbox(v_flag_4922_);
v_res_4928_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1___redArg(v_flag_boxed_4927_, v_x_4923_, v___y_4924_, v___y_4925_);
lean_dec(v___y_4925_);
lean_dec_ref(v___y_4924_);
return v_res_4928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg(lean_object* v_stx_4935_, lean_object* v_a_4936_, lean_object* v_a_4937_){
_start:
{
lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; uint8_t v___x_4943_; 
v___x_4939_ = lean_unsigned_to_nat(0u);
v___x_4940_ = l_Lean_Syntax_getArg(v_stx_4935_, v___x_4939_);
lean_inc(v___x_4940_);
v___x_4941_ = l_Lean_Syntax_getKind(v___x_4940_);
v___x_4942_ = ((lean_object*)(l_Lean_Linter_MissingDocs_handleIn___redArg___closed__1));
v___x_4943_ = lean_name_eq(v___x_4941_, v___x_4942_);
lean_dec(v___x_4941_);
if (v___x_4943_ == 0)
{
lean_object* v___x_4944_; lean_object* v_run_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; 
lean_dec(v___x_4940_);
v___x_4944_ = ((lean_object*)(l_Lean_Linter_MissingDocs_missingDocs));
v_run_4945_ = lean_ctor_get(v___x_4944_, 0);
v___x_4946_ = lean_unsigned_to_nat(2u);
v___x_4947_ = l_Lean_Syntax_getArg(v_stx_4935_, v___x_4946_);
lean_inc_ref(v_run_4945_);
lean_inc(v_a_4937_);
lean_inc_ref(v_a_4936_);
v___x_4948_ = lean_apply_4(v_run_4945_, v___x_4947_, v_a_4936_, v_a_4937_, lean_box(0));
return v___x_4948_;
}
else
{
uint8_t v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___f_4954_; lean_object* v___x_4955_; 
v___x_4949_ = 0;
v___x_4950_ = lean_unsigned_to_nat(1u);
v___x_4951_ = l_Lean_Syntax_getArg(v___x_4940_, v___x_4950_);
v___x_4952_ = lean_unsigned_to_nat(3u);
v___x_4953_ = l_Lean_Syntax_getArg(v___x_4940_, v___x_4952_);
lean_dec(v___x_4940_);
v___f_4954_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_handleIn___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_4954_, 0, v___x_4951_);
lean_closure_set(v___f_4954_, 1, v___x_4953_);
v___x_4955_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1___redArg(v___x_4949_, v___f_4954_, v_a_4936_, v_a_4937_);
if (lean_obj_tag(v___x_4955_) == 0)
{
lean_object* v_a_4956_; lean_object* v___x_4957_; lean_object* v_run_4958_; lean_object* v___f_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; 
v_a_4956_ = lean_ctor_get(v___x_4955_, 0);
lean_inc(v_a_4956_);
lean_dec_ref_known(v___x_4955_, 1);
v___x_4957_ = ((lean_object*)(l_Lean_Linter_MissingDocs_missingDocs));
v_run_4958_ = lean_ctor_get(v___x_4957_, 0);
v___f_4959_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_handleIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_4959_, 0, v_a_4956_);
v___x_4960_ = lean_unsigned_to_nat(2u);
v___x_4961_ = l_Lean_Syntax_getArg(v_stx_4935_, v___x_4960_);
lean_inc_ref(v_run_4958_);
v___x_4962_ = lean_apply_1(v_run_4958_, v___x_4961_);
v___x_4963_ = l_Lean_Elab_Command_withScope___redArg(v___f_4959_, v___x_4962_, v_a_4936_, v_a_4937_);
return v___x_4963_;
}
else
{
lean_object* v_a_4964_; lean_object* v___x_4966_; uint8_t v_isShared_4967_; uint8_t v_isSharedCheck_4971_; 
v_a_4964_ = lean_ctor_get(v___x_4955_, 0);
v_isSharedCheck_4971_ = !lean_is_exclusive(v___x_4955_);
if (v_isSharedCheck_4971_ == 0)
{
v___x_4966_ = v___x_4955_;
v_isShared_4967_ = v_isSharedCheck_4971_;
goto v_resetjp_4965_;
}
else
{
lean_inc(v_a_4964_);
lean_dec(v___x_4955_);
v___x_4966_ = lean_box(0);
v_isShared_4967_ = v_isSharedCheck_4971_;
goto v_resetjp_4965_;
}
v_resetjp_4965_:
{
lean_object* v___x_4969_; 
if (v_isShared_4967_ == 0)
{
v___x_4969_ = v___x_4966_;
goto v_reusejp_4968_;
}
else
{
lean_object* v_reuseFailAlloc_4970_; 
v_reuseFailAlloc_4970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4970_, 0, v_a_4964_);
v___x_4969_ = v_reuseFailAlloc_4970_;
goto v_reusejp_4968_;
}
v_reusejp_4968_:
{
return v___x_4969_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___redArg___boxed(lean_object* v_stx_4972_, lean_object* v_a_4973_, lean_object* v_a_4974_, lean_object* v_a_4975_){
_start:
{
lean_object* v_res_4976_; 
v_res_4976_ = l_Lean_Linter_MissingDocs_handleIn___redArg(v_stx_4972_, v_a_4973_, v_a_4974_);
lean_dec(v_a_4974_);
lean_dec_ref(v_a_4973_);
lean_dec(v_stx_4972_);
return v_res_4976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn(uint8_t v_x_4977_, lean_object* v_stx_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_){
_start:
{
lean_object* v___x_4982_; 
v___x_4982_ = l_Lean_Linter_MissingDocs_handleIn___redArg(v_stx_4978_, v_a_4979_, v_a_4980_);
return v___x_4982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleIn___boxed(lean_object* v_x_4983_, lean_object* v_stx_4984_, lean_object* v_a_4985_, lean_object* v_a_4986_, lean_object* v_a_4987_){
_start:
{
uint8_t v_x_4370__boxed_4988_; lean_object* v_res_4989_; 
v_x_4370__boxed_4988_ = lean_unbox(v_x_4983_);
v_res_4989_ = l_Lean_Linter_MissingDocs_handleIn(v_x_4370__boxed_4988_, v_stx_4984_, v_a_4985_, v_a_4986_);
lean_dec(v_a_4986_);
lean_dec_ref(v_a_4985_);
lean_dec(v_stx_4984_);
return v_res_4989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5(uint8_t v_flag_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_){
_start:
{
lean_object* v___x_4994_; 
v___x_4994_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___redArg(v_flag_4990_, v___y_4992_);
return v___x_4994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5___boxed(lean_object* v_flag_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_){
_start:
{
uint8_t v_flag_boxed_4999_; lean_object* v_res_5000_; 
v_flag_boxed_4999_ = lean_unbox(v_flag_4995_);
v_res_5000_ = l_Lean_Elab_enableInfoTree___at___00Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1_spec__5(v_flag_boxed_4999_, v___y_4996_, v___y_4997_);
lean_dec(v___y_4997_);
lean_dec_ref(v___y_4996_);
return v_res_5000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1(lean_object* v_00_u03b1_5001_, uint8_t v_flag_5002_, lean_object* v_x_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_){
_start:
{
lean_object* v___x_5007_; 
v___x_5007_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1___redArg(v_flag_5002_, v_x_5003_, v___y_5004_, v___y_5005_);
return v___x_5007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1___boxed(lean_object* v_00_u03b1_5008_, lean_object* v_flag_5009_, lean_object* v_x_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_, lean_object* v___y_5013_){
_start:
{
uint8_t v_flag_boxed_5014_; lean_object* v_res_5015_; 
v_flag_boxed_5014_ = lean_unbox(v_flag_5009_);
v_res_5015_ = l_Lean_Elab_withEnableInfoTree___at___00Lean_Linter_MissingDocs_handleIn_spec__1(v_00_u03b1_5008_, v_flag_boxed_5014_, v_x_5010_, v___y_5011_, v___y_5012_);
lean_dec(v___y_5012_);
lean_dec_ref(v___y_5011_);
return v_res_5015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2(lean_object* v_t_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_){
_start:
{
lean_object* v___x_5020_; 
v___x_5020_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2___redArg(v_t_5016_, v___y_5018_);
return v___x_5020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2___boxed(lean_object* v_t_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_){
_start:
{
lean_object* v_res_5025_; 
v_res_5025_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__1_spec__2(v_t_5021_, v___y_5022_, v___y_5023_);
lean_dec(v___y_5023_);
lean_dec_ref(v___y_5022_);
return v_res_5025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2(lean_object* v_00_u03b1_5026_, lean_object* v_optionName_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_){
_start:
{
lean_object* v___x_5031_; 
v___x_5031_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___redArg(v_optionName_5027_, v___y_5028_, v___y_5029_);
return v___x_5031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2___boxed(lean_object* v_00_u03b1_5032_, lean_object* v_optionName_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_){
_start:
{
lean_object* v_res_5037_; 
v_res_5037_ = l___private_Lean_Elab_SetOption_0__Lean_Elab_throwUnconfigurable___at___00Lean_Elab_elabSetOption___at___00Lean_Linter_MissingDocs_handleIn_spec__0_spec__2(v_00_u03b1_5032_, v_optionName_5033_, v___y_5034_, v___y_5035_);
lean_dec(v___y_5035_);
lean_dec_ref(v___y_5034_);
return v_res_5037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleIn___regBuiltin_Lean_Linter_MissingDocs_handleIn__1(){
_start:
{
lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; 
v___x_5045_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleIn___regBuiltin_Lean_Linter_MissingDocs_handleIn__1___closed__1));
v___x_5046_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_handleIn___boxed), 5, 0);
v___x_5047_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_5045_, v___x_5046_);
return v___x_5047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleIn___regBuiltin_Lean_Linter_MissingDocs_handleIn__1___boxed(lean_object* v_a_5048_){
_start:
{
lean_object* v_res_5049_; 
v_res_5049_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleIn___regBuiltin_Lean_Linter_MissingDocs_handleIn__1();
return v_res_5049_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_MissingDocs_handleMutual_spec__0(lean_object* v_as_5050_, size_t v_i_5051_, size_t v_stop_5052_, lean_object* v_b_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_){
_start:
{
lean_object* v___x_5057_; lean_object* v_run_5058_; uint8_t v___x_5059_; 
v___x_5057_ = ((lean_object*)(l_Lean_Linter_MissingDocs_missingDocs));
v_run_5058_ = lean_ctor_get(v___x_5057_, 0);
v___x_5059_ = lean_usize_dec_eq(v_i_5051_, v_stop_5052_);
if (v___x_5059_ == 0)
{
lean_object* v___x_5060_; lean_object* v___x_5061_; 
v___x_5060_ = lean_array_uget_borrowed(v_as_5050_, v_i_5051_);
lean_inc_ref(v_run_5058_);
lean_inc(v___y_5055_);
lean_inc_ref(v___y_5054_);
lean_inc(v___x_5060_);
v___x_5061_ = lean_apply_4(v_run_5058_, v___x_5060_, v___y_5054_, v___y_5055_, lean_box(0));
if (lean_obj_tag(v___x_5061_) == 0)
{
lean_object* v_a_5062_; size_t v___x_5063_; size_t v___x_5064_; 
v_a_5062_ = lean_ctor_get(v___x_5061_, 0);
lean_inc(v_a_5062_);
lean_dec_ref_known(v___x_5061_, 1);
v___x_5063_ = ((size_t)1ULL);
v___x_5064_ = lean_usize_add(v_i_5051_, v___x_5063_);
v_i_5051_ = v___x_5064_;
v_b_5053_ = v_a_5062_;
goto _start;
}
else
{
return v___x_5061_;
}
}
else
{
lean_object* v___x_5066_; 
v___x_5066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5066_, 0, v_b_5053_);
return v___x_5066_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_MissingDocs_handleMutual_spec__0___boxed(lean_object* v_as_5067_, lean_object* v_i_5068_, lean_object* v_stop_5069_, lean_object* v_b_5070_, lean_object* v___y_5071_, lean_object* v___y_5072_, lean_object* v___y_5073_){
_start:
{
size_t v_i_boxed_5074_; size_t v_stop_boxed_5075_; lean_object* v_res_5076_; 
v_i_boxed_5074_ = lean_unbox_usize(v_i_5068_);
lean_dec(v_i_5068_);
v_stop_boxed_5075_ = lean_unbox_usize(v_stop_5069_);
lean_dec(v_stop_5069_);
v_res_5076_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_MissingDocs_handleMutual_spec__0(v_as_5067_, v_i_boxed_5074_, v_stop_boxed_5075_, v_b_5070_, v___y_5071_, v___y_5072_);
lean_dec(v___y_5072_);
lean_dec_ref(v___y_5071_);
lean_dec_ref(v_as_5067_);
return v_res_5076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleMutual___redArg(lean_object* v_stx_5077_, lean_object* v_a_5078_, lean_object* v_a_5079_){
_start:
{
lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v___x_5086_; uint8_t v___x_5087_; 
v___x_5081_ = lean_unsigned_to_nat(1u);
v___x_5082_ = l_Lean_Syntax_getArg(v_stx_5077_, v___x_5081_);
v___x_5083_ = l_Lean_Syntax_getArgs(v___x_5082_);
lean_dec(v___x_5082_);
v___x_5084_ = lean_unsigned_to_nat(0u);
v___x_5085_ = lean_array_get_size(v___x_5083_);
v___x_5086_ = lean_box(0);
v___x_5087_ = lean_nat_dec_lt(v___x_5084_, v___x_5085_);
if (v___x_5087_ == 0)
{
lean_object* v___x_5088_; 
lean_dec_ref(v___x_5083_);
v___x_5088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5088_, 0, v___x_5086_);
return v___x_5088_;
}
else
{
uint8_t v___x_5089_; 
v___x_5089_ = lean_nat_dec_le(v___x_5085_, v___x_5085_);
if (v___x_5089_ == 0)
{
if (v___x_5087_ == 0)
{
lean_object* v___x_5090_; 
lean_dec_ref(v___x_5083_);
v___x_5090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5090_, 0, v___x_5086_);
return v___x_5090_;
}
else
{
size_t v___x_5091_; size_t v___x_5092_; lean_object* v___x_5093_; 
v___x_5091_ = ((size_t)0ULL);
v___x_5092_ = lean_usize_of_nat(v___x_5085_);
v___x_5093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_MissingDocs_handleMutual_spec__0(v___x_5083_, v___x_5091_, v___x_5092_, v___x_5086_, v_a_5078_, v_a_5079_);
lean_dec_ref(v___x_5083_);
return v___x_5093_;
}
}
else
{
size_t v___x_5094_; size_t v___x_5095_; lean_object* v___x_5096_; 
v___x_5094_ = ((size_t)0ULL);
v___x_5095_ = lean_usize_of_nat(v___x_5085_);
v___x_5096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_MissingDocs_handleMutual_spec__0(v___x_5083_, v___x_5094_, v___x_5095_, v___x_5086_, v_a_5078_, v_a_5079_);
lean_dec_ref(v___x_5083_);
return v___x_5096_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleMutual___redArg___boxed(lean_object* v_stx_5097_, lean_object* v_a_5098_, lean_object* v_a_5099_, lean_object* v_a_5100_){
_start:
{
lean_object* v_res_5101_; 
v_res_5101_ = l_Lean_Linter_MissingDocs_handleMutual___redArg(v_stx_5097_, v_a_5098_, v_a_5099_);
lean_dec(v_a_5099_);
lean_dec_ref(v_a_5098_);
lean_dec(v_stx_5097_);
return v_res_5101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleMutual(uint8_t v_x_5102_, lean_object* v_stx_5103_, lean_object* v_a_5104_, lean_object* v_a_5105_){
_start:
{
lean_object* v___x_5107_; 
v___x_5107_ = l_Lean_Linter_MissingDocs_handleMutual___redArg(v_stx_5103_, v_a_5104_, v_a_5105_);
return v___x_5107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_MissingDocs_handleMutual___boxed(lean_object* v_x_5108_, lean_object* v_stx_5109_, lean_object* v_a_5110_, lean_object* v_a_5111_, lean_object* v_a_5112_){
_start:
{
uint8_t v_x_402__boxed_5113_; lean_object* v_res_5114_; 
v_x_402__boxed_5113_ = lean_unbox(v_x_5108_);
v_res_5114_ = l_Lean_Linter_MissingDocs_handleMutual(v_x_402__boxed_5113_, v_stx_5109_, v_a_5110_, v_a_5111_);
lean_dec(v_a_5111_);
lean_dec_ref(v_a_5110_);
lean_dec(v_stx_5109_);
return v_res_5114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleMutual___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1(){
_start:
{
lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; 
v___x_5122_ = ((lean_object*)(l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleMutual___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1___closed__1));
v___x_5123_ = lean_alloc_closure((void*)(l_Lean_Linter_MissingDocs_handleMutual___boxed), 5, 0);
v___x_5124_ = l_Lean_Linter_MissingDocs_addBuiltinHandler(v___x_5122_, v___x_5123_);
return v___x_5124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleMutual___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1___boxed(lean_object* v_a_5125_){
_start:
{
lean_object* v_res_5126_; 
v_res_5126_ = l___private_Lean_Linter_MissingDocs_0__Lean_Linter_MissingDocs_handleMutual___regBuiltin_Lean_Linter_MissingDocs_handleMutual__1();
return v_res_5126_;
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
